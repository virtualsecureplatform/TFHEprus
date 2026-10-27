//! Verifier authority created by trusted preparation or imported under an external pin.
use crate::ProofError;
use core::{fmt, str::FromStr};
use p3_batch_stark::common::{CommonData, GlobalPreprocessed, PreprocessedInstanceMeta};
use p3_circuit::{
    ops::{NpoTypeId, Poseidon2Config},
    StatementSchema,
};
use p3_circuit_prover::{
    air::AluExtMulKind,
    batch_stark_prover::{AirVariant, RowCounts},
    config::GoldilocksConfig,
    BuiltinArtifactAir, BuiltinArtifactNpo, CircuitVerifier, ConstraintProfile, TablePacking,
    TrustedBuiltinArtifactRelation,
};
use p3_goldilocks::Goldilocks;
use p3_recursion::prepared::NativeCommitment;
use serde::{Deserialize, Serialize};
use sha3::{Digest, Sha3_256};

const DOMAIN: &[u8] = b"TFHEprus/verifier-key/v1";
const PROTOCOL: &str = "plonky3-recursion/3a69ba61:goldilocks-d2:poseidon2-seed-1";
fn invalid(message: impl Into<String>) -> ProofError {
    ProofError::VerifierKey(message.into())
}
fn mapped(error: impl fmt::Debug) -> ProofError {
    invalid(format!("{error:?}"))
}

/// A trust anchor provisioned independently of the proof and candidate key file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierKeyFingerprint([u8; 32]);
impl fmt::Display for VerifierKeyFingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}
impl FromStr for VerifierKeyFingerprint {
    type Err = ProofError;
    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if value.len() != 64 || !value.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err(invalid(
                "expected a 64-digit hexadecimal verifier-key fingerprint",
            ));
        }
        let mut bytes = [0; 32];
        for (index, byte) in bytes.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).map_err(mapped)?;
        }
        Ok(Self(bytes))
    }
}
fn fingerprint(bytes: &[u8]) -> VerifierKeyFingerprint {
    let mut hash = Sha3_256::new();
    hash.update(DOMAIN);
    hash.update(bytes);
    VerifierKeyFingerprint(hash.finalize().into())
}

#[derive(Clone, Serialize, Deserialize)]
struct NpoArtifact {
    op_type: NpoTypeId,
    rows: usize,
    lanes: usize,
    variant: AirVariant,
    values: Vec<Goldilocks>,
}
#[derive(Clone, Serialize, Deserialize)]
struct CommonArtifact {
    commitment: NativeCommitment<GoldilocksConfig>,
    instances: Vec<Option<(usize, usize, usize)>>,
    matrix_to_instance: Vec<usize>,
}
#[derive(Clone, Serialize, Deserialize)]
struct KeyArtifact {
    version: u32,
    protocol: String,
    fri: [usize; 7],
    cap_height: usize,
    packing: TablePacking,
    rows: RowCounts,
    w: Goldilocks,
    variant: AirVariant,
    npos: Vec<NpoArtifact>,
    schema: StatementSchema,
    statement_index: Option<usize>,
    degrees: Vec<usize>,
    common: CommonArtifact,
}
fn fri_parameters() -> [usize; 7] {
    [
        crate::PROOF_FRI_LOG_BLOWUP,
        crate::PROOF_FRI_LOG_FINAL_POLY_LEN,
        crate::PROOF_FRI_MAX_LOG_ARITY,
        crate::PROOF_FRI_NUM_QUERIES,
        crate::PROOF_FRI_COMMIT_POW_BITS,
        crate::PROOF_FRI_QUERY_POW_BITS,
        0,
    ]
}

/// A verifier key whose authority comes from local trusted circuit preparation or
/// from an exact fingerprint checked before decoding. It cannot be deserialized directly.
#[derive(Clone)]
pub struct VerifierKey {
    bytes: std::sync::Arc<[u8]>,
    verifier: CircuitVerifier<GoldilocksConfig>,
}
impl VerifierKey {
    pub(crate) fn from_prepared(
        verifier: CircuitVerifier<GoldilocksConfig>,
    ) -> Result<Self, ProofError> {
        let relation = verifier.relation();
        let w = match relation.reduction() {
            AluExtMulKind::Binomial { w } if relation.ext_degree() == 2 => w,
            _ => return Err(invalid("only Goldilocks D2 recursive keys are supported")),
        };
        let common = verifier
            .common_data()
            .preprocessed
            .as_ref()
            .ok_or_else(|| invalid("missing trusted preprocessing"))?;
        let artifact = KeyArtifact {
            version: 1,
            protocol: PROTOCOL.into(),
            fri: fri_parameters(),
            cap_height: crate::MERKLE_CAP_HEIGHT,
            packing: relation.table_packing().clone(),
            rows: *relation.rows(),
            w,
            variant: relation.alu_variant(),
            npos: relation
                .non_primitives()
                .iter()
                .map(|n| NpoArtifact {
                    op_type: n.op_type().clone(),
                    rows: n.rows(),
                    lanes: n.lanes(),
                    variant: n.air_variant(),
                    values: n.public_values().to_vec(),
                })
                .collect(),
            schema: relation.statement_layout().schema().clone(),
            statement_index: relation.statement_layout().table_instance(),
            degrees: relation.trace_degree_bits().to_vec(),
            common: CommonArtifact {
                commitment: common.commitment.clone(),
                instances: common
                    .instances
                    .iter()
                    .map(|m| m.as_ref().map(|m| (m.matrix_index, m.width, m.degree_bits)))
                    .collect(),
                matrix_to_instance: common.matrix_to_instance.clone(),
            },
        };
        let bytes = postcard::to_allocvec(&artifact).map_err(mapped)?;
        Ok(Self {
            bytes: bytes.into(),
            verifier,
        })
    }
    /// Authenticate exact candidate bytes against an independently obtained pin.
    /// Never obtain `expected` by hashing the candidate key supplied with an untrusted proof.
    pub fn from_authenticated_bytes(
        bytes: &[u8],
        expected: &VerifierKeyFingerprint,
    ) -> Result<Self, ProofError> {
        if fingerprint(bytes) != *expected {
            return Err(invalid("fingerprint mismatch"));
        }
        let (artifact, rest): (KeyArtifact, _) =
            postcard::take_from_bytes(bytes).map_err(mapped)?;
        if !rest.is_empty() {
            return Err(invalid("trailing verifier-key bytes"));
        }
        if artifact.version != 1
            || artifact.protocol != PROTOCOL
            || artifact.fri != fri_parameters()
            || artifact.cap_height != crate::MERKLE_CAP_HEIGHT
        {
            return Err(invalid("unsupported verifier-key protocol or parameters"));
        }
        let npos = artifact
            .npos
            .iter()
            .map(|n| {
                if n.op_type == NpoTypeId::statement() {
                    return Ok(BuiltinArtifactNpo::statement(artifact.schema.base_len()));
                }
                let air = if n.op_type == NpoTypeId::recompose() {
                    BuiltinArtifactAir::Recompose
                } else if n.op_type == NpoTypeId::recompose_with_coeff_lookups() {
                    BuiltinArtifactAir::RecomposeWithCoefficientLookups
                } else if n.op_type == NpoTypeId::poseidon2_perm(Poseidon2Config::GOLDILOCKS_D2_W8)
                {
                    BuiltinArtifactAir::Poseidon2(Poseidon2Config::GOLDILOCKS_D2_W8)
                } else if n.op_type
                    == NpoTypeId::poseidon2_perm(Poseidon2Config::GOLDILOCKS_D2_W8.for_challenger())
                {
                    BuiltinArtifactAir::Poseidon2(
                        Poseidon2Config::GOLDILOCKS_D2_W8.for_challenger(),
                    )
                } else {
                    return Err(invalid("unsupported recursive NPO in verifier key"));
                };
                Ok(BuiltinArtifactNpo::static_values(
                    air,
                    n.rows,
                    n.lanes,
                    n.variant,
                    n.values.clone(),
                ))
            })
            .collect::<Result<Vec<_>, ProofError>>()?;
        let parts = TrustedBuiltinArtifactRelation::try_new(
            artifact.packing,
            artifact.rows,
            2,
            AluExtMulKind::Binomial { w: artifact.w },
            artifact.variant,
            ConstraintProfile::Standard,
            npos,
            artifact.schema,
            artifact.statement_index,
            None,
            artifact.degrees,
        )
        .map_err(mapped)?;
        let common = CommonData::new(
            Some(GlobalPreprocessed {
                commitment: artifact.common.commitment,
                instances: artifact
                    .common
                    .instances
                    .into_iter()
                    .map(|m| {
                        m.map(
                            |(matrix_index, width, degree_bits)| PreprocessedInstanceMeta {
                                matrix_index,
                                width,
                                degree_bits,
                            },
                        )
                    })
                    .collect(),
                matrix_to_instance: artifact.common.matrix_to_instance,
            }),
            Vec::new(),
        );
        let verifier = CircuitVerifier::from_independently_trusted_builtin_artifact(
            crate::goldilocks_config(),
            parts,
            common,
        )
        .map_err(mapped)?;
        Ok(Self {
            bytes: bytes.to_vec().into(),
            verifier,
        })
    }
    pub fn fingerprint(&self) -> VerifierKeyFingerprint {
        fingerprint(&self.bytes)
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        self.bytes.to_vec()
    }
    pub(crate) fn verify(
        &self,
        proof: &p3_circuit_prover::BatchStarkProof<GoldilocksConfig>,
        statement: &[Goldilocks],
    ) -> Result<(), ProofError> {
        self.verifier.verify(proof, statement).map_err(mapped)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fingerprints_require_exact_hex_width() {
        for invalid in [
            "",
            "00",
            "zz",
            &"0".repeat(63),
            &"0".repeat(65),
            &"é".repeat(32),
        ] {
            assert!(invalid.parse::<VerifierKeyFingerprint>().is_err());
        }
        let upper = "AB".repeat(32).parse::<VerifierKeyFingerprint>().unwrap();
        assert_eq!(upper.to_string(), "ab".repeat(32));
    }
    #[test]
    fn candidate_is_authenticated_before_decoding() {
        let pin = "00".repeat(32).parse().unwrap();
        let error = VerifierKey::from_authenticated_bytes(b"malformed candidate", &pin)
            .err()
            .unwrap();
        assert!(error.to_string().contains("fingerprint mismatch"));
    }
}
