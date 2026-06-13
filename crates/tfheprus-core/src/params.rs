use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Params {
    pub lwe_dimension: usize,
    pub polynomial_size: usize,
    pub glwe_dimension: usize,
    pub decomposition_base_log: usize,
    pub decomposition_level_count: usize,
    pub plaintext_modulus: u64,
    #[serde(default = "EncryptionNoise::legacy_default")]
    pub encryption_noise: EncryptionNoise,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EncryptionNoise {
    CenteredBinomial { terms: usize },
    DiscreteGaussianStddev { stddev: u64 },
}

impl Params {
    pub fn new(
        lwe_dimension: usize,
        polynomial_size: usize,
        glwe_dimension: usize,
        decomposition_base_log: usize,
        decomposition_level_count: usize,
        plaintext_modulus: u64,
    ) -> Self {
        Self::new_with_noise(
            lwe_dimension,
            polynomial_size,
            glwe_dimension,
            decomposition_base_log,
            decomposition_level_count,
            plaintext_modulus,
            EncryptionNoise::legacy_default(),
        )
    }

    pub fn new_with_noise(
        lwe_dimension: usize,
        polynomial_size: usize,
        glwe_dimension: usize,
        decomposition_base_log: usize,
        decomposition_level_count: usize,
        plaintext_modulus: u64,
        encryption_noise: EncryptionNoise,
    ) -> Self {
        assert!(lwe_dimension > 0);
        assert!(polynomial_size.is_power_of_two());
        assert!(glwe_dimension > 0);
        assert!((1..=32).contains(&decomposition_base_log));
        assert!(decomposition_level_count > 0);
        assert!(decomposition_base_log * decomposition_level_count <= 64);
        assert!(plaintext_modulus > 1);
        encryption_noise.validate();
        Self {
            lwe_dimension,
            polynomial_size,
            glwe_dimension,
            decomposition_base_log,
            decomposition_level_count,
            plaintext_modulus,
            encryption_noise,
        }
    }

    /// Small exact-decomposition parameters used by fast correctness tests.
    pub fn toy() -> Self {
        Self::new(8, 8, 1, 16, 4, 4)
    }

    /// Medium-sized exact-decomposition parameters for native PBS profiling.
    ///
    /// This is still not a secure TFHE parameter set. It keeps the same exact
    /// Goldilocks gadget decomposition as `toy()` but increases both the LWE
    /// dimension and polynomial size enough to make transform/key bottlenecks
    /// visible in local benchmark runs.
    pub fn moderate_toy() -> Self {
        Self::new(32, 64, 1, 16, 4, 4)
    }

    /// The parameter shape described in 451.pdf.
    ///
    /// Native PBS uses the approximate TFHE decomposition and the GLWE
    /// key-switch path. Proof tests still use smaller presets unless the CLI is
    /// explicitly asked to run the paper-shaped recursive path.
    pub fn paper_v1() -> Self {
        Self::new(728, 1024, 1, 5, 4, 4)
    }

    /// TFHE2048-shaped 128-bit security preset over the Goldilocks modulus.
    ///
    /// This follows the TFHE2048 `n=2048`, `q=2^64` shape with a slightly
    /// larger Gaussian `stddev=2^14`.  The larger noise keeps the binary
    /// input-key estimate above 128 bits for the Goldilocks modulus in
    /// `TFHEprus_secure_128.py`.
    pub fn secure_128() -> Self {
        Self::new_with_noise(
            2048,
            2048,
            1,
            9,
            4,
            4,
            EncryptionNoise::DiscreteGaussianStddev { stddev: 1 << 14 },
        )
    }

    pub fn gadget_base(&self) -> u64 {
        1u64 << self.decomposition_base_log
    }

    pub fn exponent_modulus(&self) -> usize {
        2 * self.polynomial_size
    }

    pub fn encryption_noise_description(&self) -> String {
        self.encryption_noise.description()
    }
}

impl EncryptionNoise {
    pub const fn legacy_default() -> Self {
        Self::CenteredBinomial { terms: 32 }
    }

    pub fn description(&self) -> String {
        match self {
            Self::CenteredBinomial { terms } => format!("centered_binomial_terms={terms}"),
            Self::DiscreteGaussianStddev { stddev } => {
                format!("discrete_gaussian_stddev={stddev}")
            }
        }
    }

    fn validate(&self) {
        match self {
            Self::CenteredBinomial { terms } => {
                assert!(*terms > 0);
                assert!(*terms <= i64::MAX as usize);
            }
            Self::DiscreteGaussianStddev { stddev } => {
                assert!(*stddev > 0);
                assert!(*stddev <= (i64::MAX / 16) as u64);
            }
        }
    }
}
