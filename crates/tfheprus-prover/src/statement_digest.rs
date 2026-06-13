use core::any::Any;
use core::marker::PhantomData;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_batch_stark::{StarkGenericConfig, Val};
use p3_circuit::ops::{NonPrimitivePreprocessedMap, NpoTypeId};
use p3_circuit::tables::Traces;
use p3_circuit::{CircuitError, PreprocessedColumns};
use p3_circuit_prover::batch_stark_prover::{
    BatchAir, BatchTableInstance, DynamicAirEntry, NonPrimitiveTableEntry, TablePacking,
    TableProver,
};
use p3_circuit_prover::common::{CircuitTableAir, NpoAirBuilder, NpoPreprocessor};
use p3_circuit_prover::config::{GoldilocksConfig, StarkField};
use p3_field::extension::{BinomialExtensionField, QuinticTrinomialExtensionField};
use p3_field::{Algebra, ExtensionField, Field, PrimeCharacteristicRing};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use p3_lookup::builder::InteractionBuilder;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{SymbolicExpression, SymbolicExpressionExt};
use tfheprus_circuits::statement_digest::{
    statement_digest_type_id, StatementDigestCircuitRow, StatementDigestTrace,
};
use tfheprus_circuits::{P3CircuitField, SELECTOR_DIGEST_WIDTH};

#[derive(Debug, Clone)]
pub struct StatementDigestAir<F, const D: usize = 1> {
    preprocessed: Vec<F>,
    min_height: usize,
    _phantom: PhantomData<F>,
}

impl<F: Field + PrimeCharacteristicRing, const D: usize> StatementDigestAir<F, D> {
    pub fn new_with_preprocessed(preprocessed: Vec<F>, min_height: usize) -> Self {
        Self {
            preprocessed,
            min_height,
            _phantom: PhantomData,
        }
    }

    pub const fn limb_width() -> usize {
        D
    }

    pub const fn preprocessed_limb_width() -> usize {
        2
    }

    pub fn trace_to_matrix<ExtF>(rows: &[StatementDigestCircuitRow<ExtF>]) -> RowMajorMatrix<F>
    where
        ExtF: ExtensionField<F>,
    {
        assert!(D > 0);
        assert_eq!(rows.len(), 1, "statement digest must have one row");
        let width = SELECTOR_DIGEST_WIDTH * Self::limb_width();
        let mut values = F::zero_vec(width);
        for (limb, value) in rows[0].values.iter().enumerate() {
            let coeffs = value.as_basis_coefficients_slice();
            debug_assert_eq!(coeffs.len(), D);
            let base = limb * D;
            values[base..base + D].copy_from_slice(coeffs);
        }
        RowMajorMatrix::new(values, width)
    }
}

impl<F: Field + PrimeCharacteristicRing, const D: usize> BaseAir<F> for StatementDigestAir<F, D> {
    fn width(&self) -> usize {
        SELECTOR_DIGEST_WIDTH * Self::limb_width()
    }

    fn num_public_values(&self) -> usize {
        SELECTOR_DIGEST_WIDTH
    }

    fn preprocessed_width(&self) -> usize {
        SELECTOR_DIGEST_WIDTH * Self::preprocessed_limb_width()
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let width = self.preprocessed_width();
        let mut mat = RowMajorMatrix::from_flat_padded(self.preprocessed.clone(), width, F::ZERO);
        mat.pad_to_min_power_of_two_height(self.min_height, F::ZERO);
        Some(mat)
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        Vec::new()
    }

    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        Vec::new()
    }
}

impl<AB, const D: usize> Air<AB> for StatementDigestAir<AB::F, D>
where
    AB: AirBuilder + InteractionBuilder,
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let main_local = main.current_slice();
        let prep = builder.preprocessed().clone();
        let prep_local = prep.current_slice();
        let public_values = {
            let public_values = builder.public_values();
            debug_assert_eq!(public_values.len(), SELECTOR_DIGEST_WIDTH);
            core::array::from_fn::<_, SELECTOR_DIGEST_WIDTH, _>(|i| public_values[i])
        };

        for limb in 0..SELECTOR_DIGEST_WIDTH {
            let main_off = limb * D;
            let prep_off = limb * Self::preprocessed_limb_width();
            let value_coeffs = &main_local[main_off..main_off + D];
            let witness_idx: AB::Expr = prep_local[prep_off].into();
            let multiplicity: AB::Expr = prep_local[prep_off + 1].into();

            let value_limb: AB::Expr = value_coeffs[0].into();
            let public_limb: AB::Expr = public_values[limb].into();
            builder.assert_zero(multiplicity.clone() * (value_limb - public_limb));
            for coeff in &value_coeffs[1..] {
                let coeff: AB::Expr = (*coeff).into();
                builder.assert_zero(multiplicity.clone() * coeff);
            }

            let mut fields = Vec::with_capacity(1 + D);
            fields.push(witness_idx);
            fields.extend(value_coeffs.iter().map(|coeff| (*coeff).into()));
            builder.push_interaction("WitnessChecks", fields, multiplicity, 1);
        }
    }
}

impl<SC, const D: usize> BatchAir<SC> for StatementDigestAir<Val<SC>, D>
where
    SC: StarkGenericConfig + Send + Sync,
    Val<SC>: StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
}

#[derive(Clone)]
pub struct StatementDigestPreprocessor;

impl NpoPreprocessor<P3Goldilocks> for StatementDigestPreprocessor {
    fn preprocess(
        &self,
        _circuit: &dyn Any,
        preprocessed: &mut dyn Any,
    ) -> Result<NonPrimitivePreprocessedMap<P3Goldilocks>, CircuitError> {
        if let Some(prep) = preprocessed.downcast_mut::<PreprocessedColumns<P3Goldilocks, 1>>() {
            return collect_statement_digest_preprocessed(&prep.non_primitive);
        }

        if let Some(prep) = preprocessed.downcast_mut::<PreprocessedColumns<P3CircuitField, 2>>() {
            let mut result = NonPrimitivePreprocessedMap::new();
            let op_type = statement_digest_type_id();
            if let Some(values) = prep.non_primitive.get(&op_type) {
                if !values
                    .len()
                    .is_multiple_of(StatementDigestAir::<P3Goldilocks>::preprocessed_limb_width())
                {
                    return Err(CircuitError::InvalidPreprocessedValues);
                }
                let values = values
                    .iter()
                    .map(|value| {
                        value
                            .as_base()
                            .ok_or(CircuitError::InvalidPreprocessedValues)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                result.insert(op_type, values);
            }
            return Ok(result);
        }

        Ok(NonPrimitivePreprocessedMap::new())
    }
}

fn collect_statement_digest_preprocessed(
    values_by_op: &NonPrimitivePreprocessedMap<P3Goldilocks>,
) -> Result<NonPrimitivePreprocessedMap<P3Goldilocks>, CircuitError> {
    let mut result = NonPrimitivePreprocessedMap::new();
    let op_type = statement_digest_type_id();
    if let Some(values) = values_by_op.get(&op_type) {
        if !values
            .len()
            .is_multiple_of(StatementDigestAir::<P3Goldilocks>::preprocessed_limb_width())
        {
            return Err(CircuitError::InvalidPreprocessedValues);
        }
        result.insert(op_type, values.clone());
    }
    Ok(result)
}

#[derive(Clone)]
pub struct StatementDigestAirBuilder;

impl<SC, const D: usize> NpoAirBuilder<SC, D> for StatementDigestAirBuilder
where
    SC: StarkGenericConfig + 'static + Send + Sync,
    Val<SC>: StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    fn try_build(
        &self,
        op_type: &NpoTypeId,
        prep_base: &[Val<SC>],
        min_height: usize,
        _lanes: usize,
        _constraint_profile: p3_circuit_prover::ConstraintProfile,
    ) -> Option<(CircuitTableAir<SC, D>, usize)> {
        if *op_type != statement_digest_type_id() {
            return None;
        }

        let prep_width =
            SELECTOR_DIGEST_WIDTH * StatementDigestAir::<Val<SC>, D>::preprocessed_limb_width();
        if prep_base.len() != prep_width {
            return None;
        }

        let padded_rows = min_height.next_power_of_two().max(1);
        let degree = padded_rows.trailing_zeros() as usize;
        let air =
            StatementDigestAir::<Val<SC>, D>::new_with_preprocessed(prep_base.to_vec(), min_height);

        Some((
            CircuitTableAir::Dynamic(DynamicAirEntry::new(Box::new(air))),
            degree,
        ))
    }
}

pub struct StatementDigestProver;

impl StatementDigestProver {
    pub const fn new() -> Self {
        Self
    }

    fn batch_instance_from_traces<CF, const D: usize>(
        &self,
        _config: &GoldilocksConfig,
        packing: &TablePacking,
        traces: &Traces<CF>,
    ) -> Option<BatchTableInstance<GoldilocksConfig>>
    where
        CF: ExtensionField<P3Goldilocks>,
    {
        let op_type = statement_digest_type_id();
        let trace = traces.non_primitive_traces.get(&op_type)?;
        if trace.rows() != 1 {
            return None;
        }
        let trace = trace.as_any().downcast_ref::<StatementDigestTrace<CF>>()?;
        let min_height = packing.min_trace_height();
        let prep_limb_width = StatementDigestAir::<P3Goldilocks, D>::preprocessed_limb_width();
        let mut preprocessed = P3Goldilocks::zero_vec(SELECTOR_DIGEST_WIDTH * prep_limb_width);
        for (limb, wid) in trace.rows[0].input_wids.iter().enumerate() {
            let base = limb * prep_limb_width;
            preprocessed[base] = wid.base_field_index::<P3Goldilocks, D>();
            preprocessed[base + 1] = P3Goldilocks::ZERO - P3Goldilocks::ONE;
        }

        let public_values = trace.rows[0]
            .values
            .iter()
            .map(|value| value.as_base())
            .collect::<Option<Vec<_>>>()?;
        let air =
            StatementDigestAir::<P3Goldilocks, D>::new_with_preprocessed(preprocessed, min_height);
        let matrix = StatementDigestAir::<P3Goldilocks, D>::trace_to_matrix(&trace.rows);

        Some(BatchTableInstance {
            op_type,
            air: DynamicAirEntry::new(Box::new(air)),
            trace: matrix,
            public_values,
            rows: trace.total_rows(),
            lanes: 1,
        })
    }
}

impl TableProver<GoldilocksConfig> for StatementDigestProver {
    fn op_type(&self) -> NpoTypeId {
        statement_digest_type_id()
    }

    fn batch_instance_d1(
        &self,
        config: &GoldilocksConfig,
        packing: &TablePacking,
        traces: &Traces<P3Goldilocks>,
    ) -> Option<BatchTableInstance<GoldilocksConfig>> {
        self.batch_instance_from_traces::<_, 1>(config, packing, traces)
    }

    fn batch_instance_d2(
        &self,
        config: &GoldilocksConfig,
        packing: &TablePacking,
        traces: &Traces<BinomialExtensionField<P3Goldilocks, 2>>,
    ) -> Option<BatchTableInstance<GoldilocksConfig>> {
        self.batch_instance_from_traces::<_, 2>(config, packing, traces)
    }

    fn batch_instance_d4(
        &self,
        _config: &GoldilocksConfig,
        _packing: &TablePacking,
        _traces: &Traces<BinomialExtensionField<P3Goldilocks, 4>>,
    ) -> Option<BatchTableInstance<GoldilocksConfig>> {
        None
    }

    fn batch_instance_d6(
        &self,
        _config: &GoldilocksConfig,
        _packing: &TablePacking,
        _traces: &Traces<BinomialExtensionField<P3Goldilocks, 6>>,
    ) -> Option<BatchTableInstance<GoldilocksConfig>> {
        None
    }

    fn batch_instance_d8(
        &self,
        _config: &GoldilocksConfig,
        _packing: &TablePacking,
        _traces: &Traces<BinomialExtensionField<P3Goldilocks, 8>>,
    ) -> Option<BatchTableInstance<GoldilocksConfig>> {
        None
    }

    fn batch_instance_d5(
        &self,
        _config: &GoldilocksConfig,
        _packing: &TablePacking,
        _traces: &Traces<QuinticTrinomialExtensionField<P3Goldilocks>>,
    ) -> Option<BatchTableInstance<GoldilocksConfig>> {
        None
    }

    fn batch_air_from_table_entry(
        &self,
        _config: &GoldilocksConfig,
        degree: usize,
        _circuit_extension_degree: u32,
        _table_entry: &NonPrimitiveTableEntry<GoldilocksConfig>,
    ) -> Result<DynamicAirEntry<GoldilocksConfig>, String> {
        match degree {
            1 => Ok(DynamicAirEntry::new(Box::new(StatementDigestAir::<
                P3Goldilocks,
                1,
            >::new_with_preprocessed(
                Vec::new(), 1
            )))),
            2 => Ok(DynamicAirEntry::new(Box::new(StatementDigestAir::<
                P3Goldilocks,
                2,
            >::new_with_preprocessed(
                Vec::new(), 1
            )))),
            d => Err(format!("unsupported statement-digest extension degree {d}")),
        }
    }

    fn air_with_committed_preprocessed(
        &self,
        committed_prep: Vec<P3Goldilocks>,
        min_height: usize,
        _lanes: usize,
        circuit_extension_degree: u32,
    ) -> Option<DynamicAirEntry<GoldilocksConfig>> {
        match circuit_extension_degree {
            1 => Some(DynamicAirEntry::new(Box::new(StatementDigestAir::<
                P3Goldilocks,
                1,
            >::new_with_preprocessed(
                committed_prep, min_height
            )))),
            2 => Some(DynamicAirEntry::new(Box::new(StatementDigestAir::<
                P3Goldilocks,
                2,
            >::new_with_preprocessed(
                committed_prep, min_height
            )))),
            _ => None,
        }
    }
}
