use core::any::Any;
use core::marker::PhantomData;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_batch_stark::{StarkGenericConfig, Val};
use p3_circuit::ops::{NonPrimitivePreprocessedMap, NpoTypeId};
use p3_circuit::tables::Traces;
use p3_circuit::{Circuit, CircuitError, PreprocessedColumns};
use p3_circuit_prover::batch_stark_prover::{
    BatchAir, BatchTableInstance, DynamicAirEntry, NonPrimitiveTableEntry, TablePacking,
    TableProver,
};
use p3_circuit_prover::common::{CircuitTableAir, NpoAirBuilder, NpoPreprocessor};
use p3_circuit_prover::config::StarkField;
use p3_field::extension::{BinomialExtensionField, QuinticTrinomialExtensionField};
use p3_field::{Algebra, Field, PrimeCharacteristicRing};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use p3_lookup::builder::InteractionBuilder;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{SymbolicExpression, SymbolicExpressionExt};
use tfheprus_circuits::range_check::{
    parse_range_check_bit_count, range_check_type_id, RangeCheckCircuitRow, RangeCheckTrace,
};

pub const RANGE_CHECK_DEFAULT_LANES: usize = 8;

#[derive(Debug, Clone)]
pub struct RangeCheckAir<F> {
    bit_count: usize,
    lanes: usize,
    preprocessed: Vec<F>,
    min_height: usize,
    _phantom: PhantomData<F>,
}

impl<F: Field + PrimeCharacteristicRing> RangeCheckAir<F> {
    pub fn new_with_preprocessed(
        bit_count: usize,
        lanes: usize,
        preprocessed: Vec<F>,
        min_height: usize,
    ) -> Self {
        assert!((1..=32).contains(&bit_count));
        Self {
            bit_count,
            lanes: lanes.max(1),
            preprocessed,
            min_height,
            _phantom: PhantomData,
        }
    }

    pub const fn lane_width_for(bit_count: usize) -> usize {
        1 + bit_count
    }

    pub const fn preprocessed_lane_width() -> usize {
        2
    }

    pub fn trace_to_matrix(
        rows: &[RangeCheckCircuitRow<F>],
        bit_count: usize,
        lanes: usize,
    ) -> RowMajorMatrix<F> {
        let lanes = lanes.max(1);
        let lane_width = Self::lane_width_for(bit_count);
        let row_width = lanes * lane_width;
        let num_rows = rows.len().div_ceil(lanes).max(1);
        let mut values = F::zero_vec(num_rows * row_width);

        for (op_idx, row) in rows.iter().enumerate() {
            debug_assert_eq!(row.bits.len(), bit_count);
            let r = op_idx / lanes;
            let lane = op_idx % lanes;
            let base = r * row_width + lane * lane_width;
            values[base] = row.value;
            for bit_index in 0..bit_count {
                values[base + 1 + bit_index] = row.bits[bit_index];
            }
        }

        let mut mat = RowMajorMatrix::new(values, row_width);
        mat.pad_to_power_of_two_height(F::ZERO);
        mat
    }
}

impl<F: Field + PrimeCharacteristicRing> BaseAir<F> for RangeCheckAir<F> {
    fn width(&self) -> usize {
        self.lanes * Self::lane_width_for(self.bit_count)
    }

    fn preprocessed_width(&self) -> usize {
        self.lanes * Self::preprocessed_lane_width()
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

impl<AB> Air<AB> for RangeCheckAir<AB::F>
where
    AB: AirBuilder + InteractionBuilder,
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let main_local = main.current_slice();
        let prep = builder.preprocessed().clone();
        let prep_local = prep.current_slice();
        let lane_width = Self::lane_width_for(self.bit_count);
        let prep_lane_width = Self::preprocessed_lane_width();

        for lane in 0..self.lanes {
            let main_off = lane * lane_width;
            let prep_off = lane * prep_lane_width;
            let value: AB::Expr = main_local[main_off].into();
            let mut reconstructed = AB::Expr::ZERO;

            for bit_index in 0..self.bit_count {
                let bit: AB::Expr = main_local[main_off + 1 + bit_index].into();
                builder.assert_zero(bit.clone() * (bit.clone() - AB::Expr::ONE));
                let scale = AB::Expr::from(AB::F::from_u64(1u64 << bit_index));
                reconstructed += bit * scale;
            }

            builder.assert_zero(value.clone() - reconstructed);

            let witness_idx: AB::Expr = prep_local[prep_off].into();
            let multiplicity: AB::Expr = prep_local[prep_off + 1].into();
            builder.push_interaction("WitnessChecks", vec![witness_idx, value], multiplicity, 1);
        }
    }
}

impl<SC> BatchAir<SC> for RangeCheckAir<Val<SC>>
where
    SC: StarkGenericConfig + Send + Sync,
    Val<SC>: StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
}

#[derive(Clone)]
pub struct RangeCheckPreprocessor;

impl NpoPreprocessor<P3Goldilocks> for RangeCheckPreprocessor {
    fn preprocess(
        &self,
        _circuit: &dyn Any,
        preprocessed: &mut dyn Any,
    ) -> Result<NonPrimitivePreprocessedMap<P3Goldilocks>, CircuitError> {
        let Some(prep) = preprocessed.downcast_mut::<PreprocessedColumns<P3Goldilocks, 1>>() else {
            return Ok(NonPrimitivePreprocessedMap::new());
        };

        let mut result = NonPrimitivePreprocessedMap::new();
        for (op_type, values) in &prep.non_primitive {
            if parse_range_check_bit_count(op_type).is_some() {
                if !values
                    .len()
                    .is_multiple_of(RangeCheckAir::<P3Goldilocks>::preprocessed_lane_width())
                {
                    return Err(CircuitError::InvalidPreprocessedValues);
                }
                result.insert(op_type.clone(), values.clone());
            }
        }
        Ok(result)
    }
}

#[derive(Clone)]
pub struct RangeCheckAirBuilder {
    bit_count: usize,
    lanes: usize,
}

impl RangeCheckAirBuilder {
    pub fn new(bit_count: usize, lanes: usize) -> Self {
        Self {
            bit_count,
            lanes: lanes.max(1),
        }
    }
}

impl<SC> NpoAirBuilder<SC, 1> for RangeCheckAirBuilder
where
    SC: StarkGenericConfig + 'static + Send + Sync,
    Val<SC>: StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    fn lanes(&self) -> usize {
        self.lanes
    }

    fn try_build(
        &self,
        op_type: &NpoTypeId,
        prep_base: &[Val<SC>],
        min_height: usize,
        lanes: usize,
        _constraint_profile: p3_circuit_prover::ConstraintProfile,
    ) -> Option<(CircuitTableAir<SC, 1>, usize)> {
        if parse_range_check_bit_count(op_type)? != self.bit_count {
            return None;
        }

        let prep_lane_width = RangeCheckAir::<Val<SC>>::preprocessed_lane_width();
        if !prep_base.len().is_multiple_of(prep_lane_width) {
            return None;
        }

        let num_ops = prep_base.len() / prep_lane_width;
        let num_rows = num_ops.div_ceil(lanes).max(1);
        let padded_rows = num_rows
            .next_power_of_two()
            .max(min_height.next_power_of_two());
        let degree = padded_rows.trailing_zeros() as usize;
        let air = RangeCheckAir::<Val<SC>>::new_with_preprocessed(
            self.bit_count,
            lanes,
            prep_base.to_vec(),
            min_height,
        );

        Some((
            CircuitTableAir::Dynamic(DynamicAirEntry::new(Box::new(air))),
            degree,
        ))
    }
}

pub struct RangeCheckProver {
    bit_count: usize,
    lanes: usize,
}

impl RangeCheckProver {
    pub fn new(bit_count: usize, lanes: usize) -> Self {
        Self {
            bit_count,
            lanes: lanes.max(1),
        }
    }

    fn batch_instance_from_traces<SC, CF>(
        &self,
        _config: &SC,
        packing: &TablePacking,
        traces: &Traces<CF>,
    ) -> Option<BatchTableInstance<SC>>
    where
        SC: StarkGenericConfig + 'static + Send + Sync,
        Val<SC>: StarkField,
        SymbolicExpressionExt<Val<SC>, SC::Challenge>:
            Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
    {
        let op_type = range_check_type_id(self.bit_count);
        let trace = traces.non_primitive_traces.get(&op_type)?;
        if trace.rows() == 0 {
            return None;
        }
        let trace = trace.as_any().downcast_ref::<RangeCheckTrace<Val<SC>>>()?;
        let lanes = packing.npo_lanes(&op_type).unwrap_or(self.lanes).max(1);
        let min_height = packing.min_trace_height();
        let prep_lane_width = RangeCheckAir::<Val<SC>>::preprocessed_lane_width();
        let mut preprocessed = Val::<SC>::zero_vec(trace.total_rows() * prep_lane_width);
        for (row_index, row) in trace.rows.iter().enumerate() {
            let base = row_index * prep_lane_width;
            preprocessed[base] = row.input_wid.base_field_index::<Val<SC>, 1>();
            preprocessed[base + 1] = Val::<SC>::ZERO - Val::<SC>::ONE;
        }

        let air = RangeCheckAir::<Val<SC>>::new_with_preprocessed(
            self.bit_count,
            lanes,
            preprocessed,
            min_height,
        );
        let matrix = RangeCheckAir::<Val<SC>>::trace_to_matrix(&trace.rows, self.bit_count, lanes);

        Some(BatchTableInstance {
            op_type,
            air: DynamicAirEntry::new(Box::new(air)),
            trace: matrix,
            public_values: Vec::new(),
            rows: trace.total_rows(),
            lanes,
        })
    }
}

impl<SC> TableProver<SC> for RangeCheckProver
where
    SC: StarkGenericConfig + 'static + Send + Sync,
    Val<SC>: StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    fn op_type(&self) -> NpoTypeId {
        range_check_type_id(self.bit_count)
    }

    fn lanes(&self) -> usize {
        self.lanes
    }

    fn batch_instance_d1(
        &self,
        config: &SC,
        packing: &TablePacking,
        traces: &Traces<Val<SC>>,
    ) -> Option<BatchTableInstance<SC>> {
        self.batch_instance_from_traces(config, packing, traces)
    }

    fn batch_instance_d2(
        &self,
        config: &SC,
        packing: &TablePacking,
        traces: &Traces<BinomialExtensionField<Val<SC>, 2>>,
    ) -> Option<BatchTableInstance<SC>> {
        self.batch_instance_from_traces(config, packing, traces)
    }

    fn batch_instance_d4(
        &self,
        config: &SC,
        packing: &TablePacking,
        traces: &Traces<BinomialExtensionField<Val<SC>, 4>>,
    ) -> Option<BatchTableInstance<SC>> {
        self.batch_instance_from_traces(config, packing, traces)
    }

    fn batch_instance_d6(
        &self,
        config: &SC,
        packing: &TablePacking,
        traces: &Traces<BinomialExtensionField<Val<SC>, 6>>,
    ) -> Option<BatchTableInstance<SC>> {
        self.batch_instance_from_traces(config, packing, traces)
    }

    fn batch_instance_d8(
        &self,
        config: &SC,
        packing: &TablePacking,
        traces: &Traces<BinomialExtensionField<Val<SC>, 8>>,
    ) -> Option<BatchTableInstance<SC>> {
        self.batch_instance_from_traces(config, packing, traces)
    }

    fn batch_instance_d5(
        &self,
        config: &SC,
        packing: &TablePacking,
        traces: &Traces<QuinticTrinomialExtensionField<Val<SC>>>,
    ) -> Option<BatchTableInstance<SC>> {
        self.batch_instance_from_traces(config, packing, traces)
    }

    fn batch_air_from_table_entry(
        &self,
        _config: &SC,
        _degree: usize,
        _circuit_extension_degree: u32,
        table_entry: &NonPrimitiveTableEntry<SC>,
    ) -> Result<DynamicAirEntry<SC>, String> {
        let bit_count = parse_range_check_bit_count(&table_entry.op_type)
            .ok_or_else(|| format!("not a range-check op: {}", table_entry.op_type))?;
        let air = RangeCheckAir::<Val<SC>>::new_with_preprocessed(
            bit_count,
            table_entry.lanes,
            Vec::new(),
            1,
        );
        Ok(DynamicAirEntry::new(Box::new(air)))
    }

    fn air_with_committed_preprocessed(
        &self,
        committed_prep: Vec<Val<SC>>,
        min_height: usize,
        lanes: usize,
        _circuit_extension_degree: u32,
    ) -> Option<DynamicAirEntry<SC>> {
        let air = RangeCheckAir::<Val<SC>>::new_with_preprocessed(
            self.bit_count,
            lanes,
            committed_prep,
            min_height,
        );
        Some(DynamicAirEntry::new(Box::new(air)))
    }
}

pub fn range_check_bit_counts(circuit: &Circuit<P3Goldilocks>) -> Vec<usize> {
    let mut bit_counts = circuit
        .enabled_ops
        .keys()
        .filter_map(parse_range_check_bit_count)
        .collect::<Vec<_>>();
    bit_counts.sort_unstable();
    bit_counts.dedup();
    bit_counts
}

pub fn proof_range_check_bit_counts<SC>(
    proof: &p3_circuit_prover::BatchStarkProof<SC>,
) -> Vec<usize>
where
    SC: StarkGenericConfig,
{
    let mut bit_counts = proof
        .non_primitives
        .iter()
        .filter_map(|entry| parse_range_check_bit_count(&entry.op_type))
        .collect::<Vec<_>>();
    bit_counts.sort_unstable();
    bit_counts.dedup();
    bit_counts
}
