use core::any::Any;
use core::fmt::{self, Debug};

use p3_circuit::builder::{
    CircuitBuilder, CircuitBuilderError, NonPrimitiveOperationData, NpoCircuitPlugin,
    NpoLoweringContext,
};
use p3_circuit::ops::{
    ExecutionContext, NonPrimitiveExecutor, NpoConfig, NpoTypeId, Op, OpStateMap,
    PreprocessedWriter,
};
use p3_circuit::tables::{NonPrimitiveTrace, TraceGeneratorFn};
use p3_circuit::{CircuitError, ExprId, WitnessId};
use p3_field::{ExtensionField, Field, PrimeCharacteristicRing, PrimeField64};
use p3_goldilocks::Goldilocks as P3Goldilocks;

const RANGE_CHECK_TYPE_PREFIX: &str = "tfheprus/range_check_u";

#[derive(Debug, Clone)]
pub struct RangeCheckCircuitRow<F> {
    pub input_wid: WitnessId,
    pub value: F,
    pub bits: Vec<F>,
}

#[derive(Debug, Default)]
pub struct RangeCheckExecutionState<F> {
    pub bit_count: usize,
    pub rows: Vec<RangeCheckCircuitRow<F>>,
}

#[derive(Debug, Clone)]
pub struct RangeCheckTrace<F> {
    pub op_type: NpoTypeId,
    pub bit_count: usize,
    pub rows: Vec<RangeCheckCircuitRow<F>>,
}

impl<F> RangeCheckTrace<F> {
    pub const fn total_rows(&self) -> usize {
        self.rows.len()
    }
}

impl<TraceF: Clone + Send + Sync + 'static, CF> NonPrimitiveTrace<CF> for RangeCheckTrace<TraceF> {
    fn op_type(&self) -> NpoTypeId {
        self.op_type.clone()
    }

    fn rows(&self) -> usize {
        self.total_rows()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn boxed_clone(&self) -> Box<dyn NonPrimitiveTrace<CF>> {
        Box::new(self.clone())
    }
}

#[derive(Clone)]
struct RangeCheckCircuitPlugin {
    bit_count: usize,
}

impl Debug for RangeCheckCircuitPlugin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RangeCheckCircuitPlugin")
            .field("bit_count", &self.bit_count)
            .finish()
    }
}

impl<F> NpoCircuitPlugin<F> for RangeCheckCircuitPlugin
where
    F: Field + ExtensionField<P3Goldilocks> + PrimeCharacteristicRing + Send + Sync + 'static,
{
    fn type_id(&self) -> NpoTypeId {
        range_check_type_id(self.bit_count)
    }

    fn lower(
        &self,
        data: &NonPrimitiveOperationData<F>,
        output_exprs: &[(u32, ExprId)],
        ctx: &mut NpoLoweringContext<'_, F>,
    ) -> Result<Op<F>, CircuitBuilderError> {
        if data.input_exprs.len() != 1 || data.input_exprs[0].len() != 1 {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "RangeCheck",
                expected: "1 input witness".to_string(),
                got: data.input_exprs.len(),
            });
        }
        if !output_exprs.is_empty() {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "RangeCheck",
                expected: "no outputs".to_string(),
                got: output_exprs.len(),
            });
        }

        let input_wid = ctx.resolve_witness_id(data.input_exprs[0][0], "RangeCheck input")?;
        Ok(Op::NonPrimitiveOpWithExecutor {
            inputs: vec![vec![input_wid]],
            outputs: Vec::new(),
            executor: Box::new(RangeCheckExecutor::<F>::new(self.bit_count)),
            op_id: data.op_id,
        })
    }

    fn trace_generator(&self) -> TraceGeneratorFn<F> {
        range_check_trace_generator(self.bit_count)
    }

    fn config(&self) -> NpoConfig {
        NpoConfig::new(self.bit_count)
    }
}

pub fn register_range_check_npo<F>(builder: &mut CircuitBuilder<F>, bit_count: usize)
where
    F: Field + ExtensionField<P3Goldilocks> + PrimeCharacteristicRing + Send + Sync + 'static,
{
    assert_valid_bit_count(bit_count);
    builder.register_npo(RangeCheckCircuitPlugin { bit_count });
}

pub fn range_check_expr<F>(builder: &mut CircuitBuilder<F>, value: ExprId, bit_count: usize)
where
    F: Field + ExtensionField<P3Goldilocks> + PrimeCharacteristicRing + Send + Sync + 'static,
{
    assert_valid_bit_count(bit_count);
    builder.push_non_primitive_op_with_outputs(
        range_check_type_id(bit_count),
        vec![vec![value]],
        Vec::new(),
        None,
        "range_check",
    );
}

pub fn range_check_type_id(bit_count: usize) -> NpoTypeId {
    NpoTypeId::new(format!("{RANGE_CHECK_TYPE_PREFIX}{bit_count}"))
}

pub fn parse_range_check_bit_count(op_type: &NpoTypeId) -> Option<usize> {
    op_type
        .as_str()
        .strip_prefix(RANGE_CHECK_TYPE_PREFIX)?
        .parse()
        .ok()
}

fn assert_valid_bit_count(bit_count: usize) {
    assert!((1..=63).contains(&bit_count));
}

macro_rules! define_range_check_trace_generators {
    ($(($name:ident, $bit_count:literal)),+ $(,)?) => {
        $(
            fn $name<F>(op_states: &OpStateMap) -> Result<Option<Box<dyn NonPrimitiveTrace<F>>>, CircuitError>
            where
                F: Field + Clone + Send + Sync + 'static,
            {
                generate_range_check_trace_for_bit_count(op_states, $bit_count)
            }
        )+

        fn range_check_trace_generator<F>(bit_count: usize) -> TraceGeneratorFn<F>
        where
            F: Field + Clone + Send + Sync + 'static,
        {
            match bit_count {
                $($bit_count => $name::<F>,)+
                _ => panic!("unsupported range-check bit count {bit_count}"),
            }
        }
    };
}

define_range_check_trace_generators!(
    (generate_range_check_trace_u1, 1),
    (generate_range_check_trace_u2, 2),
    (generate_range_check_trace_u3, 3),
    (generate_range_check_trace_u4, 4),
    (generate_range_check_trace_u5, 5),
    (generate_range_check_trace_u6, 6),
    (generate_range_check_trace_u7, 7),
    (generate_range_check_trace_u8, 8),
    (generate_range_check_trace_u9, 9),
    (generate_range_check_trace_u10, 10),
    (generate_range_check_trace_u11, 11),
    (generate_range_check_trace_u12, 12),
    (generate_range_check_trace_u13, 13),
    (generate_range_check_trace_u14, 14),
    (generate_range_check_trace_u15, 15),
    (generate_range_check_trace_u16, 16),
    (generate_range_check_trace_u17, 17),
    (generate_range_check_trace_u18, 18),
    (generate_range_check_trace_u19, 19),
    (generate_range_check_trace_u20, 20),
    (generate_range_check_trace_u21, 21),
    (generate_range_check_trace_u22, 22),
    (generate_range_check_trace_u23, 23),
    (generate_range_check_trace_u24, 24),
    (generate_range_check_trace_u25, 25),
    (generate_range_check_trace_u26, 26),
    (generate_range_check_trace_u27, 27),
    (generate_range_check_trace_u28, 28),
    (generate_range_check_trace_u29, 29),
    (generate_range_check_trace_u30, 30),
    (generate_range_check_trace_u31, 31),
    (generate_range_check_trace_u32, 32),
    (generate_range_check_trace_u33, 33),
    (generate_range_check_trace_u34, 34),
    (generate_range_check_trace_u35, 35),
    (generate_range_check_trace_u36, 36),
    (generate_range_check_trace_u37, 37),
    (generate_range_check_trace_u38, 38),
    (generate_range_check_trace_u39, 39),
    (generate_range_check_trace_u40, 40),
    (generate_range_check_trace_u41, 41),
    (generate_range_check_trace_u42, 42),
    (generate_range_check_trace_u43, 43),
    (generate_range_check_trace_u44, 44),
    (generate_range_check_trace_u45, 45),
    (generate_range_check_trace_u46, 46),
    (generate_range_check_trace_u47, 47),
    (generate_range_check_trace_u48, 48),
    (generate_range_check_trace_u49, 49),
    (generate_range_check_trace_u50, 50),
    (generate_range_check_trace_u51, 51),
    (generate_range_check_trace_u52, 52),
    (generate_range_check_trace_u53, 53),
    (generate_range_check_trace_u54, 54),
    (generate_range_check_trace_u55, 55),
    (generate_range_check_trace_u56, 56),
    (generate_range_check_trace_u57, 57),
    (generate_range_check_trace_u58, 58),
    (generate_range_check_trace_u59, 59),
    (generate_range_check_trace_u60, 60),
    (generate_range_check_trace_u61, 61),
    (generate_range_check_trace_u62, 62),
    (generate_range_check_trace_u63, 63),
);

#[derive(Clone)]
struct RangeCheckExecutor<F> {
    op_type: NpoTypeId,
    bit_count: usize,
    _phantom: core::marker::PhantomData<F>,
}

impl<F> RangeCheckExecutor<F> {
    fn new(bit_count: usize) -> Self {
        Self {
            op_type: range_check_type_id(bit_count),
            bit_count,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<F> Debug for RangeCheckExecutor<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RangeCheckExecutor")
            .field("op_type", &self.op_type)
            .field("bit_count", &self.bit_count)
            .finish()
    }
}

impl<F> NonPrimitiveExecutor<F> for RangeCheckExecutor<F>
where
    F: Field + ExtensionField<P3Goldilocks> + PrimeCharacteristicRing + Send + Sync + 'static,
{
    fn execute(
        &self,
        inputs: &[Vec<WitnessId>],
        outputs: &[Vec<WitnessId>],
        ctx: &mut ExecutionContext<'_, F>,
    ) -> Result<(), CircuitError> {
        if inputs.len() != 1 || inputs[0].len() != 1 {
            return Err(CircuitError::NonPrimitiveOpLayoutMismatch {
                op: self.op_type.clone(),
                expected: "1 input witness".to_string(),
                got: inputs.len(),
            });
        }
        if !outputs.is_empty() {
            return Err(CircuitError::NonPrimitiveOpLayoutMismatch {
                op: self.op_type.clone(),
                expected: "no outputs".to_string(),
                got: outputs.len(),
            });
        }

        let input_wid = inputs[0][0];
        let value = ctx.get_witness(input_wid)?;
        let Some(base_value) = value.as_base() else {
            return Err(CircuitError::InvalidPreprocessing {
                reason: "range check witness must be base-field embedded",
            });
        };
        let raw = base_value.as_canonical_u64();
        let limit = 1u64 << self.bit_count;
        if raw >= limit {
            return Err(CircuitError::InvalidPreprocessing {
                reason: "range check witness is out of range",
            });
        }

        let bits = (0..self.bit_count)
            .map(|bit_index| F::from(P3Goldilocks::from_u64((raw >> bit_index) & 1)))
            .collect();

        let state = ctx.get_op_state_mut::<RangeCheckExecutionState<F>>(&self.op_type);
        state.bit_count = self.bit_count;
        state.rows.push(RangeCheckCircuitRow {
            input_wid,
            value,
            bits,
        });

        Ok(())
    }

    fn op_type(&self) -> &NpoTypeId {
        &self.op_type
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn preprocess(
        &self,
        inputs: &[Vec<WitnessId>],
        _outputs: &[Vec<WitnessId>],
        preprocessed: &mut dyn PreprocessedWriter<F>,
    ) -> Result<(), CircuitError> {
        if inputs.len() != 1 || inputs[0].len() != 1 {
            return Err(CircuitError::NonPrimitiveOpLayoutMismatch {
                op: self.op_type.clone(),
                expected: "1 input witness".to_string(),
                got: inputs.len(),
            });
        }
        preprocessed.register_non_primitive_witness_reads(&self.op_type, &[inputs[0][0]])?;
        preprocessed
            .register_non_primitive_preprocessed_no_read(&self.op_type, &[F::ZERO - F::ONE]);
        Ok(())
    }

    fn boxed(&self) -> Box<dyn NonPrimitiveExecutor<F>> {
        Box::new(self.clone())
    }
}

pub fn generate_range_check_trace<F>(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<F>>>, CircuitError>
where
    F: Field + Clone + Send + Sync + 'static,
{
    for bit_count in 1..=63 {
        if let Some(trace) = generate_range_check_trace_for_bit_count(op_states, bit_count)? {
            return Ok(Some(trace));
        }
    }
    Ok(None)
}

fn generate_range_check_trace_for_bit_count<F>(
    op_states: &OpStateMap,
    bit_count: usize,
) -> Result<Option<Box<dyn NonPrimitiveTrace<F>>>, CircuitError>
where
    F: Field + Clone + Send + Sync + 'static,
{
    let op_type = range_check_type_id(bit_count);
    let Some(state) = op_states.get(&op_type) else {
        return Ok(None);
    };
    let Some(state) = state.downcast_ref::<RangeCheckExecutionState<F>>() else {
        return Ok(None);
    };
    if state.rows.is_empty() {
        return Ok(None);
    }
    Ok(Some(Box::new(RangeCheckTrace {
        op_type,
        bit_count: state.bit_count,
        rows: state.rows.clone(),
    })))
}

#[cfg(test)]
mod tests {
    use p3_goldilocks::Goldilocks;

    use super::*;

    fn range_checked_private_input_circuit(
        bit_count: usize,
    ) -> Result<p3_circuit::circuit::Circuit<Goldilocks>, p3_circuit::CircuitBuilderError> {
        let mut builder = CircuitBuilder::<Goldilocks>::new();
        register_range_check_npo(&mut builder, bit_count);
        let value = builder.alloc_private_input("range_value");
        range_check_expr(&mut builder, value, bit_count);
        let one = builder.define_const(Goldilocks::ONE);
        let shifted = builder.add(value, one);
        let expected = builder.public_input();
        builder.connect(shifted, expected);
        builder.build()
    }

    #[test]
    fn range_check_accepts_valid_private_witness() {
        let circuit = range_checked_private_input_circuit(4).unwrap();
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&[Goldilocks::from_u64(16)])
            .unwrap();
        runner
            .set_private_inputs(&[Goldilocks::from_u64(15)])
            .unwrap();

        let traces = runner.run().unwrap();
        assert!(traces
            .non_primitive_traces
            .contains_key(&range_check_type_id(4)));
    }

    #[test]
    fn range_check_rejects_out_of_range_private_witness() {
        let circuit = range_checked_private_input_circuit(4).unwrap();
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&[Goldilocks::from_u64(17)])
            .unwrap();
        runner
            .set_private_inputs(&[Goldilocks::from_u64(16)])
            .unwrap();

        assert!(runner.run().is_err());
    }

    #[test]
    fn range_check_generates_distinct_traces_for_multiple_bit_counts() {
        let mut builder = CircuitBuilder::<Goldilocks>::new();
        register_range_check_npo(&mut builder, 5);
        register_range_check_npo(&mut builder, 46);
        let small = builder.alloc_private_input("small_range_value");
        let large = builder.alloc_private_input("large_range_value");
        range_check_expr(&mut builder, small, 5);
        range_check_expr(&mut builder, large, 46);
        let sum = builder.add(small, large);
        let expected = builder.public_input();
        builder.connect(sum, expected);
        let circuit = builder.build().unwrap();

        let small_value = Goldilocks::from_u64(16);
        let large_value = Goldilocks::from_u64(1u64 << 45);
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&[small_value + large_value])
            .unwrap();
        runner
            .set_private_inputs(&[small_value, large_value])
            .unwrap();
        let traces = runner.run().unwrap();

        let small_trace = traces
            .non_primitive_trace::<RangeCheckTrace<Goldilocks>>(&range_check_type_id(5))
            .expect("u5 range-check trace should be generated");
        let large_trace = traces
            .non_primitive_trace::<RangeCheckTrace<Goldilocks>>(&range_check_type_id(46))
            .expect("u46 range-check trace should be generated");

        assert_eq!(small_trace.rows.len(), 1);
        assert_eq!(small_trace.rows[0].value, small_value);
        assert_eq!(large_trace.rows.len(), 1);
        assert_eq!(large_trace.rows[0].value, large_value);
    }
}
