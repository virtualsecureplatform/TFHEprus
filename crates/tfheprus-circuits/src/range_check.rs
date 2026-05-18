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
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};

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
    F: Field + PrimeField64 + PrimeCharacteristicRing + Send + Sync + 'static,
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
        generate_range_check_trace::<F>
    }

    fn config(&self) -> NpoConfig {
        NpoConfig::new(self.bit_count)
    }
}

pub fn register_range_check_npo<F>(builder: &mut CircuitBuilder<F>, bit_count: usize)
where
    F: Field + PrimeField64 + PrimeCharacteristicRing + Send + Sync + 'static,
{
    assert_valid_bit_count(bit_count);
    builder.register_npo(RangeCheckCircuitPlugin { bit_count });
}

pub fn range_check_expr<F>(builder: &mut CircuitBuilder<F>, value: ExprId, bit_count: usize)
where
    F: Field + PrimeField64 + PrimeCharacteristicRing + Send + Sync + 'static,
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
    assert!((1..=32).contains(&bit_count));
}

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
    F: Field + PrimeField64 + PrimeCharacteristicRing + Send + Sync + 'static,
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
        let raw = value.as_canonical_u64();
        let limit = 1u64 << self.bit_count;
        if raw >= limit {
            return Err(CircuitError::InvalidPreprocessing {
                reason: "range check witness is out of range",
            });
        }

        let bits = (0..self.bit_count)
            .map(|bit_index| F::from_u64((raw >> bit_index) & 1))
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
    for (op_type, state) in op_states {
        if parse_range_check_bit_count(op_type).is_none() {
            continue;
        }
        let Some(state) = state.downcast_ref::<RangeCheckExecutionState<F>>() else {
            continue;
        };
        if state.rows.is_empty() {
            continue;
        }
        return Ok(Some(Box::new(RangeCheckTrace {
            op_type: op_type.clone(),
            bit_count: state.bit_count,
            rows: state.rows.clone(),
        })));
    }
    Ok(None)
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
}
