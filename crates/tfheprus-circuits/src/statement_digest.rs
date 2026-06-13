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
use p3_field::Field;

use crate::SELECTOR_DIGEST_WIDTH;

const STATEMENT_DIGEST_TYPE: &str = "tfheprus/statement_digest";

#[derive(Debug, Clone)]
pub struct StatementDigestCircuitRow<F> {
    pub input_wids: [WitnessId; SELECTOR_DIGEST_WIDTH],
    pub values: [F; SELECTOR_DIGEST_WIDTH],
}

#[derive(Debug, Default)]
pub struct StatementDigestExecutionState<F> {
    pub rows: Vec<StatementDigestCircuitRow<F>>,
}

#[derive(Debug, Clone)]
pub struct StatementDigestTrace<F> {
    pub rows: Vec<StatementDigestCircuitRow<F>>,
}

impl<F> StatementDigestTrace<F> {
    pub const fn total_rows(&self) -> usize {
        self.rows.len()
    }
}

impl<TraceF: Clone + Send + Sync + 'static, CF> NonPrimitiveTrace<CF>
    for StatementDigestTrace<TraceF>
{
    fn op_type(&self) -> NpoTypeId {
        statement_digest_type_id()
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
struct StatementDigestCircuitPlugin;

impl Debug for StatementDigestCircuitPlugin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("StatementDigestCircuitPlugin")
    }
}

impl<F> NpoCircuitPlugin<F> for StatementDigestCircuitPlugin
where
    F: Field + Send + Sync + 'static,
{
    fn type_id(&self) -> NpoTypeId {
        statement_digest_type_id()
    }

    fn lower(
        &self,
        data: &NonPrimitiveOperationData<F>,
        output_exprs: &[(u32, ExprId)],
        ctx: &mut NpoLoweringContext<'_, F>,
    ) -> Result<Op<F>, CircuitBuilderError> {
        if data.input_exprs.len() != 1 || data.input_exprs[0].len() != SELECTOR_DIGEST_WIDTH {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "StatementDigest",
                expected: "one digest input vector".to_string(),
                got: data.input_exprs.len(),
            });
        }
        if !output_exprs.is_empty() {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "StatementDigest",
                expected: "no outputs".to_string(),
                got: output_exprs.len(),
            });
        }

        let input_wids = data.input_exprs[0]
            .iter()
            .map(|&expr| ctx.resolve_witness_id(expr, "StatementDigest input"))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Op::NonPrimitiveOpWithExecutor {
            inputs: vec![input_wids],
            outputs: Vec::new(),
            executor: Box::new(StatementDigestExecutor::<F>::new()),
            op_id: data.op_id,
        })
    }

    fn trace_generator(&self) -> TraceGeneratorFn<F> {
        generate_statement_digest_trace::<F>
    }

    fn config(&self) -> NpoConfig {
        NpoConfig::new(0)
    }
}

pub fn register_statement_digest_npo<F>(builder: &mut CircuitBuilder<F>)
where
    F: Field + Send + Sync + 'static,
{
    builder.register_npo(StatementDigestCircuitPlugin);
}

pub fn bind_statement_digest_exprs<F>(
    builder: &mut CircuitBuilder<F>,
    digest: &[ExprId; SELECTOR_DIGEST_WIDTH],
) where
    F: Field + Send + Sync + 'static,
{
    builder.push_non_primitive_op_with_outputs(
        statement_digest_type_id(),
        vec![digest.to_vec()],
        Vec::new(),
        None,
        "statement_digest",
    );
}

pub fn statement_digest_type_id() -> NpoTypeId {
    NpoTypeId::new(STATEMENT_DIGEST_TYPE)
}

#[derive(Clone)]
struct StatementDigestExecutor<F> {
    op_type: NpoTypeId,
    _phantom: core::marker::PhantomData<F>,
}

impl<F> StatementDigestExecutor<F> {
    fn new() -> Self {
        Self {
            op_type: statement_digest_type_id(),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<F> Debug for StatementDigestExecutor<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StatementDigestExecutor")
            .field("op_type", &self.op_type)
            .finish()
    }
}

impl<F> NonPrimitiveExecutor<F> for StatementDigestExecutor<F>
where
    F: Field + Send + Sync + 'static,
{
    fn execute(
        &self,
        inputs: &[Vec<WitnessId>],
        outputs: &[Vec<WitnessId>],
        ctx: &mut ExecutionContext<'_, F>,
    ) -> Result<(), CircuitError> {
        if inputs.len() != 1 || inputs[0].len() != SELECTOR_DIGEST_WIDTH {
            return Err(CircuitError::NonPrimitiveOpLayoutMismatch {
                op: self.op_type.clone(),
                expected: "one digest input vector".to_string(),
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

        let input_wids: [WitnessId; SELECTOR_DIGEST_WIDTH] =
            inputs[0].clone().try_into().map_err(|_| {
                CircuitError::NonPrimitiveOpLayoutMismatch {
                    op: self.op_type.clone(),
                    expected: "four digest witnesses".to_string(),
                    got: inputs[0].len(),
                }
            })?;
        let values: [F; SELECTOR_DIGEST_WIDTH] = input_wids
            .iter()
            .map(|&wid| ctx.get_witness(wid))
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .map_err(|_| CircuitError::NonPrimitiveOpLayoutMismatch {
                op: self.op_type.clone(),
                expected: "four digest witness values".to_string(),
                got: input_wids.len(),
            })?;

        let state = ctx.get_op_state_mut::<StatementDigestExecutionState<F>>(&self.op_type);
        state
            .rows
            .push(StatementDigestCircuitRow { input_wids, values });
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
        if inputs.len() != 1 || inputs[0].len() != SELECTOR_DIGEST_WIDTH {
            return Err(CircuitError::NonPrimitiveOpLayoutMismatch {
                op: self.op_type.clone(),
                expected: "one digest input vector".to_string(),
                got: inputs.len(),
            });
        }
        for wid in &inputs[0] {
            preprocessed.register_non_primitive_witness_reads(&self.op_type, &[*wid])?;
            preprocessed
                .register_non_primitive_preprocessed_no_read(&self.op_type, &[F::ZERO - F::ONE]);
        }
        Ok(())
    }

    fn boxed(&self) -> Box<dyn NonPrimitiveExecutor<F>> {
        Box::new(self.clone())
    }
}

pub fn generate_statement_digest_trace<F>(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<F>>>, CircuitError>
where
    F: Field + Clone + Send + Sync + 'static,
{
    let op_type = statement_digest_type_id();
    let Some(state) = op_states.get(&op_type) else {
        return Ok(None);
    };
    let Some(state) = state.downcast_ref::<StatementDigestExecutionState<F>>() else {
        return Ok(None);
    };
    if state.rows.is_empty() {
        return Ok(None);
    }
    Ok(Some(Box::new(StatementDigestTrace {
        rows: state.rows.clone(),
    })))
}
