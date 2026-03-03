module

public import Veir.Analysis
public import Veir.IR.Basic

public section

namespace Veir.Transforms.SCCP

-- TODO: Implement these eventually

-- Replace the given value with a constant if the corresponding lattice
-- represents a constant. Returns success if the value was replaced, failure
-- otherwise.
--
-- def replaceWithConstant
--     (top : OperationPtr)
--     (value : ValuePtr)
--     (dfCtx : DataFlowContext)
--     (irCtx : IRContext OpCode) : IRContext OpCode := by
--   sorry

-- Rewrite the given regions using the computing analysis. This replaces the
-- uses of all values that have been computed to be constant, and erases as
-- many newly dead operations.
--
-- def rewrite
--     (top : OperationPtr)
--     (dfCtx : DataFlowContext)
--     (irCtx : IRContext OpCode) : IRContext OpCode := by
--   sorry

-- Run sparse conditional constant propagation on the given top-level operation
-- and rewrite the IR using the resulting dataflow facts.
--
-- def runOnOperation
--     (top : OperationPtr)
--     (irCtx : IRContext OpCode) : IRContext OpCode := by
--   let dfCtx := fixpointSolve top #[SparseConstantPropagationAnalysis, DeadCodeAnalysis] irCtx
--   exact rewrite top dfCtx irCtx

end Veir.Transforms.SCCP
