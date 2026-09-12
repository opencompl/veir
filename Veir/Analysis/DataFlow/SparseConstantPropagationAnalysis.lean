module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis
import Veir.Interfaces.FoldInterfaces

public section

namespace Veir

namespace SparseConstantPropagation

instance : SparseFactSpec .sparseConstant AbstractConstant where
  payloadEq := rfl

def kind : AnalysisKind :=
  .sparseConstantPropagation

/--
Sparse constant propagation transfer function.
- operations with regions conservatively force results to `⊤`,
- any operand at `⊥` leave results as `⊥` and delay propagation,
- otherwise we try to fold and return the result (if there isn't 
  a result from the fold, return `⊤`)
-/
def transfer
    (op : OperationPtr)
    (operandLatticeElements : Array AbstractConstant)
    (irCtx : WfIRContext OpCode) : Array AbstractConstant :=
  let numResults := op.getNumResults! irCtx.raw
  let opType := op.getOpType! irCtx.raw

  -- Don't try to simulate the results of an operation with regions as we
  -- can't guarantee that folding will be out-of-place. We don't allow
  -- in-place folds as the desire here is for simulated execution, and not
  -- general folding.
  if op.getNumRegions! irCtx.raw ≠ 0 then
    Array.replicate numResults ⊤

  -- Wait until every operand lattice has been initialized before trying to
  -- infer a result.
  else if operandLatticeElements.any (· = ⊥) then
    Array.replicate numResults ⊥
  
  -- Grab constant out of constant like operation
  else if opType.isConstantLike then
    (op.getResults! irCtx.raw).map fun result =>
      (result.constantValue irCtx.raw).map AbstractConstant.ofRuntimeValue |>.getD ⊤

  -- Attempt folding the lattice elements of the operands
  else if opInBounds : op.InBounds irCtx.raw then
    let constantOperands := operandLatticeElements.map fun
      | .constant ⟨bitwidth, value⟩ => some (.int bitwidth value)
      | _ => none
    match op.foldsTo irCtx opInBounds constantOperands with
    | some results =>
      results.map fun result => AbstractConstant.ofFoldDecision result operandLatticeElements
    | none =>
        Array.replicate numResults ⊤

  else
    Array.replicate numResults ⊤

end SparseConstantPropagation

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.kind
    SparseConstantPropagation.transfer

end Veir
