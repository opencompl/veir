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

private def abstractConstantOfRuntimeValue : RuntimeValue → AbstractConstant
  | .int bitwidth value => .constant ⟨bitwidth, value⟩
  | _ => ⊤

private def abstractConstantOfFoldResult
    (result : FoldResult) (operands : Array AbstractConstant) : AbstractConstant :=
  match result with
  | .useOperand index => operands[index]?.getD ⊤
  | .useConstant value => abstractConstantOfRuntimeValue value

/--
Sparse constant propagation transfer function.
- region operations conservatively force results to the unknown state,
- operands at `⊥` delay propagation,
- otherwise we try to fold and report any discovered constant facts.
-/
def transfer
    (op : OperationPtr)
    (operandLatticeElements : Array AbstractConstant)
    (irCtx : WfIRContext OpCode) : Array (Option AbstractConstant) :=
  let numResults := op.getNumResults! irCtx.raw

  -- Don't try to simulate the results of a region operation as we can't
  -- guarantee that folding will be out-of-place. We don't allow in-place
  -- folds as the desire here is for simulated execution, and not general
  -- folding.
  if op.getNumRegions! irCtx.raw ≠ 0 then
    Array.replicate numResults (some ⊤)

  -- Wait until every operand lattice has been initialized before trying to
  -- infer a result.
  else if operandLatticeElements.any (· = ⊥) then
    Array.replicate numResults none

  else
    let opType := op.getOpType! irCtx.raw
    if opType.isConstantLike then
      (op.getResults! irCtx.raw).map fun result =>
        some <| (result.constantValue irCtx.raw).map abstractConstantOfRuntimeValue |>.getD ⊤
    else
      let constantOperands := operandLatticeElements.map fun
        | .constant ⟨bitwidth, value⟩ => some (.int bitwidth value)
        | _ => none
      if opInBounds : op.InBounds irCtx.raw then
        match op.foldsTo irCtx opInBounds constantOperands with
        | some results =>
          results.map fun result => some (abstractConstantOfFoldResult result operandLatticeElements)
        | none =>
          Array.replicate numResults (some ⊤)
      else
        Array.replicate numResults (some ⊤)

end SparseConstantPropagation

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.kind
    SparseConstantPropagation.transfer

end Veir
