module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Analysis.DataFlow.SparseAnalysis

public section

namespace Veir

namespace SparseConstantPropagation

instance : SparseFactSpec .sparseConstant AbstractConstant where
  payloadEq := rfl

def kind : AnalysisKind :=
  .sparseConstantPropagation

/--
Fold a binary operation on known constants when bitwidths agree.
Returns `none` if widths mismatch or folding yields no value.
-/
def foldKnownBinary?
    (lhs rhs : ConcreteConstant)
    (f : {w : Nat} -> Data.LLVM.Int w -> Data.LLVM.Int w -> Option (Data.LLVM.Int w))
    : Option ConcreteConstant :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsValue := Data.LLVM.Int.cast rhs.value (Eq.symm h)
    f lhs.value rhsValue |> .map ({ bitwidth := lhs.bitwidth, value := · })
  else
    none

/--
Try to fold a binary op from operand lattice elements.
Only folds when there are exactly two operands and both are known constants.
-/
def foldBinaryOp?
    (operandLatticeElements : Array AbstractConstant)
    (f : {w : Nat} -> Data.LLVM.Int w -> Data.LLVM.Int w -> Option (Data.LLVM.Int w))
    : Option AbstractConstant :=
  if operandLatticeElements.size ≠ 2 then
    none
  else
    match operandLatticeElements[0]?, operandLatticeElements[1]? with
    | some (AbstractConstant.constant lhs), some (AbstractConstant.constant rhs) =>
      foldKnownBinary? lhs rhs f |> .map (.constant ·)
    | _, _ =>
      none

/-- Produce a folded constant when possible, otherwise conservatively yield `⊤`. -/
def foldedOrUnknown
    (numResults : Nat)
    (folded : Option AbstractConstant) : Array (Option AbstractConstant) :=
  match folded with
  | some constant =>
    #[some constant]
  | none =>
    Array.replicate numResults (some ⊤)

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

  -- TODO: Mirror MLIR's generic `op->fold` path once Veir has an operation
  -- folder and fold-result representation. For now we manually handle the
  -- arithmetic ops.
  else
    match (op.get! irCtx.raw).opType with
    | .arith .constant =>
      if numResults > 0 then
        let intAttr := (op.getProperties! irCtx.raw Arith.constant).value
        #[some (.constant ⟨intAttr.type.bitwidth,
            Data.LLVM.Int.constant intAttr.type.bitwidth intAttr.value⟩)]
      else
        #[]
    | .arith .addi =>
      let flags := op.getProperties! irCtx.raw Arith.addi
      foldedOrUnknown numResults <| foldBinaryOp? operandLatticeElements (fun lhs rhs =>
        match Data.LLVM.Int.add lhs rhs flags.attr.nsw flags.attr.nuw with
        | .val v => some (.val v)
        | .poison => none)
    | .arith .muli =>
      let flags := op.getProperties! irCtx.raw Arith.muli
      foldedOrUnknown numResults <| foldBinaryOp? operandLatticeElements (fun lhs rhs =>
        match Data.LLVM.Int.mul lhs rhs flags.attr.nsw flags.attr.nuw with
        | .val v => some (.val v)
        | .poison => none)
    | .arith .andi =>
      foldedOrUnknown numResults <| foldBinaryOp? operandLatticeElements (fun lhs rhs =>
        match lhs, rhs with
        | .val lhs', .val rhs' => some (.val (BitVec.and lhs' rhs'))
        | _, _ => none)
    | .arith .subi =>
      let flags := op.getProperties! irCtx.raw Arith.subi
      foldedOrUnknown numResults <| foldBinaryOp? operandLatticeElements (fun lhs rhs =>
        match Data.LLVM.Int.sub lhs rhs flags.attr.nsw flags.attr.nuw with
        | .val v => some (.val v)
        | .poison => none)
    | _ =>
      Array.replicate numResults (some ⊤)

end SparseConstantPropagation

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.kind
    SparseConstantPropagation.transfer

end Veir
