import Veir.IR
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.LinkedList
import Veir.Rewriter.BasicDefs
import Veir.Rewriter.GetSetBasic

namespace Veir

set_option warn.sorry false in
@[irreducible]
def Rewriter.createOp (ctx: IRContext) (opType: OpCode)
    (resultTypes: Array TypeAttr) (operands: Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions: Array RegionPtr) (properties: propertiesOf opType)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds ctx)
    (hblockOperands : ∀ oper, oper ∈ blockOperands → oper.InBounds ctx)
    (hregions : ∀ reg, reg ∈ regions → reg.InBounds ctx)
    (hins : insertionPoint.maybe InsertPoint.InBounds ctx)
    (hx : ctx.FieldsInBounds) : Option (IRContext × OperationPtr) :=
  rlet hnew : (ctx, newOpPtr) ← Rewriter.createEmptyOp ctx opType properties
  have hib : newOpPtr.InBounds ctx := by grind
  have : (newOpPtr.get ctx (by grind)).results = #[] := by
    grind [createEmptyOp, OperationPtr.allocEmpty, Operation.empty]
  have newOpPtrZeroRes: 0 = newOpPtr.getNumResults ctx (by grind) := by grind [OperationPtr.getNumResults]
  let ctx := Rewriter.initOpResults ctx newOpPtr resultTypes 0 hib newOpPtrZeroRes
  let ctx := newOpPtr.setProperties ctx properties (by grind) (by sorry)
  let ctx := Rewriter.initOpRegions ctx newOpPtr regions
  let ctx := Rewriter.initOpOperands ctx newOpPtr (by grind) operands (by grind) (by grind)
  let ctx := Rewriter.initBlockOperands ctx newOpPtr blockOperands (hoperands := by grind (ematch := 10))
  match _ : insertionPoint with
  | some insertionPoint =>
    rlet ctx ← Rewriter.insertOp? ctx newOpPtr insertionPoint (by grind) (by cases insertionPoint <;> grind (ematch := 10) [Option.maybe]) (by grind) in
    some (ctx, newOpPtr)
  | none =>
    (ctx, newOpPtr)

@[grind .]
theorem Rewriter.createOp_inBounds_mono (ptr : GenericPtr)
    (heq : createOp ctx opType numResults operands blockOperands regions props ip h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp)) :
    ptr.InBounds ctx → ptr.InBounds newCtx := by
  simp only [createOp] at heq
  split at heq; grind
  split at heq
  · split at heq; grind only
    intros hptr
    rename_i h
    simp at heq
    have ⟨_, _⟩ := heq
    subst newOp
    subst newCtx
    rw [←Rewriter.insertOp?_inBounds_mono ptr h]
    grind
  · grind (ematch := 10)

@[grind .]
theorem Rewriter.createOp_fieldsInBounds
    (heq : createOp ctx opType numResults operands blockOperands numRegions props ip h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp)) :
    ctx.FieldsInBounds → newCtx.FieldsInBounds := by
  simp only [createOp] at heq
  split at heq; grind
  split at heq
  · split at heq
    · grind
    · grind
  · grind

set_option warn.sorry false in
unseal Rewriter.createRegion in
@[irreducible]
def IRContext.create : Option (IRContext × OperationPtr) :=
  rlet (ctx, operation) ← Rewriter.createEmptyOp .empty .builtin_module ()
  rlet (ctx, region) ← Rewriter.createRegion ctx
  let ctx := Rewriter.initOpRegions ctx operation #[region]
  let moduleRegion := operation.getRegion! ctx 0
  rlet (ctx, block) ← Rewriter.createBlock ctx (some (.atEnd moduleRegion)) (by grind) (by sorry)
  return (ctx, ⟨0⟩)
