import Mlir.Core.Basic
import Mlir.Rewriter

namespace Mlir

@[irreducible]
def Builder.createBlock (ctx: IRContext) (insertionPoint: Option BlockInsertPoint)
    (hctx : ctx.FieldsInBounds) (hip : insertionPoint.maybe BlockInsertPoint.InBounds ctx)
    : Option (IRContext × BlockPtr) :=
  rlet (ctx, newBlockPtr) ← BlockPtr.allocEmpty ctx
  match h : insertionPoint with
  | some insertionPoint => do
    let ctx ← Rewriter.insertBlock? ctx newBlockPtr insertionPoint (by grind [Option.maybe, cases BlockInsertPoint])
    (ctx, newBlockPtr)
  | none =>
    (ctx, newBlockPtr)

@[irreducible, grind]
def Builder.createRegion (ctx: IRContext) : Option (IRContext × RegionPtr) :=
  RegionPtr.allocEmpty ctx

@[irreducible]
def Builder.initOpRegions (ctx: IRContext) (opPtr: OperationPtr) (numRegions: Nat)
    (hop : opPtr.InBounds ctx) : Option IRContext :=
  match numRegions with
  | 0 => some ctx
  | Nat.succ n => do
    rlet (ctx, regionPtr) ← Builder.createRegion ctx
    let oldRegion := regionPtr.get ctx (by grind)
    let ctx := opPtr.setRegions ctx ((opPtr.get ctx).regions.push regionPtr)
    Builder.initOpRegions ctx opPtr n (by grind)

@[grind .]
theorem Builder.initOpRegions_fieldsInBounds
    (hx : ctx.FieldsInBounds)
    (heq : initOpRegions ctx opPtr numRegions h₁ = some ctx') :
    ctx'.FieldsInBounds := by
  induction numRegions generalizing ctx <;> sorry --grind [initOpRegions]

@[grind .]
theorem Builder.initOpRegions_inBounds_mono (ptr : GenericPtr)
    (heq : initOpRegions ctx opPtr numRegions h₁ = some ctx') :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  induction numRegions generalizing ctx <;>
    grind [initOpRegions, Option.unattach_eq_some_iff]

@[irreducible]
def Builder.initOpResults (ctx: IRContext) (opPtr: OperationPtr) (numResults: Nat) (index: Nat := 0) (hop : opPtr.InBounds ctx)
    (hidx : index = opPtr.getNumResults ctx) : IRContext :=
  match numResults with
  | 0 => ctx
  | Nat.succ n =>
    let result: OpResult := { type := (), firstUse := none, index := index, owner := opPtr }
    let ctx := opPtr.pushResult ctx result
    have : opPtr.InBounds ctx := by grind
    have : result.FieldsInBounds ctx := by
      -- TODO(later): write the right lemma somewhere.
      constructor <;> grind [OperationPtr.pushResult, OperationPtr.setResults, OperationPtr.set, OperationPtr.get]
    Builder.initOpResults ctx opPtr n (index + 1) (by grind) (by grind)

@[grind .]
theorem Builder.initOpResults_fieldsInBounds (hx : ctx.FieldsInBounds) :
    (initOpResults ctx opPtr numResults index h₁ h₂).FieldsInBounds := by
  induction numResults generalizing ctx index
  · grind [initOpResults]
  case succ numResults ih =>
    simp [initOpResults]
    apply ih
    apply OperationPtr.pushResult_fieldsInBounds
    · constructor <;> grind [OperationPtr.pushResult, OperationPtr.setResults, OperationPtr.set, OperationPtr.get]
    · grind

@[grind .]
theorem Builder.initOpResults_inBounds_mono (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (initOpResults ctx opPtr numResults index h₁ h₂) := by
  induction numResults generalizing ctx index <;> grind [initOpResults]

@[irreducible]
protected def Builder.pushOperand (ctx : IRContext) (opPtr : OperationPtr) (valuePtr : ValuePtr)
    (opPtrInBounds : opPtr.InBounds ctx := by grind) (valueInBounds : valuePtr.InBounds ctx := by grind) (hctx : ctx.FieldsInBounds) : IRContext :=
  let op := (opPtr.get ctx (by grind))
  let index := opPtr.getNumOperands ctx (by grind)
  let operand := { value := valuePtr, owner := opPtr, back := OpOperandPtrPtr.valueFirstUse valuePtr, nextUse := none : OpOperand}
  have : operand.FieldsInBounds ctx := by constructor <;> grind [Option.maybe]
  let ctx := opPtr.pushOperand ctx operand (by grind)
  let ctx := (OpOperandPtr.mk opPtr index).insertIntoCurrent ctx (by grind) (by grind)
  ctx

@[grind .]
theorem Builder.pushOperand_inBounds (ptr : GenericPtr) :
    ptr.InBounds (Builder.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) ↔
    (ptr.InBounds ctx ∨
     ptr = .opOperand ⟨opPtr, (opPtr.getNumOperands ctx)⟩ ∨
     ptr = .opOperandPtr (.operandNextUse ⟨opPtr, (opPtr.getNumOperands ctx)⟩)) := by
  grind [Builder.pushOperand]

@[grind .]
theorem Builder.pushOperand_inBounds_mono (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (Builder.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) := by
  grind

@[grind .]
theorem Builder.pushOperand_fieldsInBounds :
    (Builder.pushOperand ctx opPtr valuePtr h₁ h₂ h₃).FieldsInBounds := by
  grind [Builder.pushOperand]

@[irreducible]
def Builder.initOpOperands (ctx: IRContext) (opPtr: OperationPtr) (opPtrInBounds : opPtr.InBounds ctx)
    (operands : Array ValuePtr) (hoperands : ∀ oper, oper ∈ operands → oper.InBounds ctx) (hctx : ctx.FieldsInBounds)
    (n : Nat := operands.size) (hn : 0 ≤ n ∧ n ≤ operands.size := by grind) : IRContext :=
  match h : n with
  | 0 => ctx
  | Nat.succ n' =>
    let index := operands.size - n
    let valuePtr := operands[index]'(by grind)
    let ctx := Builder.pushOperand ctx opPtr valuePtr (by grind) (by grind) (by grind)
    Builder.initOpOperands ctx opPtr (by grind) operands (by grind) (by grind) n' (by grind)

@[grind .]
theorem Builder.initOpOperands_fieldsInBounds :
    (initOpOperands ctx opPtr h₁ operands h₂ h₃ n hn).FieldsInBounds := by
  induction n generalizing ctx
  case zero => grind [initOpOperands]
  case succ n ih =>
    simp [initOpOperands]
    grind

@[grind .]
theorem Builder.initOpOperands_inBounds_mono (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (initOpOperands ctx opPtr h₁ operands h₂ h₃ n hn) := by
  induction n generalizing ctx
  case zero => grind [initOpOperands]
  case succ n ih =>
    simp [initOpOperands]
    grind

@[irreducible]
private def Builder.createEmptyOp (ctx : IRContext) (opType : Nat) : Option (IRContext × OperationPtr) :=
  OperationPtr.allocEmpty ctx opType

@[grind .]
theorem Builder.createEmptyOp_new_inBounds (h : createEmptyOp ctx opType = some (ctx', op)) :
    op.InBounds ctx' := by
  grind [createEmptyOp]

@[grind .]
theorem Builder.createEmptyOp_genericPtr_mono (ptr : GenericPtr) (heq : createEmptyOp ctx type = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .operation ptr') := by
  grind [createEmptyOp, OperationPtr.allocEmpty_genericPtr_iff']

@[grind .]
theorem Builder.createEmptyOp_fieldsInBounds (h : createEmptyOp ctx opType = some (ctx', op)) :
    ctx.FieldsInBounds → ctx'.FieldsInBounds := by
  grind [createEmptyOp]


@[irreducible]
def Builder.createOp (ctx: IRContext) (opType: Nat)
    (numResults: Nat) (operands: Array ValuePtr) (numRegions: Nat) (properties: UInt64)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds ctx)
    (hins : insertionPoint.maybe InsertPoint.InBounds ctx)
    (hx : ctx.FieldsInBounds) : Option (IRContext × OperationPtr) :=
  rlet (ctx, newOpPtr) ← Builder.createEmptyOp ctx opType
  have hib : newOpPtr.InBounds ctx := by grind
  have : (newOpPtr.get ctx (by grind)).results = #[] := by
    grind [createEmptyOp, OperationPtr.allocEmpty, Operation.empty]
  let ctx := Builder.initOpResults ctx  newOpPtr numResults 0 (by grind) (by grind [OperationPtr.getNumResults])
  let ctx := newOpPtr.setProperties ctx properties
  rlet ctx ← Builder.initOpRegions ctx newOpPtr numRegions (by grind)
  let ctx := Builder.initOpOperands ctx newOpPtr (by grind) operands (by grind) (by grind)
  match _ : insertionPoint with
  | some insertionPoint =>
    rlet ctx ← Rewriter.insertOp? ctx newOpPtr insertionPoint (by grind) (by cases insertionPoint <;> grind [Option.maybe]) (by grind) in
    some (ctx, newOpPtr)
  | none =>
    (ctx, newOpPtr)

abbrev ModuleTypeID := 0

unseal Builder.createRegion in
@[irreducible]
def IRContext.create : Option (IRContext × OperationPtr) :=
  let ctx : IRContext := {
    nextID := 0,
    operations := Std.HashMap.emptyWithCapacity,
    blocks := Std.HashMap.emptyWithCapacity,
    regions := Std.HashMap.emptyWithCapacity,
    topLevelOp := 0
  }
  -- Note: We inline part of the definition of `createOp` because the above
  -- `ctx` does not satisfy `ctx.FieldsInBounds` because `topLevelOp` is an
  -- invalid pointer.
  rlet (ctx, operation) ← Builder.createEmptyOp ctx ModuleTypeID
  have hib : operation.InBounds ctx := by grind
  have : ctx.topLevelOp = 0 := by
    grind [Builder.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set]
  have hops : ∀ (op : OperationPtr), op.InBounds ctx ↔ op = 0 := by
    grind [Builder.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, OperationPtr.InBounds]
  have : (operation.get ctx (by grind)).results = #[] := by
    grind [Builder.createEmptyOp, OperationPtr.allocEmpty, Operation.empty]
  have : ∀ (bl : BlockPtr), bl.InBounds ctx ↔ False := by
    grind [Builder.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, BlockPtr.InBounds]
  have : ∀ (r : RegionPtr), r.InBounds ctx ↔ False := by
    grind [Builder.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, RegionPtr.InBounds]
  have : ctx.nextID = 1 := by
    grind [Builder.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, RegionPtr.InBounds]
  have : operation.get ctx (by simp_all) = Operation.empty ModuleTypeID := by
    grind [Builder.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, RegionPtr.InBounds]
  rlet ctx ← Builder.initOpRegions ctx operation 1 (by grind)
  have : operation = 0 := by grind [Builder.createEmptyOp, OperationPtr.allocEmpty]
  have : ctx.topLevelOp = 0 := by
    simp_all [Builder.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Builder.createRegion]
    grind [RegionPtr.set, RegionPtr.allocEmpty]
  have hop₀ : ∀ (op : OperationPtr), op.InBounds ctx ↔ op = 0 := by
    simp_all [Builder.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Builder.createRegion]
    simp [OperationPtr.InBounds] at hops
    grind [Region.empty, RegionPtr.set, OperationPtr.InBounds]
  have : operation.get ctx (by simp_all) =
    { Operation.empty ModuleTypeID with regions := #[1] } := by
    simp_all [Builder.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Builder.createRegion]
    grind [Operation.empty, RegionPtr.set, RegionPtr.InBounds, RegionPtr.get, OperationPtr.get, RegionPtr.allocEmpty]
  have : ∀ (bl : BlockPtr), bl.InBounds ctx ↔ False := by
    simp_all [Builder.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Builder.createRegion]
    grind [Region.empty, RegionPtr.set, BlockPtr.InBounds]
  have : ∀ (r : RegionPtr), r.InBounds ctx ↔ r = 1 := by
    simp_all [Builder.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Builder.createRegion]
    grind [Region.empty, RegionPtr.set, RegionPtr.InBounds]
  have : (1 : RegionPtr).get ctx (by simp_all) = Region.empty := by
    simp_all [Builder.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Builder.createRegion]
    grind [Region.empty, RegionPtr.set, RegionPtr.InBounds, RegionPtr.get, RegionPtr.allocEmpty]
  have : ctx.FieldsInBounds := by
    constructor
    · grind [Operation.empty]
    · sorry -- grind [Operation.FieldsInBounds, Operation.empty]
    · grind
    · grind [Region.FieldsInBounds, Region.empty]
  let moduleRegion := (operation.get ctx (by grind)).regions[0]!
  rlet (ctx, block) ← Builder.createBlock ctx (some (BlockInsertPoint.AtEnd moduleRegion)) (by grind) (by grind [Option.maybe, BlockInsertPoint.InBounds])
  let ctx := { ctx with topLevelOp := operation }
  (ctx, 0)
