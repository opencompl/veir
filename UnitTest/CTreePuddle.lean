import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity

open Veir Veir.Puddle

namespace Veir.Puddle.CTree

/-- Integer freeze preserves concrete inputs and replaces poison by any concrete bitvector. -/
@[simp, grind =]
theorem CanInterpretTo.freeze_int {ty : IntegerType} (property : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int ty.bitwidth) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .freeze) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth value] results ↔
    ∃ v : BitVec ty.bitwidth, (value = .poison ∨ value = .val v) ∧
      results = .ok #[.int ty.bitwidth (.val v)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, bind_pure_comp, Functor.map]
  cases value <;> cases results <;> simp [PureOrErr.CanInterpretTo.bind_iff]

/-- Integer addition has a single outcome, including poison from overflow flags. -/
@[simp, grind =]
theorem CanInterpretTo.add_int {ty : IntegerType} (property : propertiesOf (OpCode.llvm .add))
    (x y : Data.LLVM.Int ty.bitwidth) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .add) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
    results = .ok #[.int ty.bitwidth (Data.LLVM.Int.add x y property.nsw property.nuw)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

/-- Integer freeze preserves a concrete value and chooses a bitvector for poison. -/
theorem freeze_eq {bw : Nat} (ty : IntegerType) (freezeProp : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int bw) (memory : MemoryState) :
    Llvm.freeze.interpretOpCTree freezeProp #[TypeAttr.of IntegerType ty]
      #[RuntimeValue.int bw value] #[] memory = (match value with
      | .val bits => pure (#[RuntimeValue.int bw (.val bits)], memory, none)
      | .poison => do
        let bits ← CTree.CTree.choose (SubC := FreezeC) (FreezeCIn.mk bw)
        pure (#[RuntimeValue.int bw (.val bits)], memory, none)) := by
  cases value <;> rfl

/-- Peel one target freeze, keeping the source and continuation folded. -/
@[simp, grind =]
theorem Tree.Refines.target_bind_freeze {α : Type}
    {relation : α → (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Prop}
    {ty : IntegerType} (freezeProp : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int ty.bitwidth) (memory : MemoryState)
    (source : Tree α)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
      Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
    : Tree.Refines relation source
      (CTree.bind
        (Llvm.freeze.interpretOpCTree freezeProp #[TypeAttr.of IntegerType ty]
          #[RuntimeValue.int ty.bitwidth value] #[] memory)
        next) ↔
    ∀ bits : BitVec ty.bitwidth, (value = .poison ∨ value = .val bits) →
      Tree.Refines relation source
        (next (#[RuntimeValue.int ty.bitwidth (.val bits)], memory, none)) := by
  cases value <;>
    simp [freeze_eq, Tree.Refines, CTree.CTree.choose_def, CTree.CTree.tau_def, Bind.bind]

/-- Peel an integer add in the target, preserving poison and the overflow flags.
The source and continuation remain folded. -/
@[simp, grind =]
theorem Tree.Refines.target_bind_add {α β : Type} {relation : α → β → Prop}
    {ty : IntegerType} (addProp : propertiesOf (OpCode.llvm .add))
    (x y : Data.LLVM.Int ty.bitwidth) (memory : MemoryState) (source : Tree α)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Tree β) :
    Tree.Refines relation source
      (CTree.bind
        (Llvm.add.interpretOpCTree addProp #[TypeAttr.of IntegerType ty]
          #[RuntimeValue.int ty.bitwidth x, RuntimeValue.int ty.bitwidth y] #[] memory)
        next) ↔
    Tree.Refines relation source
      (next (#[RuntimeValue.int ty.bitwidth (Data.LLVM.Int.add x y addProp.nsw addProp.nuw)],
        memory, none)) := by
  simp [Llvm.interpretOpCTree, Tree.refines_monadLift_bind_target, Llvm.interpretOp']

/-- Peel a target load, checking alignment before reading memory. UB and failure
stop the target without running its continuation. -/
@[simp, grind =]
theorem Tree.Refines.target_bind_load {α β : Type} {relation : α → β → Prop}
    (loadProp : propertiesOf (OpCode.llvm .load)) (ty : TypeAttr)
    (ptr : Data.LLVM.Ptr) (memory : MemoryState) (source : Tree α)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Tree β)
    (layout : DataLayout := .riscv64) :
    Tree.Refines relation source
      (CTree.bind
        (Llvm.load.interpretOpCTree loadProp #[ty] #[RuntimeValue.addr ptr] #[] memory layout)
        next) ↔
    match ptr with
    | .poison => Tree.Refines relation source ub
    | .val addr =>
      (do
        addr.checkAlignment (Llvm.accessAlignment layout loadProp.alignment ty.val)
        memory.llvmLoad addr ty).foldProp
        (fun value => Tree.Refines relation source (next (#[value], memory, none)))
        (fun error : Interp β => Tree.Refines relation source (monadLift error)) := by
  cases ptr with
  | poison => simp [Llvm.interpretOpCTree, Llvm.interpretOp', monadLift, MonadLift.monadLift]
  | val addr =>
    cases halign : addr.checkAlignment (Llvm.accessAlignment layout loadProp.alignment ty.val) <;>
      cases hload : memory.llvmLoad addr ty <;>
      simp [Llvm.interpretOpCTree, Llvm.interpretOp', halign, hload,
        Interp.foldProp, monadLift, MonadLift.monadLift, Bind.bind]

/-- Peel a source load against any target. Successful reads preserve memory;
poison pointers, alignment errors, and memory errors retain their semantics. -/
@[simp, grind =]
theorem Tree.Refines.source_load {β : Type}
    {relation : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → β → Prop}
    (loadProp : propertiesOf (OpCode.llvm .load)) (ty : TypeAttr)
    (ptr : Data.LLVM.Ptr) (memory : MemoryState) (target : Tree β)
    (layout : DataLayout := .riscv64) :
    Tree.Refines relation
      (Llvm.load.interpretOpCTree loadProp #[ty] #[RuntimeValue.addr ptr] #[] memory layout)
      target ↔
    match ptr with
    | .poison => Tree.Refines relation ub target
    | .val addr =>
      (do
        addr.checkAlignment (Llvm.accessAlignment layout loadProp.alignment ty.val)
        memory.llvmLoad addr ty).foldProp
        (fun value => Tree.Refines relation (pure (#[value], memory, none)) target)
        (fun error : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction) =>
          Tree.Refines relation (monadLift error) target) := by
  cases ptr with
  | poison => rfl
  | val addr =>
    cases halign : addr.checkAlignment (Llvm.accessAlignment layout loadProp.alignment ty.val) <;>
      cases hload : memory.llvmLoad addr ty <;>
      simp [Llvm.interpretOpCTree, Llvm.interpretOp', halign, hload,
        Interp.foldProp, monadLift, MonadLift.monadLift, Bind.bind]

/-- Once the target has returned, source freeze peeling is an equivalence.
Peel target choices first so the source witness can depend on them. -/
theorem Tree.Refines.source_bind_freeze {ty : IntegerType} (freezeProp : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int ty.bitwidth) (memory : MemoryState)
    (targetResult : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
      Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
    Tree.Refines OperationResult.isRefinedBy
      (CTree.bind
        (Llvm.freeze.interpretOpCTree freezeProp #[TypeAttr.of IntegerType ty]
          #[RuntimeValue.int ty.bitwidth value] #[] memory)
        next) (pure targetResult) ↔
    ∃ bits : BitVec ty.bitwidth, (value = .poison ∨ value = .val bits) ∧
      Tree.Refines OperationResult.isRefinedBy
        (next (#[RuntimeValue.int ty.bitwidth (.val bits)], memory, none))
        (pure targetResult) := by
  cases value <;>
    simp [freeze_eq, Tree.Refines, CTree.CTree.choose_def, CTree.CTree.tau_def, Bind.bind]

/-- Peel the source root against a returned target, choosing one permitted result. -/
theorem Tree.Refines.source_freeze {ty : IntegerType} (freezeProp : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int ty.bitwidth) (memory : MemoryState)
    (targetResult : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    Tree.Refines OperationResult.isRefinedBy
      (Llvm.freeze.interpretOpCTree freezeProp #[TypeAttr.of IntegerType ty]
        #[RuntimeValue.int ty.bitwidth value] #[] memory) (pure targetResult) ↔
    ∃ bits : BitVec ty.bitwidth, (value = .poison ∨ value = .val bits) ∧
      Tree.Refines OperationResult.isRefinedBy
        (pure (#[RuntimeValue.int ty.bitwidth (.val bits)], memory, none))
        (pure targetResult) := by
  have peeled := Tree.Refines.source_bind_freeze freezeProp value memory targetResult pure
  change (Tree.Refines _ (_ >>= pure) (pure targetResult) ↔ _) at peeled
  simpa only [bind_pure] using peeled

end Veir.Puddle.CTree

open Veir.Puddle.CTree

namespace CTreePuddleTest

/-- Recreating a nondeterministic operation must allow the source choice to depend on the target. -/
private def recreateFreeze : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let root ← MatchProg.root (.llvm .freeze) #[x] #[ty]
      return (ty, x, root.properties))
    (fun (ty, x, prop) => CreateProg.operation (.llvm .freeze) #[x] #[ty] prop)
    (fun result => result)

example : CTree.Pattern.Valid recreateFreeze := by
  unfold recreateFreeze
  provePuddleValid program sym =>
    simp only [RuntimeValue.Conforms.integerType, interpretOpCTree, forall_exists_index,
      forall_eq_apply_imp_iff, Tree.Refines.target_bind_freeze, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem!_pos, List.getElem_toArray,
      List.getElem_cons_zero, Tree.Refines.source_freeze, Tree.refines_pure, forall_const]
    grind

/-- A created terminator is rejected by the static support check. -/
private def createReturnBeforeFreeze : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let root ← MatchProg.root (.llvm .freeze) #[x] #[ty]
      return (ty, x, root.properties))
    (fun (ty, x, prop) => do
      let returnProp ← CreateProg.property (.llvm .return) ()
      let _ ← CreateProg.operation (.llvm .return) #[] #[] returnProp
      CreateProg.operation (.llvm .freeze) #[x] #[ty] prop)
    (fun result => result)

example : ¬ CTree.Pattern.Supported createReturnBeforeFreeze := by
  unfold createReturnBeforeFreeze
  unfoldPuddleBuilder
  simp [CTree.Pattern.Supported, get_effects, is_terminator]

/--
Rewrite `freeze (add x y)` to `add (freeze x) (freeze y)` for wrapping addition.
Match two operations and create three, with independent choices for the two new freezes.
-/
private def freezeAdd : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let add ← MatchProg.operation (.llvm .add) #[x, y] #[ty]
        (fun properties => !properties.nsw && !properties.nuw)
      let root ← MatchProg.root (.llvm .freeze) #[add.res[0]!] #[ty]
      return (ty, x, y, add.properties, root.properties))
    (fun (ty, x, y, addProp, freezeProp) => do
      let fx ← CreateProg.operation (.llvm .freeze) #[x] #[ty] freezeProp
      let fy ← CreateProg.operation (.llvm .freeze) #[y] #[ty] freezeProp
      CreateProg.operation (.llvm .add) #[fx.res[0]!, fy.res[0]!] #[ty] addProp)
    (fun result => result)

theorem freezeAdd_valid : CTree.Pattern.Valid freezeAdd := by
  unfold freezeAdd
  provePuddleValid program sym =>
    puddleNoAssignments
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro ty x y addProp hnsw hnuw sum hsum freezeProp memory
    simp only [CTree.CanInterpretTo.add_int, Interp.ok.injEq, Array.mk.injEq,
      List.cons.injEq, and_true] at hsum
    subst sum
    simp only [CTree.interpretOpCTree, hnsw, hnuw, Tree.Refines.target_bind_freeze, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem!_pos, List.getElem_toArray,
      List.getElem_cons_zero, Tree.Refines.target_bind_add, Tree.Refines.source_freeze, Tree.refines_pure,
      OperationResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
      RuntimeValue.arrayIsRefinedBy_refl, and_true, ControlFlowAction.optionIsRefinedBy_refl,
      and_self]
    intro xVal hx yVal hy
    exists xVal + yVal
    simp [Data.LLVM.Int.add, Id.run]
    grind

end CTreePuddleTest

namespace CTreeStatefulPuddleTest

private def recreateLoad : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
      let ptr ← MatchProg.value ptrTy
      let root ← MatchProg.root (.llvm .load) #[ptr] #[ty]
      return (ty, ptr, root.properties))
    (fun (ty, ptr, prop) => CreateProg.operation (.llvm .load) #[ptr] #[ty] prop)
    (fun result => result)

-- Memory effects are allowed on both sides of a rewrite.
example : CTree.Pattern.Supported recreateLoad := by
  unfold recreateLoad
  unfoldPuddleBuilder
  simp [CTree.Pattern.Supported, get_effects, is_terminator]

example : CTree.Pattern.Valid recreateLoad := by
  unfold recreateLoad
  provePuddleValid
  simp only [RuntimeValue.Conforms.llvmPointerType, forall_exists_index, forall_eq_apply_imp_iff,
    interpretOpCTree, forall_const]
  rintro ty (ptr | _) prop memory
  · simp only [Tree.Refines.target_bind_load, Tree.Refines.source_load]
    cases halign : ptr.checkAlignment
      (Llvm.accessAlignment DataLayout.riscv64 prop.alignment (Attribute.of IntegerType ty)) <;>
      cases hload : memory.llvmLoad ptr (TypeAttr.of IntegerType ty) <;>
      simp [halign, Interp.foldProp, monadLift, MonadLift.monadLift, Bind.bind, Tree.refines_refl]
  · simp [Tree.refines_refl]

end CTreeStatefulPuddleTest

namespace CTreeMatchPurityTest

-- An effectful non-root match is still forbidden, even when the root is also effectful.
private def matchTwoLoads : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
      let ptr ← MatchProg.value ptrTy
      let _ ← MatchProg.operation (.llvm .load) #[ptr] #[ty]
      let root ← MatchProg.root (.llvm .load) #[ptr] #[ty]
      return (ty, ptr, root.properties))
    (fun (ty, ptr, prop) => CreateProg.operation (.llvm .load) #[ptr] #[ty] prop)
    (fun result => result)

example : ¬ CTree.Pattern.Supported matchTwoLoads := by
  unfold matchTwoLoads
  unfoldPuddleBuilder
  simp [CTree.Pattern.Supported, get_effects, is_terminator]

  exact ⟨default, by decide⟩

end CTreeMatchPurityTest
