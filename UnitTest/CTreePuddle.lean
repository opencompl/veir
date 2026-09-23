import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import Veir.Meta.Tactic.PBVDecide

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
  simp only [CanInterpretTo, Veir.CTree.interpretOp', Llvm.interpretOpCTree, bind_pure_comp, Functor.map]
  cases value <;> cases results <;> simp [PureOrErr.CanInterpretTo.bind_iff]

/-- Integer addition has a single outcome, including poison from overflow flags. -/
@[simp, grind =]
theorem CanInterpretTo.add_int {ty : IntegerType} (property : propertiesOf (OpCode.llvm .add))
    (x y : Data.LLVM.Int ty.bitwidth) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .add) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
    results = .ok #[.int ty.bitwidth (Data.LLVM.Int.add x y property.nsw property.nuw)] := by
  simp only [CanInterpretTo, Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

/-- Integer freeze preserves a concrete value and chooses a bitvector for poison. -/
theorem freeze_eq {EIn : Type} {E : EIn → Type} [ErrorE -< E] [CTree.UBE -< E]
    {bw : Nat} (ty : IntegerType) (freezeProp : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int bw) (memory : MemoryState) :
    Llvm.freeze.interpretOpCTree (E := E) freezeProp #[TypeAttr.of IntegerType ty]
      #[RuntimeValue.int bw value] #[] memory = (match value with
      | .val bits => pure (#[RuntimeValue.int bw (.val bits)], memory, none)
      | .poison => do
        let bits ← CTree.CTree.choose (SubC := FreezeC) (FreezeCIn.mk bw)
        pure (#[RuntimeValue.int bw (.val bits)], memory, none)) := by
  cases value <;> rfl

/-- Peel one target freeze, keeping the source and continuation folded. -/
@[simp, grind =]
theorem Tree.sim_target_bind_freeze {α : Type}
    {relation : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → α → Prop}
    {ty : IntegerType} (freezeProp : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int ty.bitwidth) (memory : MemoryState)
    (source : Tree α)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
      Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
    : CTree.Sim relation
      (CTree.bind
        (Llvm.freeze.interpretOpCTree freezeProp #[TypeAttr.of IntegerType ty]
          #[RuntimeValue.int ty.bitwidth value] #[] memory)
        next) source ↔
    ∀ bits : BitVec ty.bitwidth, (value = .poison ∨ value = .val bits) →
      CTree.Sim relation
        (next (#[RuntimeValue.int ty.bitwidth (.val bits)], memory, none)) source := by
  cases value <;>
    simp [freeze_eq, CTree.CTree.choose_def, CTree.CTree.tau_def, Bind.bind]

/-- Peel an integer add in the target, preserving poison and the overflow flags.
The source and continuation remain folded. -/
@[simp, grind =]
theorem Tree.sim_target_bind_add {α β : Type} {relation : β → α → Prop}
    {ty : IntegerType} (addProp : propertiesOf (OpCode.llvm .add))
    (x y : Data.LLVM.Int ty.bitwidth) (memory : MemoryState) (source : Tree α)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Tree β) :
    CTree.Sim relation
      (CTree.bind
        (Llvm.add.interpretOpCTree addProp #[TypeAttr.of IntegerType ty]
          #[RuntimeValue.int ty.bitwidth x, RuntimeValue.int ty.bitwidth y] #[] memory)
        next) source ↔
    CTree.Sim relation
      (next (#[RuntimeValue.int ty.bitwidth (Data.LLVM.Int.add x y addProp.nsw addProp.nuw)],
        memory, none)) source := by
  simp [Llvm.interpretOpCTree, sim_monadLift_bind_left, Llvm.interpretOp']

/-- Peel a target load, checking alignment before reading memory. UB and failure
stop the target without running its continuation. -/
@[simp, grind =]
theorem Tree.sim_target_bind_load {α β : Type} {relation : β → α → Prop}
    (loadProp : propertiesOf (OpCode.llvm .load)) (ty : TypeAttr)
    (ptr : Data.LLVM.Ptr) (memory : MemoryState) (source : Tree α)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Tree β)
    (layout : DataLayout := .riscv64) :
    CTree.Sim relation
      (CTree.bind
        (Llvm.load.interpretOpCTree loadProp #[ty] #[RuntimeValue.addr ptr] #[] memory layout)
        next) source ↔
    match ptr with
    | .poison => CTree.Sim relation (ub : Tree _) source
    | .val addr =>
      match (do
        addr.checkAlignment (Llvm.accessAlignment layout loadProp.alignment ty.val)
        memory.llvmLoad addr ty) with
      | .ok value => CTree.Sim relation (next (#[value], memory, none)) source
      | .ub _ => CTree.Sim relation (ub : Tree _) source
      | .fail _ => CTree.Sim relation (fail : Tree _) source := by
  cases ptr with
  | poison => simp [Llvm.interpretOpCTree, Llvm.interpretOp', monadLift, MonadLift.monadLift]
  | val addr =>
    cases halign : addr.checkAlignment (Llvm.accessAlignment layout loadProp.alignment ty.val) <;>
      cases hload : memory.llvmLoad addr ty <;>
      simp [Llvm.interpretOpCTree, Llvm.interpretOp', halign, hload,
        monadLift, MonadLift.monadLift, Bind.bind]

/-- Peel a source load against any target. Successful reads preserve memory;
poison pointers, alignment errors, and memory errors retain their semantics. -/
@[simp, grind =]
theorem Tree.sim_source_load {β : Type}
    {relation : β → (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Prop}
    (loadProp : propertiesOf (OpCode.llvm .load)) (ty : TypeAttr)
    (ptr : Data.LLVM.Ptr) (memory : MemoryState) (target : Tree β)
    (layout : DataLayout := .riscv64) :
    CTree.Sim relation target
      (Llvm.load.interpretOpCTree loadProp #[ty] #[RuntimeValue.addr ptr] #[] memory layout) ↔
    match ptr with
    | .poison => CTree.Sim relation target (ub : Tree _)
    | .val addr =>
      match (do
        addr.checkAlignment (Llvm.accessAlignment layout loadProp.alignment ty.val)
        memory.llvmLoad addr ty) with
      | .ok value => CTree.Sim relation target (pure (#[value], memory, none) : Tree _)
      | .ub _ => CTree.Sim relation target (ub : Tree _)
      | .fail _ => CTree.Sim relation target (fail : Tree _) := by
  cases ptr with
  | poison => rfl
  | val addr =>
    cases halign : addr.checkAlignment (Llvm.accessAlignment layout loadProp.alignment ty.val) <;>
      cases hload : memory.llvmLoad addr ty <;>
      simp [Llvm.interpretOpCTree, Llvm.interpretOp', halign, hload,
        monadLift, MonadLift.monadLift, Bind.bind]

/-- Once the target has returned, source freeze peeling is an equivalence.
Peel target choices first so the source witness can depend on them. -/
theorem Tree.sim_source_bind_freeze {ty : IntegerType}
    {relation : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
      (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Prop}
    (freezeProp : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int ty.bitwidth) (memory : MemoryState)
    (targetResult : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
      Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
    CTree.Sim relation
      (pure targetResult : Tree _) (CTree.bind
        (Llvm.freeze.interpretOpCTree freezeProp #[TypeAttr.of IntegerType ty]
          #[RuntimeValue.int ty.bitwidth value] #[] memory)
        next) ↔
    ∃ bits : BitVec ty.bitwidth, (value = .poison ∨ value = .val bits) ∧
      CTree.Sim relation
        (pure targetResult : Tree _) (next (#[RuntimeValue.int ty.bitwidth (.val bits)], memory, none)) := by
  cases value <;>
    simp [freeze_eq, CTree.CTree.choose_def, CTree.CTree.tau_def, Bind.bind]

/-- Peel the source root against a returned target, choosing one permitted result. -/
theorem Tree.sim_source_freeze {ty : IntegerType}
    {relation : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
      (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Prop}
    (freezeProp : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int ty.bitwidth) (memory : MemoryState)
    (targetResult : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    CTree.Sim relation
      (pure targetResult : Tree _) (Llvm.freeze.interpretOpCTree freezeProp #[TypeAttr.of IntegerType ty]
        #[RuntimeValue.int ty.bitwidth value] #[] memory) ↔
    ∃ bits : BitVec ty.bitwidth, (value = .poison ∨ value = .val bits) ∧
      CTree.Sim relation
        (pure targetResult : Tree _) (pure (#[RuntimeValue.int ty.bitwidth (.val bits)], memory, none) : Tree _) := by
  have peeled := Tree.sim_source_bind_freeze (relation := relation) freezeProp value memory targetResult pure
  change (CTree.Sim _ (pure targetResult : Tree _) (_ >>= pure) ↔ _) at peeled
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

set_option warn.sorry false in
example : CTree.Pattern.Valid recreateFreeze := by
  unfold recreateFreeze
  simpPuddleValid program sym =>
    simp only [RuntimeValue.Conforms.integerType, Veir.CTree.interpretOp', forall_exists_index,
      forall_eq_apply_imp_iff, Tree.sim_target_bind_freeze, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem!_pos, List.getElem_toArray,
      List.getElem_cons_zero, Tree.sim_source_freeze, CTree.Sim.pure, forall_const]
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
        (fun properties => properties == { nsw := false, nuw := false })
      let root ← MatchProg.root (.llvm .freeze) #[add.res[0]!] #[ty]
      return (ty, x, y, add.properties, root.properties))
    (fun (ty, x, y, addProp, freezeProp) => do
      let fx ← CreateProg.operation (.llvm .freeze) #[x] #[ty] freezeProp
      let fy ← CreateProg.operation (.llvm .freeze) #[y] #[ty] freezeProp
      CreateProg.operation (.llvm .add) #[fx.res[0]!, fy.res[0]!] #[ty] addProp)
    (fun result => result)

set_option warn.sorry false in
example : CTree.Pattern.Valid freezeAdd := by
  unfold freezeAdd
  simpPuddleValid program sym =>
    puddleNoAssignments
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff,
      CTree.CanInterpretTo.add_int, Interp.ok.injEq, Array.mk.injEq, List.cons.injEq, and_true,
      forall_eq, Veir.CTree.interpretOp', Tree.sim_target_bind_freeze, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem!_pos, List.getElem_toArray,
      List.getElem_cons_zero, Tree.sim_target_bind_add, Tree.sim_source_freeze, CTree.Sim.pure,
      OperationResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
      RuntimeValue.arrayIsRefinedBy_refl, and_true, ControlFlowAction.optionIsRefinedBy_refl,
      and_self, RuntimeValue.int_val_isRefinedBy_iff, RuntimeValue.int.injEq, heq_eq_eq, true_and,
      forall_const]
    simp only [IsOpCode.propertiesOf, _propertiesOf, Llvm.propertiesOf, forall_eq]
    grind [Data.LLVM.Int.add, Id.run]

end CTreePuddleTest

namespace CTreeStatefulPuddleTest

/-- Replace a load with another load. -/
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

/- Memory effects are allowed on both sides of a rewrite. -/
example : CTree.Pattern.Supported recreateLoad := by
  unfold recreateLoad
  unfoldPuddleBuilder
  simp [CTree.Pattern.Supported, get_effects, is_terminator]

set_option warn.sorry false in
example : CTree.Pattern.Valid recreateLoad := by
  unfold recreateLoad
  simpPuddleValid
  simp only [RuntimeValue.Conforms.llvmPointerType, Veir.CTree.interpretOp', forall_exists_index,
    forall_eq_apply_imp_iff, Tree.sim_target_bind_load, Tree.sim_source_load,
    CTree.Subeffect.mapEff, CTree.Subeffect.map_eq_inr, CTree.Subeffect.map_eq_self,
    CTree.HasUB.isUB_inr, CTree.HasUB.isUB_ube, sim_ub, TypeAttr.of_val, CTree.Subeffect.map_eq_inl,
    CTree.HasUB.isUB_inl, ErrorEIn.isUB, sim_fail, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem!_pos, List.getElem_toArray,
    List.getElem_cons_zero, CTree.Sim.pure, forall_const]
  rintro ty (ptr | _) prop memory
  · simp only
    split <;> simp
  · simp

end CTreeStatefulPuddleTest

namespace CTreeMatchPurityTest

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

/- An effectful non-root match is still forbidden, even when the root is also effectful. -/
example : ¬ CTree.Pattern.Supported matchTwoLoads := by
  unfold matchTwoLoads
  unfoldPuddleBuilder
  simp only [CTree.Pattern.Supported, is_terminator, get_effects, List.mem_cons, List.not_mem_nil,
    or_false, ne_eq, forall_eq_or_imp, not_true_eq_false, false_implies, and_self, Handle.mk.injEq,
    Nat.reduceEqDiff, not_false_eq_true, forall_const, true_and, forall_eq, and_true,
    Classical.not_forall]
  exact ⟨default, by decide⟩

end CTreeMatchPurityTest
