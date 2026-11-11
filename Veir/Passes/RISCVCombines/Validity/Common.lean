module

public import Veir.Interpreter.CTree
import all Veir.Interpreter.CTree
import all Veir.Interpreter.RuntimeValue.Conforms

public meta import Lean
public import Veir.IR.Simp
import all Veir.Passes.RISCVCombines.Combine
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.Dialects.RV64.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.RISCV.Interpreter
import all Veir.IR.Attribute
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Lemmas
import all Veir.Data.Refinement
import Veir.PatternRewriter.Puddle.Definitions
import Veir.PatternRewriter.Puddle.Validity
import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import Veir.Passes.RISCVCombines.Proofs

/-! Shared imports, tactics and semantic lemmas for the CTree validity proofs of the RISC-V
combines. Each proof unfolds the pattern with the `riscv_pattern` simp set, normalizes its
semantics down to a register equality and closes it
with the combine's local correctness lemma from `Veir.Passes.RISCVCombines.Proofs`. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

/-- Bind a type equation introduced by a `TypeAttr` matcher.
Copied from `math-fehr/puddle-ctree-wip` (`InstructionSelection/Proofs/Utils.lean`). -/
@[simp, ctree_semantics]
theorem TypeAttr.forall_of_eq_imp_iff {T : Type} [IsTypeAttr T] {P : TypeAttr → T → Prop} :
    (∀ (type : TypeAttr) (x : T), TypeAttr.of T x = type → P type x) ↔
      (∀ (x : T), P (TypeAttr.of T x) x) := by
  grind

@[simp, ctree_semantics]
theorem PureOrErr.checked_return {p : Prop} [Decidable p] {value result : α} :
    PureOrErr.CanInterpretTo (if p then (pure value : Tree α) else ub) (.ok result) ↔
      p ∧ result = value := by
  by_cases h : p <;> simp [h, Veir.ub, CTree.trigger_def]

@[simp, ctree_semantics]
theorem Sim.check_source {p : Prop} [Decidable p] {R : α → β → Prop}
    {target : Tree α} {source : Tree β} :
    Sim R target (if p then source else ub) ↔ (p → Sim R target source) := by
  by_cases h : p <;> simp [h]

attribute [ctree_semantics] PureOrErr.CanInterpretTo.bind_iff

/-- Expose the outcome of an `Interp` computation forming the entire source tree.
Copied from `math-fehr/puddle-ctree-wip` (`InstructionSelection/Proofs/Utils.lean`), where it is
tagged `ctree_semantics`. Here it is passed explicitly by `simpCombineSemantics`, because the
store proofs must keep the source lifted. -/
theorem Sim.bind_monadLift_right_iff {EIn : Type} {E : EIn → Type}
    [HasUB EIn] [ErrorE -< E] [UBE -< E]
    {CIn C'In : Type} {C : CIn → Type} {C' : C'In → Type}
    {α β : Type} (relation : α → β → Prop)
    (other : CTree E C α) (func : Interp β) :
    CTree.Sim relation other (monadLift func : CTree E C' β) ↔
      match func with
      | .ok value => CTree.Sim relation other (pure value : CTree E C' β)
      | .ub _ => CTree.Sim relation other (ub : CTree E C' β)
      | .fail _ => CTree.Sim relation other (fail : CTree E C' β) := by
  cases func <;> rfl

open Lean Meta in
/-- Split, recursively, each local conjunction and existential, such as the result and memory
equations of a matched operation (see `Puddle.CTree.CanInterpretTo`) or the bytes a load read. -/
meta partial def casesAnds (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type ← instantiateMVars decl.type
      unless type.isAppOfArity ``And 2 || type.isAppOfArity ``Exists 2 do continue
      let subgoals ← goal.cases decl.fvarId
      return (← subgoals.toList.mapM fun subgoal => casesAnds subgoal.mvarId).flatten
    return [goal]

open Lean Elab Tactic in
/-- Split every local conjunction and existential. -/
elab "casesAnds" : tactic => do
  let goals ← getGoals
  setGoals (← goals.flatMapM fun goal => casesAnds goal)

open Lean Elab Tactic in
elab "clearCombineVerification" : tactic => do
  let goals ← getGoals
  setGoals (← goals.mapM fun goal => goal.withContext do
    let mut goal := goal
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if (← instantiateMVars decl.type).isAppOf ``Veir.IsFromVerifiedOp then
        goal ← goal.tryClear decl.fvarId
    return goal)

open Lean Meta Elab Tactic in
/-- Simplify each case before splitting the next value. Successful operation equations
fix intermediate results, so splitting all results at once creates redundant branches. -/
meta partial def normalizeConformingValues (goal : MVarId) : TacticM (List MVarId) := do
  setGoals [goal]
  evalTactic (← `(tactic| (
    try simp_all [RuntimeValue.isRefinedBy]
    all_goals (try casesAnds)
    all_goals (try subst_vars))))
  let goals ← getGoals
  goals.flatMapM fun goal => goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type ← instantiateMVars decl.type
      unless type.isAppOfArity ``RuntimeValue.Conforms 2 do continue
      let .fvar value := type.appFn!.appArg! | continue
      let subgoals ← goal.cases value
      return (← subgoals.toList.mapM fun subgoal =>
        normalizeConformingValues subgoal.mvarId).flatten
    return [goal]

open Lean Elab Tactic in
elab "casesConformingValues" : tactic => do
  let goals ← getGoals
  setGoals (← goals.flatMapM normalizeConformingValues)

/-- Unfold the operation semantics of a goal produced by `simpPuddleValid`. -/
macro "simpCombineSemantics" : tactic => `(tactic|
  simp [ctree_semantics, Sim.bind_monadLift_right_iff])

/-- Split the matched inputs of a normalized combine validity goal, then substitute the results
of the matched operations. Each round resolves one more level of nested matched operations:
an operation's result equation only appears once its operands are known registers. -/
macro "normalizeCombineValid" : tactic => `(tactic| (
  intros
  clearCombineVerification
  casesConformingValues
  iterate 4 (
    all_goals (try simp_all [RuntimeValue.isRefinedBy])
    all_goals (try casesAnds)
    all_goals (try subst_vars)
    all_goals (try intros)
    all_goals clearCombineVerification)))

/-- Prove the validity of a combine pattern, closing each
remaining register equality with the local correctness lemma `lemma` from
`Veir.Passes.RISCVCombines.Proofs`. The lemma's conclusion must match the normalized goal; its
hypotheses (the matcher's guards) are discharged from the matched properties. -/
macro "proveCombineValid" "using" lemma:term : tactic => `(tactic| (
  try simp only [riscv_pattern]
  simpPuddleValid
  simpCombineSemantics
  all_goals normalizeCombineValid
  all_goals first
    | (solve | apply $lemma <;> simp_all)
    | (try simp_all [($lemma)]
       all_goals split <;> simp_all [RuntimeValue.isRefinedBy, ControlFlowAction.optionIsRefinedBy])))

/-! ### Stores

A store writes a little-endian prefix of its value register. The local lemmas
`Data.RISCV.drop_<ext>_<store>` show that the dropped extension does not change that prefix. -/

/-- A root store and a created store that write the same bytes simulate each other.
The statement keeps the source as a lifted `Interp` computation, so that it can be transported
into a normalized goal through `Sim.bind_monadLift_right_iff` without rewriting below the
dependent size proof of `MemoryState.store`. -/
theorem sim_store {R : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
      (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Prop}
    (hR : ∀ mem, R (#[], mem, none) (#[], mem, none))
    (mem : MemoryState) (p : Data.Pointer) (source target poison : ByteArray)
    (hsource : poison.size = source.size) (htarget : poison.size = target.size)
    (hbytes : source = target) :
    CTree.Sim R
      (CTree.bind (monadLift (mem.store p target poison htarget >>= fun mem =>
          (Interp.ok (#[], mem, none) :
            Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction))) :
          Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
        fun result => CTree.bind
          (if result.1 = #[] then pure result else ub)
          (fun result => pure (#[], result.2.fst, none)))
      (CTree.bind (monadLift (mem.store p source poison hsource >>= fun mem =>
          (Interp.ok (#[], mem, none) :
            Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction))) :
          Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
        (fun result => if result.1 = #[] then pure result else ub)) := by
  subst hbytes
  cases mem.store p source poison hsource <;> simp [hR, monadLift, MonadLift.monadLift]

/-- A lifted failing source is simulated by any target. -/
@[simp]
theorem sim_monadLift_fail_right {α β : Type} (R : α → β → Prop) (target : Tree α)
    (location : Option OperationPtr) :
    CTree.Sim R target (monadLift (Interp.fail location : Interp β) : Tree β) := by
  simp [monadLift, MonadLift.monadLift]

/-- A lifted source with undefined behavior is simulated by any target. -/
@[simp]
theorem sim_monadLift_ub_right {α β : Type} (R : α → β → Prop) (target : Tree α)
    (location : Option OperationPtr) :
    CTree.Sim R target (monadLift (Interp.ub location : Interp β) : Tree β) := by
  simp [monadLift, MonadLift.monadLift]

/-- Close a store-combine validity goal, normalized by `simp [ctree_semantics]`, given the local
lemma `bytes` showing that the dropped extension does not change the stored bytes. -/
macro "closeStoreValid" bytes:term : tactic => `(tactic| (
  all_goals normalizeCombineValid
  all_goals
    exact sim_store
      (by simp [RuntimeValue.arrayIsRefinedBy_refl, ControlFlowAction.optionIsRefinedBy])
      _ _ _ _ _ _ _ $bytes))

/-- Prove the validity of a store combine, given the local
lemma `bytes` showing that the dropped extension does not change the stored bytes. -/
macro "proveStoreValid" bytes:term : tactic => `(tactic| (
  try simp only [riscv_pattern]
  simpPuddleValid
  try simp [ctree_semantics]
  all_goals closeStoreValid $bytes))

end Veir.RISCV.CTreeProofs
