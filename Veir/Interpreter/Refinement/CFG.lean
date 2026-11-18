module

public import Veir.Interpreter.Refinement.Basic
import Veir.Interpreter.Refinement.Lemmas
import all Veir.Interpreter.Basic
import all Init.Internal.Order.Basic

public section

/-!
# Refinement of control-flow graphs

`interpretBlockCFG` is a partial fixpoint, so a refinement between two runs of
it cannot be shown by unfolding. `interpretBlockCFG_isRefinedBy` reduces it to
a statement about single blocks: a relation between the calls that is
re-established whenever both sides branch. This is the principle by which a
transformation that is not a local rewrite lifts from blocks to functions.
-/

namespace Veir

open Lean.Order

/-- A predicate on one value of a function is admissible if it is admissible on that value. -/
theorem admissible_eval {α : Sort u} {β : α → Sort v} [∀ x, CCPO (β x)] (x : α)
    {Q : β x → Prop} (hadm : admissible Q) : admissible (fun (f : ∀ x, β x) => Q (f x)) := by
  intro c hchain h
  rw [← fun_csup_eq]
  apply hadm _ (chain_apply hchain x)
  rintro _ ⟨f, hcf, rfl⟩
  exact h _ hcf

variable {ctx ctx' : WfIRContext OpCode}

/--
  A relation between a call of `interpretBlockCFG` in `ctx` and one in `ctx'`:
  the block to run, the values of its arguments, and the state.
-/
abbrev BlockCallRel (ctx ctx' : WfIRContext OpCode) : Type :=
  BlockPtr → Array RuntimeValue → InterpreterState ctx →
  BlockPtr → Array RuntimeValue → InterpreterState ctx' → Prop

/--
  The outcomes of one block are related: both return values related by `R`, or
  both branch, to blocks that are in bounds together and whose calls are
  related by `Rel` again.
-/
@[expose]
def BlockCallRel.Step (Rel : BlockCallRel ctx ctx')
    (R : InterpreterState ctx × Array RuntimeValue →
      InterpreterState ctx' × Array RuntimeValue → Prop)
    (source : InterpreterState ctx × ControlFlowAction)
    (target : InterpreterState ctx' × ControlFlowAction) : Prop :=
  match source.2, target.2 with
  | .return res, .return res' => R (source.1, res) (target.1, res')
  | .branch res succ, .branch res' succ' =>
    succ.InBounds ctx.raw → succ'.InBounds ctx'.raw ∧ Rel succ res source.1 succ' res' target.1
  | _, _ => False

/--
  If related calls run their block to related outcomes, then related calls
  run their control-flow graph to related results.
-/
theorem interpretBlockCFG_isRefinedBy {Rel : BlockCallRel ctx ctx'}
    {R : InterpreterState ctx × Array RuntimeValue →
      InterpreterState ctx' × Array RuntimeValue → Prop}
    (hStep : ∀ block values state block' values' state'
      (blockIn : block.InBounds ctx.raw) (blockIn' : block'.InBounds ctx'.raw),
      Rel block values state block' values' state' →
      Interp.isRefinedBy (Rel.Step R)
        (interpretBlock block values state blockIn)
        (interpretBlock block' values' state' blockIn'))
    {block values state block' values' state'}
    (blockIn : block.InBounds ctx.raw) (blockIn' : block'.InBounds ctx'.raw)
    (hRel : Rel block values state block' values' state') :
    Interp.isRefinedBy R
      (interpretBlockCFG block values state blockIn)
      (interpretBlockCFG block' values' state' blockIn') := by
  refine interpretBlockCFG.fixpoint_induct (ctx := ctx)
    (motive := fun f => ∀ block values state (blockIn : block.InBounds ctx.raw),
      ∀ block' values' state' (blockIn' : block'.InBounds ctx'.raw),
      Rel block values state block' values' state' →
      Interp.isRefinedBy R (f block values state blockIn)
        (interpretBlockCFG block' values' state' blockIn')) ?_ ?_
    block values state blockIn block' values' state' blockIn' hRel
  · apply admissible_pi; intro b
    apply admissible_pi; intro v
    apply admissible_pi; intro s
    apply admissible_pi; intro hb
    iterate 5 (apply admissible_pi; intro _)
    let T := Interp (InterpreterState ctx × Array RuntimeValue)
    refine admissible_eval (β := fun b : BlockPtr => Array RuntimeValue → InterpreterState ctx →
        autoParam (b.InBounds ctx.raw) interpretBlockCFG._auto_1 → T) b
      (Q := fun g => Interp.isRefinedBy R (g v s hb) _) ?_
    refine admissible_eval (β := fun _ : Array RuntimeValue => InterpreterState ctx →
        autoParam (b.InBounds ctx.raw) interpretBlockCFG._auto_1 → T) v
      (Q := fun g => Interp.isRefinedBy R (g s hb) _) ?_
    refine admissible_eval (β := fun _ : InterpreterState ctx =>
        autoParam (b.InBounds ctx.raw) interpretBlockCFG._auto_1 → T) s
      (Q := fun g => Interp.isRefinedBy R (g hb) _) ?_
    refine admissible_eval (β := fun _ : autoParam (b.InBounds ctx.raw) interpretBlockCFG._auto_1 => T)
      hb (Q := fun g => Interp.isRefinedBy R g _) ?_
    exact Interp.admissible_of_ub _ (by simp [Interp.isRefinedBy])
  · intro f ih block values state blockIn block' values' state' blockIn' hRel
    have hBlock := hStep block values state block' values' state' blockIn blockIn' hRel
    rw [interpretBlockCFG]
    rcases hsrc : interpretBlock block values state blockIn with _ | _ | ⟨s, cf⟩
    · simp [hsrc, Interp.isRefinedBy]
    · simp [hsrc, Interp.isRefinedBy]
    · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hBlock
      obtain ⟨⟨s', cf'⟩, htgt, hStepRel⟩ := hBlock
      simp only [hsrc, htgt]
      cases cf <;> cases cf' <;> simp only [BlockCallRel.Step] at hStepRel
      · simpa [Interp.isRefinedBy] using hStepRel
      next res succ res' succ' =>
        by_cases hIn : succ.InBounds ctx.raw
        · have ⟨hIn', hRel'⟩ := hStepRel hIn
          simp only [hIn, hIn', ↓reduceDIte]
          exact ih _ _ _ hIn _ _ _ hIn' hRel'
        · simp [hIn, Interp.isRefinedBy]

end Veir
