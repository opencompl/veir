module

public import Veir.PatternRewriter.Internal.Traversal
import all Veir.PatternRewriter.Basic
import all Veir.IR.WellFormed
import all Veir.IR.Basic
import all Init.Data.Array.Basic

public section
namespace Veir.PatternRewriter
variable {OpInfo : Type} [HasOpInfo OpInfo]

variable {w : Worklist} {P Q : OperationPtr → Prop} {op : OperationPtr}

theorem Worklist.All.mono (h : w.All P) (f : ∀ op, P op → Q op) : w.All Q :=
  fun op mem => f op (h op mem)

theorem Worklist.All.push (h : w.All P) (ok : P op) : (w.push op).All P := by
  unfold Worklist.push
  split
  · exact h
  · intro other mem
    simp only [Array.mem_push, Option.some.injEq] at mem
    rcases mem with mem | rfl
    · exact h _ mem
    · exact ok

theorem Worklist.All.remove (h : w.All P) : (w.remove op).All P := by
  unfold Worklist.remove
  split
  · intro other mem
    obtain ⟨i, hi, eq⟩ := Array.getElem_of_mem mem
    simp only [Array.getElem_set] at eq
    split at eq
    · contradiction
    · exact h _ (eq ▸ Array.getElem_mem (by simpa using hi))
  · exact h

theorem Worklist.All.pop (h : w.All P) :
    w.pop.2.All P ∧ ∀ op, w.pop.1 = some op → P op := by
  have kept : ∀ x ∈ w.stack.popWhile (· = none), x ∈ w.stack := by
    have sub (xs : Array (Option OperationPtr)) : ∀ x ∈ xs.popWhile (· = none), x ∈ xs := by
      have subPop (xs : Array (Option OperationPtr)) (x) (mem : x ∈ xs.pop) : x ∈ xs := by
        obtain ⟨i, hi, eq⟩ := Array.getElem_of_mem mem
        grind [Array.getElem_mem]
      fun_induction Array.popWhile <;> grind
    exact sub _
  unfold Worklist.pop
  dsimp only
  split
  · constructor
    · exact fun op mem => h _ (kept _ mem)
    · simp
  · constructor
    · intro op mem
      obtain ⟨i, hi, eq⟩ := Array.getElem_of_mem mem
      apply h _ (kept _ ?_)
      grind [Array.getElem_mem]
    · intro op eq
      cases eq
      apply h _ (kept _ ?_)
      simp only [Option.some_get]
      exact Array.back_mem _

/-- Following a use chain only enqueues owners whose operand is the indicated value. -/
private theorem all_addUseChain {P : OperationPtr → Prop} (fuel : Nat)
    (rw : PatternRewriter OpInfo) (v : ValuePtr) (chain : Option OpOperandPtr) (hin)
    (all : rw.worklist.All P)
    (users : ∀ op, op.InBounds rw.ctx.raw → v ∈ op.getOperands! rw.ctx.raw → P op)
    (points : ∀ use, chain = some use → use.getValue! rw.ctx.raw = v) :
    (rw.addUseChainUserInWorklist chain fuel hin).worklist.All P := by
  induction fuel generalizing rw chain with
  | zero => exact all
  | succ n ih =>
    cases chain with
    | none => exact all
    | some u =>
      have uIn : u.InBounds rw.ctx.raw := by simpa [Option.maybe_def] using hin
      have value := points u rfl
      have ⟨opIn, bound⟩ := u.inBounds_def.mp uIn
      have idx : u.index < u.op.getNumOperands! rw.ctx.raw := by grind
      have owner := (rw.ctx.wellFormed.operations u.op opIn).operand_owner u.index idx
      have self : u.op.getOpOperand u.index = u := by cases u; rfl
      rw [self] at owner
      have ok : P (u.getOwner rw.ctx.raw uIn) := by
        rw [← OpOperandPtr.getOwner!_eq_getOwner uIn, owner]
        apply users _ opIn (OperationPtr.getOperands!.mem_iff_exists_index.mpr ⟨u.index, idx, ?_⟩)
        simpa only [OperationPtr.getOperand!_eq_OpOperandPtr_get!, self] using value
      simp only [addUseChainUserInWorklist]
      apply ih {rw with worklist := rw.worklist.push _} _ _ (all.push ok) users
      intro next link
      have ⟨array, defuse⟩ := rw.ctx.wellFormed.valueDefUseChains v (by grind)
      have link' : u.getNextUse! rw.ctx.raw = some next := by simpa [OpOperandPtr.getNextUse!_eq_getNextUse uIn] using link
      have chainMem : u ∈ array := (defuse.allUsesInChain u uIn value).mpr (by simp)
      rw [← value] at defuse
      exact (ValuePtr.DefUse.value!_eq_value!_of_nextUse!_eq chainMem defuse link').symm.trans value

private theorem all_addUsers (rw : PatternRewriter OpInfo) (v : ValuePtr) (hin)
    (all : rw.worklist.All P)
    (users : ∀ op, op.InBounds rw.ctx.raw → v ∈ op.getOperands! rw.ctx.raw → P op) :
    (rw.addUsersInWorklist v hin).worklist.All P := by
  apply all_addUseChain _ _ v _ _ all users
  intro u first
  exact rw.ctx.wellFormed.OpOperandPtr_value_of_getFirstUse hin (by simpa [ValuePtr.getFirstUse!_eq_getFirstUse hin] using first)

theorem all_replaceValue! (rw : PatternRewriter OpInfo) (v newValue : ValuePtr)
    (hin : v.InBounds rw.ctx.raw) (all : rw.worklist.All P)
    (users : ∀ op, op.InBounds rw.ctx.raw → v ∈ op.getOperands! rw.ctx.raw → P op) :
    (rw.replaceValue! v newValue).worklist.All P := by
  simpa only [replaceValue!, dite_eq_left hin] using all_addUsers rw v hin all users

private theorem forIn_all {α σ : Type} (xs : List α) (body : α → σ → Id (ForInStep σ))
    (P : σ → Prop) (step : ∀ x ∈ xs, ∀ s, P s → P (body x s).run.value)
    (s : σ) (start : P s) : P (forIn xs s body).run := by
  induction xs generalizing s with
  | nil => exact start
  | cons hd tl ih =>
    rw [List.forIn_cons]
    have post := step hd (by simp) s start
    cases h : body hd s with
    | done last => simpa [h, Id.run, ForInStep.value, Bind.bind, Pure.pure] using post
    | yield next =>
      exact ih (fun x hx => step x (by simp [hx])) next (by simpa [h, Id.run, ForInStep.value, Bind.bind, Pure.pure] using post)

theorem all_eraseOp (rw : PatternRewriter OpInfo) (op : OperationPtr) (regions unused inside)
    (all : rw.worklist.All P)
    (defs : ∀ v ∈ op.getOperands! rw.ctx.raw, ∀ d, v.definingOp? = some d → P d) :
    (rw.eraseOp op regions unused inside).worklist.All P := by
  unfold eraseOp
  dsimp only [Id.run, Bind.bind, Pure.pure]
  rw [← Array.forIn_toList]
  apply forIn_all _ _ (Worklist.All · P) ?_ _ all.remove
  intro v mem w prior
  try dsimp only
  split
  · rename_i d found
    split
    · exact prior.push (defs v (by simpa [OperationPtr.getOperands!_eq_getOperands inside] using mem) d found)
    · exact prior
  · exact prior

end Veir.PatternRewriter
