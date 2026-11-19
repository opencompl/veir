module

public import Veir.Interpreter.CTreeInterpreter
import all CTree.Interp

public section

/-!
# The closed CFG interpreter

`interpretRegion` runs a region's CFG in `RegionTree`, whose effects include region calls, and
closes them with `CTree.mrec`. The event type of a `RegionTree` depends on its context, so two
trees from different contexts cannot be compared with `CTree.Sim` before `mrec` removes the
region calls.

No operation calls a region, so the CFG loop can be run as a closed `Tree` instead. This file
defines that closed loop. It keeps the silent steps of the ordinary interpreter: `inflate` is the
event-handler layer that `interpretOp` and `mrec` each wrap around a tree.
-/

open CTree

namespace Veir.CTree

/-- Re-emit the events of a closed tree with the ordinary CTree event interpreter, keeping the
silent steps it inserts. -/
@[expose]
def inflate (tree : Tree α) : Tree α :=
  CTree.interp (fun event => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) event) tree

@[simp] theorem inflate_pure (value : α) : inflate (pure value : Tree α) = pure value := by
  unfold inflate CTree.interp
  rw [CTree.iter]
  simp

private theorem inflate_tau (choice : C1In ⊕ FreezeCIn)
    (next : (C1 ⊕ₑ FreezeC) choice → Tree α) :
    inflate (.tauG choice next) = .tauG choice (fun x => .tau1 (inflate (next x))) := by
  unfold inflate CTree.interp
  rw [CTree.iter]
  simp

private theorem inflate_vis (event : ErrorEIn ⊕ UBEIn)
    (next : (ErrorE ⊕ₑ UBE) event → Tree α) :
    inflate (.vis event next) = .vis event next := by
  unfold inflate CTree.interp
  rw [CTree.iter]
  cases event <;> simp [CTree.trigger_def, Bind.bind] <;>
    congr 1 <;> funext impossible <;> exact nomatch impossible

open Tower in
/-- Inflation preserves the tree up to silent steps, including on infinite branches. -/
theorem inflate_sim_eq (t : Tree α) : Sim Eq (inflate t) t ∧ Sim Eq t (inflate t) := by
  letI : Std.Refl (@Eq α) := ⟨fun _ => rfl⟩
  let F := MuSimF (E := ErrorE ⊕ₑ UBE) (C := FreezeC) (C' := FreezeC) (@Eq α)
  have both : ∀ R : Chain F, ∀ t : Tree α,
      R.elem true (inflate t) t ∧ R.elem true t (inflate t) := by
    apply tower_ind (f := F)
      (P := fun R => ∀ t : Tree α, R true (inflate t) t ∧ R true t (inflate t))
    · intro P ih t
      constructor <;> rw [inf_iff_ternary_rel] <;> intro R hR
      · exact (ih R hR t).1
      · exact (ih R hR t).2
    · intro R ih t
      cases t using CTree.CTree.cases with
      | ret x =>
        change F R.elem true (inflate (pure x)) (pure x) ∧ F R.elem true (pure x) (inflate (pure x))
        rw [inflate_pure]
        exact ⟨MuSimF.refl Eq (Chain.next F R) _, MuSimF.refl Eq (Chain.next F R) _⟩
      | vis e k =>
        rw [inflate_vis]
        exact ⟨MuSimF.refl Eq (Chain.next F R) _, MuSimF.refl Eq (Chain.next F R) _⟩
      | tau c k =>
        rw [inflate_tau]
        constructor
        · apply MuSimF.tau Eq R
          intro x
          exact ⟨x, MuSimF.tau1_l Eq R (ih (k x)).1⟩
        · apply MuSimF.tau Eq R
          intro x
          exact ⟨x, MuSimF.tau_r Eq R _ _ _ PUnit.unit (ih (k x)).2⟩
  constructor <;> rw [Sim, LTS.Sim, gfp_iff_ternary_rel] <;> intro R
  · exact (both R t).1
  · exact (both R t).2

/-- Re-emitting the same events preserves simulation, including undefined behavior. -/
theorem sim_inflate {RR : α → β → Prop} {t : Tree α} {u : Tree β} (h : Sim RR t u) :
    Sim RR (inflate t) (inflate u) := by
  apply Sim.trans ((inflate_sim_eq t).1) (Sim.trans h (inflate_sim_eq u).2 ?_)
  · rintro _ _ _ rfl hrel
    exact hrel
  · rintro _ _ _ hrel rfl
    exact hrel

/-- Interpret an operation as a closed tree, with the two event-handler layers of `interpretOp`. -/
@[expose]
def interpretOperationTree (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (inBounds : op.InBounds ctx.raw := by grind) :
    Tree (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op | fail
  let opType := op.getOpType ctx.raw inBounds
  let (resultValues, mem, action) ← inflate (inflate (interpretOp' opType
    (op.getProperties ctx.raw opType) (op.getResultTypes ctx.raw) operands
    (op.getSuccessors ctx.raw) state.memory (op.getRegions ctx.raw)))
  let some variables := state.variables.setResultValues? op resultValues inBounds | fail
  return (⟨variables, mem⟩, action)

/-- Continue a closed CFG step after an operation produced its control-flow action. -/
@[expose]
def interpretCFGTreeContinue {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (action : Option ControlFlowAction)
    (opIn : op.InBounds ctx.raw := by grind) :
    Tree ((interpretCFG.StateLocation ctx × InterpreterState ctx) ⊕
      (InterpreterState ctx × Array RuntimeValue)) := do
  match action with
  | some (.return results) => return .inr (state, results)
  | some (.branch args dest) =>
    if h : dest.InBounds ctx.raw then
      return .inl (.inl (⟨dest, h⟩, args), state)
    else fail
  | none =>
    rlet some nextOp := op.getNextOp ctx.raw | fail
    return .inl (.inr ⟨nextOp, by grind⟩, state)

/-- One closed CFG step: enter a block, or run an operation. -/
@[expose]
def interpretCFGTreeStep {ctx : WfIRContext OpCode}
    (location : interpretCFG.StateLocation ctx) (state : InterpreterState ctx) :
    Tree ((interpretCFG.StateLocation ctx × InterpreterState ctx) ⊕
      (InterpreterState ctx × Array RuntimeValue)) := do
  match location with
  | .inl (⟨block, blockIn⟩, values) =>
    if values.size != block.getNumArguments ctx.raw then fail else
    let some variables := state.variables.setArgumentValues? block values | fail
    rlet some firstOp := block.getFirstOp ctx.raw | fail
    return .inl (.inr ⟨firstOp, by grind⟩, ⟨variables, state.memory⟩)
  | .inr ⟨op, opIn⟩ =>
    let (state, action) ← interpretOperationTree op state opIn
    interpretCFGTreeContinue op state action

/-- The closed CFG loop of a region. -/
@[expose]
def interpretCFGTree (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw := by grind) :
    Tree (InterpreterState ctx × Array RuntimeValue) := do
  rlet some firstBlock := region.getFirstBlock ctx.raw | fail
  _root_.CTree.iter (fun (location, state) => interpretCFGTreeStep location state)
    (.inl (⟨firstBlock, by grind⟩, values), state)

end Veir.CTree
