import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity

open Veir

namespace PuddleSymbolicStepTest

open Veir.Puddle.CTree

-- A concrete success must retain its construction safety obligation.
example (condition : Prop) :
    ((CreationM.choose (fun outcome : Interp Nat => outcome = .ok 0)).bind
      (fun _ => CreationM.check condition)).Models (fun _ => True) ↔ condition := by
  puddleStep sym []
  all_goals rfl

-- Failure reaches the final postcondition without calling the continuation.
example (next : Nat → CreationM Unit) (k : Interp Unit → Prop) :
    ((CreationM.choose (fun outcome : Interp Nat => outcome = .fail none)).bind next).Models k ↔
      k (.fail none) := by
  puddleStep sym []
  all_goals rfl

-- UB reaches the final postcondition without calling the continuation.
example (next : Nat → CreationM Unit) (k : Interp Unit → Prop) :
    ((CreationM.choose (fun outcome : Interp Nat => outcome = .ub none)).bind next).Models k ↔
      k (.ub none) := by
  puddleStep sym []
  all_goals rfl

-- Every nondeterministic choice must satisfy the postcondition.
example (k : Interp Nat → Prop) :
    ((CreationM.choose (fun outcome : Interp Nat => ∃ n, outcome = .ok n)).bind
      CreationM.pure).Models k ↔ ∀ n, k (.ok n) := by
  puddleStep sym []
  all_goals rfl

-- Peeling a known result must leave the next operation choice folded.
example (outcomes : Interp Nat → Prop) (k : Interp Nat → Prop)
    (h : (CreationM.choose outcomes).Models k) :
    ((CreationM.choose (fun outcome : Interp Nat => outcome = .ok 0)).bind
      (fun _ => CreationM.choose outcomes)).Models k := by
  puddleStep sym []
  run_tac
    let target ← Lean.Elab.Tactic.getMainTarget
    unless target.isAppOf ``CreationM.Models do
      throwError "puddleStep sym expanded the next operation choice"
  exact h

end PuddleSymbolicStepTest

namespace PuddleSymbolicStepsTest

open Veir.Puddle.CTree

-- Later operations must retain every earlier choice, including dependent choices.
example (condition : Nat → Nat → Prop) (k : Interp Nat → Prop)
    (h : ∀ x y, condition x y ∧ k (.ok (x + y))) :
    ((CreationM.choose (fun outcome : Interp Nat => ∃ x, outcome = .ok x)).bind
      (fun x => (CreationM.choose (fun outcome : Interp Nat => ∃ y, outcome = .ok y)).bind
        (fun y => (CreationM.check (condition x y)).bind
          (fun _ => CreationM.pure (x + y))))).Models k := by
  puddleSteps sym []
  exact h

end PuddleSymbolicStepsTest

namespace PuddleSymbolicBuilderTest

open Veir.Puddle Veir.Puddle.CTree

-- Match exports must keep their identifiers when creation continues the handle numbering.
private def rebuildAdd (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth == width)
      let lhs ← MatchProg.value ty
      let rhs ← MatchProg.value ty
      let root ← MatchProg.root (.llvm .add) #[lhs, rhs] #[ty]
      return (ty, lhs, rhs, root.properties))
    (fun (ty, lhs, rhs, properties) =>
      CreateProg.operation (.llvm .add) #[lhs, rhs] #[ty] properties)
    (fun result => result)

example (width : Nat) :
    (rebuildAdd width).matcher.numHandles = 6 ∧
    (rebuildAdd width).creation.numHandles = 8 ∧
    (rebuildAdd width).replacement.values = #[⟨7⟩] := by
  unfold rebuildAdd
  unfoldPuddleBuilderForSym
  all_goals simp [← Array.toList_inj]

private abbrev Metadata :=
  Handle OpCode .type × Handle OpCode (.prop (.llvm .add)) × Unit

-- Native callbacks stay abstract while nested metadata tuples allocate fresh handles.
private def rebuildWithMetadata
    (inspect : IRContext OpCode → OperationPtr → Option (MetadataValues OpCode Metadata))
    (rewrite : MetadataValues OpCode Metadata → Option (MetadataValues OpCode Metadata)) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value ty
      let rhs ← MatchProg.value ty
      let root ← MatchProg.root (.llvm .add) #[lhs, rhs] #[ty]
      let metadata ← MatchProg.inspectOperation (Outputs := Metadata) root.op inspect
      MatchProg.matchNative metadata (fun _ => true)
      return (lhs, rhs, metadata))
    (fun (lhs, rhs, metadata) => do
      let (ty, properties, _) ← CreateProg.applyNative (Outputs := Metadata) metadata rewrite
      CreateProg.operation (.llvm .add) #[lhs, rhs] #[ty] properties)
    (fun result => result)

example (inspect rewrite) :
    (rebuildWithMetadata inspect rewrite).matcher.numHandles = 8 ∧
    (rebuildWithMetadata inspect rewrite).creation.numHandles = 12 ∧
    (rebuildWithMetadata inspect rewrite).replacement.values = #[⟨11⟩] := by
  unfold rebuildWithMetadata
  unfoldPuddleBuilderForSym
  run_tac
    let target ← Lean.Elab.Tactic.getMainTarget
    if (target.find? fun e => e.isAppOf ``Pattern.Builder ||
        e.isAppOf ``MetadataTuple.Shape.fresh).isSome then
      throwError "symbolic builder normalization left unexpanded metadata allocation"
  all_goals simp [← Array.toList_inj]

-- Probe the tactic boundary with opaque native callbacks. This checks normalization
-- without assuming that an arbitrary metadata rewrite is semantically valid.
example (_inspect : IRContext OpCode → OperationPtr → Option (MetadataValues OpCode Metadata))
    (_rewrite : MetadataValues OpCode Metadata → Option (MetadataValues OpCode Metadata)) : True := by
  run_tac
    let saved ← Lean.Elab.Tactic.getGoals
    let type ← Lean.Elab.Term.elabTerm
      (← `(CTree.Pattern.Valid (rebuildWithMetadata $(Lean.mkIdent `_inspect) $(Lean.mkIdent `_rewrite)))) none
    let probe ← Lean.Meta.mkFreshExprMVar type
    Lean.Elab.Tactic.setGoals [probe.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      unfold rebuildWithMetadata
      provePuddleValid program sym =>
        puddleNoAssignments)))
    unless (← Lean.Elab.Tactic.getGoals).length == 2 do
      throwError "opaque native construction must retain its separate success obligation"
    Lean.Elab.Tactic.setGoals saved
  trivial

end PuddleSymbolicBuilderTest

namespace CTreeExecutionTest

-- Ordinary CTree bind does not execute a continuation after an abort.
example (next : Nat → Tree Unit) :
    Tree.interp_ub_and_error (CTree.bind (ub : Tree Nat) next) = pure (.ub none) := by
  simp

example (next : Nat → Tree Unit) :
    Tree.interp_ub_and_error (CTree.bind (fail : Tree Nat) next) = pure (.fail none) := by
  simp

-- The adapter preserves each choice rather than selecting an outcome early.
example (next : BitVec 8 → Tree Nat) :
    Tree.interp_ub_and_error (do
      let bits ← CTree.CTree.choose (E := ErrorE ⊕ₑ UBE) (C := FreezeC) (SubC := FreezeC) (FreezeCIn.mk 8)
      next bits) =
    CTree.CTree.tauG (.inr (FreezeCIn.mk 8)) (fun bits => Tree.interp_ub_and_error (next bits)) := by
  simp [CTree.CTree.choose_def, CTree.CTree.tau_def, Bind.bind]

-- A source abort permits a successful target, as in Interp.isRefinedBy.
example (value : Nat) : Tree.Refines Eq (ub : Tree Nat) (pure value) := by
  simp only [Tree.Refines, Tree.interp_ub_and_error_ub, Tree.interp_ub_and_error_pure]
  exact (CTree.Sim.ret _ _ _).mpr trivial

example (value : Nat) : Tree.Refines Eq (fail : Tree Nat) (pure value) := by
  simp only [Tree.Refines, Tree.interp_ub_and_error_fail, Tree.interp_ub_and_error_pure]
  exact (CTree.Sim.ret _ _ _).mpr trivial

-- Failure of the target cannot refine a successful source outcome.
example (value : Nat) : ¬ Interp.isRefinedBy Eq (.ok value) (.fail none) := by
  simp [Interp.isRefinedBy]

-- Simulation's bind rule remains available for compositional proofs.
example (left right : Tree Nat) (next next' : Nat → Tree Nat)
    (head : CTree.Sim Eq left right)
    (tail : ∀ value, CTree.Sim Eq (next value) (next' value)) :
    CTree.Sim Eq (left >>= next) (right >>= next') := by
  apply CTree.Sim.bind _ _ _ _ head
  rintro x y rfl
  exact tail x

end CTreeExecutionTest

namespace CTreeRefinesPrintingTest

open Lean Elab Tactic

private meta def checkDoNotation (sourceLength targetLength : Nat) : TacticM Unit :=
  withMainContext do
    let target ← getMainTarget
    let stx ← PrettyPrinter.delab target
    let `(term| $_ $_ $source $dest) := stx
      | throwError "expected a refinement application, got {stx}"
    let `(term| do $source:doSeqItem*) := source
      | throwError "expected do notation in the source argument, got {stx}"
    let `(term| do $dest:doSeqItem*) := dest
      | throwError "expected do notation in both refinement arguments, got {stx}"
    unless source.size == sourceLength && dest.size == targetLength do
      throwError "expected flattened do sequences, got {stx}"
    let recovered ← Term.elabTerm stx (some (mkSort .zero))
    unless ← Meta.isDefEq recovered target do
      throwError "displayed refinement does not elaborate to the original expression"
    for (option, value) in [( `pp.explicit, true), (`pp.notation, false)] do
      let raw ← withOptions (·.setBool option value) (PrettyPrinter.delab target)
      if raw == stx then
        throwError "refinement printer ignored {option}"

-- Both concrete CTree.bind and ordinary monadic bind flatten; unused values and
-- local lets must survive printing and elaboration without changing the program.
example (source target : Tree Nat) :
    Tree.Refines Eq
      (CTree.bind source fun value => do
        let doubled := value + value
        let _ ← target
        pure doubled)
      target →
    Tree.Refines Eq
      (CTree.bind source fun value => do
        let doubled := value + value
        let _ ← target
        pure doubled)
      target := by
  intro h
  run_tac checkDoNotation 4 1
  exact h

-- A named continuation is displayed as a bind followed by its application.
example (source : Tree Nat) (next : Nat → Tree Nat) :
    Tree.Refines Eq (pure 0) (CTree.bind source next) →
    Tree.Refines Eq (pure 0) (CTree.bind source next) := by
  intro h
  run_tac checkDoNotation 1 2
  exact h

end CTreeRefinesPrintingTest
