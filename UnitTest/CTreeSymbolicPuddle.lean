import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import CTree.Delaborator

open Veir

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
  unfoldPuddleBuilder
  all_goals simp [← Array.toList_inj]

private abbrev Metadata :=
  Handle OpCode .type × Handle OpCode (.prop (.llvm .add)) × Unit

-- Native callbacks stay abstract while nested metadata tuples allocate fresh handles.
private def rebuildWithMetadata
    (inspect : IRContext OpCode → OperationPtr → Option (MetadataValues OpCode Metadata))
    (rewrite : MetadataValues OpCode Metadata → Option (MetadataValues OpCode Metadata))
    (guard : MetadataValues OpCode Metadata → Bool := fun _ => true) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value ty
      let rhs ← MatchProg.value ty
      let root ← MatchProg.root (.llvm .add) #[lhs, rhs] #[ty]
      let metadata ← MatchProg.inspectOperation (Outputs := Metadata) root.op inspect
      MatchProg.matchNative metadata guard
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
  unfoldPuddleBuilder
  run_tac
    let target ← Lean.Elab.Tactic.getMainTarget
    if (target.find? fun e => e.isAppOf ``Pattern.Builder ||
        e.isAppOf ``MetadataTuple.Shape.fresh).isSome then
      throwError "symbolic builder normalization left unexpanded metadata allocation"
  all_goals simp [← Array.toList_inj]

-- Probe the tactic boundary with opaque native callbacks. This checks normalization
-- without assuming that an arbitrary metadata rewrite is semantically valid.
example (_inspect : IRContext OpCode → OperationPtr → Option (MetadataValues OpCode Metadata))
    (_rewrite : MetadataValues OpCode Metadata → Option (MetadataValues OpCode Metadata))
    (_guard : MetadataValues OpCode Metadata → Bool) : True := by
  run_tac
    let saved ← Lean.Elab.Tactic.getGoals
    let type ← Lean.Elab.Term.elabTerm
      (← `(CTree.Pattern.Valid (rebuildWithMetadata $(Lean.mkIdent `_inspect)
        $(Lean.mkIdent `_rewrite) $(Lean.mkIdent `_guard)))) none
    let probe ← Lean.Meta.mkFreshExprMVar type
    Lean.Elab.Tactic.setGoals [probe.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      unfold rebuildWithMetadata
      simpPuddleValid program sym =>
        puddleNoAssignments)))
    unless (← Lean.Elab.Tactic.getGoals).length == 1 do
      throwError "validity normalization must leave exactly the semantic obligation"
    let rewrite ← Lean.Elab.Term.elabTerm (Lean.mkIdent `_rewrite) none
    let guard ← Lean.Elab.Term.elabTerm (Lean.mkIdent `_guard) none
    let mut hasInterpreter := false
    for goal in ← Lean.Elab.Tactic.getGoals do
      let type ← goal.getType
      unless type.containsFVar rewrite.fvarId! && type.containsFVar guard.fvarId! do
        throwError "native normalization erased a callback or its guard"
      hasInterpreter := hasInterpreter || (type.find? (·.isAppOf ``Veir.CTree.interpretOp')).isSome
    unless hasInterpreter do
      throwError "native normalization unfolded the operation interpreter"
    Lean.Elab.Tactic.setGoals saved
  trivial

end PuddleSymbolicBuilderTest

namespace CTreeExecutionTest

-- Ordinary CTree bind does not execute a continuation after an abort.
example (next : Nat → Tree Unit) : CTree.bind (ub : Tree Nat) next = ub := by
  simp

example (next : Nat → Tree Unit) : CTree.bind (fail : Tree Nat) next = fail := by
  simp

-- Execution preserves every choice until simulation compares the trees.
example (next : BitVec 8 → Tree Nat) :
    (do
      let bits ← CTree.CTree.choose (E := ErrorE ⊕ₑ CTree.UBE) (C := FreezeC) (SubC := FreezeC) (FreezeCIn.mk 8)
      next bits) =
    CTree.CTree.tauG (C := FreezeC) (.inr (FreezeCIn.mk 8)) next := by
  simp [CTree.CTree.choose_def, CTree.CTree.tau_def, Bind.bind]

-- Both kinds of source abort permit any target, including an arbitrary continuation.
example (target : Tree Nat) : CTree.Sim Eq target (ub : Tree Nat) := by
  simp

example (target : Tree Nat) : CTree.Sim Eq target (fail : Tree Nat) := by
  simp

-- The sum instance classifies both terminal effects as UB.
example : CTree.HasUB.isUB (Sum.inl ErrorEIn.mk : ErrorEIn ⊕ CTree.UBEIn) := by
  trivial

example : CTree.HasUB.isUB (Sum.inr CTree.UBEIn.mk : ErrorEIn ⊕ CTree.UBEIn) := by
  trivial

-- Simulation's bind rule remains available for compositional proofs.
example (left right : Tree Nat) (next next' : Nat → Tree Nat)
    (head : CTree.Sim Eq left right)
    (tail : ∀ value, CTree.Sim Eq (next value) (next' value)) :
    CTree.Sim Eq (left >>= next) (right >>= next') := by
  apply CTree.Sim.bind _ _ _ _ head
  rintro x y rfl
  exact tail x

end CTreeExecutionTest

namespace CTreeSimPrintingTest

open Lean Elab Tactic

private meta def checkDoNotation (leftLength rightLength : Nat) : TacticM Unit :=
  withMainContext do
    let target ← getMainTarget
    let stx ← PrettyPrinter.delab target
    let `(term| $_ $_ $left $right) := stx
      | throwError "expected a simulation application, got {stx}"
    let `(term| do $left:doSeqItem*) := left
      | throwError "expected do notation in the left argument, got {stx}"
    let `(term| do $right:doSeqItem*) := right
      | throwError "expected do notation in both simulation arguments, got {stx}"
    unless left.size == leftLength && right.size == rightLength do
      throwError "expected flattened do sequences, got {stx}"
    let recovered ← Term.elabTerm stx (some (mkSort .zero))
    unless ← Meta.isDefEq recovered target do
      throwError "displayed simulation does not elaborate to the original expression"
    for (option, value) in [( `pp.explicit, true), (`pp.notation, false)] do
      let raw ← withOptions (·.setBool option value) (PrettyPrinter.delab target)
      if raw == stx then
        throwError "simulation printer ignored {option}"

-- Both concrete CTree.bind and ordinary monadic bind flatten; unused values and
-- local lets must survive printing and elaboration without changing the program.
example (source target : Tree Nat) :
    CTree.Sim Eq target
      (CTree.bind source fun value => do
        let doubled := value + value
        let _ ← target
        pure doubled) →
    CTree.Sim Eq target
      (CTree.bind source fun value => do
        let doubled := value + value
        let _ ← target
        pure doubled) := by
  intro h
  run_tac checkDoNotation 1 4
  exact h

-- A named continuation is displayed as a bind followed by its application.
example (source : Tree Nat) (next : Nat → Tree Nat) :
    CTree.Sim Eq (CTree.bind source next) (pure 0 : Tree Nat) →
    CTree.Sim Eq (CTree.bind source next) (pure 0 : Tree Nat) := by
  intro h
  run_tac checkDoNotation 2 1
  exact h

end CTreeSimPrintingTest
