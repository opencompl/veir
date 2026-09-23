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

end PuddleSymbolicBuilderTest
