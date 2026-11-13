module

public import Veir.Interpreter.CTreeInterpreter
public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.ProvedMonotone
import all Veir.Interpreter.CTree

public section

/-!
# Refinement of interpreter trees

`Tree.Refines relation source target` says that every behavior of the target tree is simulated by
a behavior of the source tree, with returned values related by `relation`, source first. It is
`CTree.Sim` on the trees themselves, with its arguments reversed to Veir's source-to-target order.

This is the refinement the DCE proof archived in `Archive/dce-proof` is written against, except
that the archived version first reified terminal events as `Interp` outcomes and then had to assume
three facts as axioms: that undefined behavior admits every target, that refining loop bodies give
refining loops, and that opcodes are monotone. On the trees themselves all three are theorems, from
the simulation rules `CTree.Sim.ub` and `CTree.Sim.iter` and from the per-opcode monotonicity proofs
behind `OpCode.treeMonotoneProved`.
-/

namespace Veir.Tree

/-- Every target behavior is simulated by a source behavior, with results related by `relation`. -/
@[expose]
def Refines (relation : α → β → Prop) (source : Tree α) (target : Tree β) : Prop :=
  _root_.CTree.Sim (fun target source => relation source target) target source

/-- Returned values refine exactly when they are related. -/
theorem refines_pure (relation : α → β → Prop) (source : α) (target : β) :
    Refines relation (pure source) (pure target) ↔ relation source target := by
  simp [Refines]

/-- Weakening the relation on returned values preserves refinement. -/
theorem refines_mono {relation relation' : α → β → Prop} {source : Tree α} {target : Tree β}
    (h : Refines relation source target) (weaker : ∀ a b, relation a b → relation' a b) :
    Refines relation' source target :=
  _root_.CTree.Sim.mono h fun b a hab => weaker a b hab

/-- Undefined source behavior admits every target behavior. The archived proof assumed this as
`refines_ub`; on the trees themselves it is the simulation rule for undefined behavior. -/
theorem refines_ub (relation : α → β → Prop) (target : Tree β) :
    Refines relation (ub : Tree α) target := by
  simp [Refines]

/-- Source failure admits every target behavior, like undefined behavior. -/
theorem refines_fail (relation : α → β → Prop) (target : Tree β) :
    Refines relation (fail : Tree α) target := by
  simp [Refines]

/-- Related computations followed by related continuations are related. -/
theorem refines_bind {relation : α → β → Prop} {relation' : γ → δ → Prop}
    {source : Tree α} {target : Tree β} {next : α → Tree γ} {next' : β → Tree δ}
    (h : Refines relation source target)
    (hnext : ∀ a b, relation a b → Refines relation' (next a) (next' b)) :
    Refines relation' (source >>= next) (target >>= next') :=
  _root_.CTree.Sim.bind target source next' next h fun b a hab => hnext a b hab

/-- Refining loop bodies give refining loops from related loop states. The archived proof assumed
this as `refines_iter : IterationCompatible`; it is the simulation rule for iteration. -/
theorem refines_iter {ι κ α β : Type} (stateRelation : ι → κ → Prop) (relation : α → β → Prop)
    (bodySource : ι → Tree (ι ⊕ α)) (bodyTarget : κ → Tree (κ ⊕ β))
    (hbody : ∀ source target, stateRelation source target →
      Refines (Sum.LiftRel stateRelation relation) (bodySource source) (bodyTarget target))
    (source : ι) (target : κ) (hstate : stateRelation source target) :
    Refines relation (CTree.iter bodySource source) (CTree.iter bodyTarget target) := by
  unfold Refines at *
  refine _root_.CTree.Sim.iter (RRi := fun target source => stateRelation source target)
    bodyTarget bodySource target source hstate ?_
  intro target source hstate
  refine (hbody source target hstate).mono ?_
  intro _ _ h
  cases h <;> constructor <;> assumption

/-- Running an opcode on refined operands in refined memory refines running it on the originals.
The archived proof assumed this as `operation_monotonicity`; it is proved per opcode in the
dialects, see `OpCode.treeMonotoneProved`. -/
theorem operation_monotonicity (opType : OpCode) [Veir.CTree.InterpretOpTreeMonotone opType]
    (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (valuesSource valuesTarget : Array RuntimeValue)
    (memorySource memoryTarget : MemoryState) (regions : Array RegionPtr)
    (hvalues : valuesSource ⊒ valuesTarget) (hmemory : memorySource ⊒ memoryTarget) :
    Refines OperationResult.isRefinedBy
      (Veir.CTree.interpretOp' opType properties resultTypes valuesSource blockOperands
        memorySource regions)
      (Veir.CTree.interpretOp' opType properties resultTypes valuesTarget blockOperands
        memoryTarget regions) :=
  Veir.CTree.InterpretOpTreeMonotone.monotone properties resultTypes valuesSource valuesTarget
    blockOperands memorySource memoryTarget regions hvalues hmemory

/-- `operation_monotonicity` for every opcode in `OpCode.treeMonotoneProved`. -/
theorem operation_monotonicity_of_treeMonotoneProved (opType : OpCode)
    (hproved : opType.treeMonotoneProved = true)
    (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (valuesSource valuesTarget : Array RuntimeValue)
    (memorySource memoryTarget : MemoryState) (regions : Array RegionPtr)
    (hvalues : valuesSource ⊒ valuesTarget) (hmemory : memorySource ⊒ memoryTarget) :
    Refines OperationResult.isRefinedBy
      (Veir.CTree.interpretOp' opType properties resultTypes valuesSource blockOperands
        memorySource regions)
      (Veir.CTree.interpretOp' opType properties resultTypes valuesTarget blockOperands
        memoryTarget regions) :=
  have := OpCode.interpretOpTreeMonotone_of_treeMonotoneProved hproved
  operation_monotonicity opType properties resultTypes blockOperands valuesSource valuesTarget
    memorySource memoryTarget regions hvalues hmemory

end Veir.Tree

end
