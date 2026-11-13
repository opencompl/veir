module

public import Veir.Passes.DCE.Erasure
public import Veir.Rewriter.WfRewriter.GetSet
import all Veir.Interfaces.SideEffectInterfaces
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.Rewriter.Basic
import all Veir.IR.Basic

public section

namespace Veir.DCE

theorem Erasures.operation_inBounds {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) : operation.InBounds source.raw := by
  induction erases with
  | refl => exact survivor
  | tail previous step ih =>
    cases step with
    | erase deleted inBounds dead =>
      exact ih ((eraseOp_inBounds_iff _ deleted operation inBounds dead).mp survivor).1

/-- Lift any observation preserved by one deletion to the original context,
using only survival of the observed operation in the final context. -/
theorem Erasures.survivor_observation {α : Type} (observe : IRContext OpCode → OperationPtr → α)
    (stable : ∀ (ctx : WfIRContext OpCode) deleted
      (inBounds : deleted.InBounds ctx.raw) (dead : deleted.isTriviallyDead ctx.raw) other,
      other.InBounds (WfRewriter.eraseOp ctx deleted dead.1 dead.2.1 inBounds).raw →
      observe (WfRewriter.eraseOp ctx deleted dead.1 dead.2.1 inBounds).raw other =
        observe ctx.raw other)
    {source target : WfIRContext OpCode} (erases : Erasures source target)
    (operation : OperationPtr) (survivor : operation.InBounds target.raw) :
    observe target.raw operation = observe source.raw operation := by
  induction erases with
  | refl => rfl
  | tail previous step ih =>
    cases step with
    | erase deleted inBounds dead =>
      rw [stable _ deleted inBounds dead operation survivor]
      exact ih ((eraseOp_inBounds_iff _ deleted operation inBounds dead).mp survivor).1

theorem Erasures.getOpType {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getOpType! target.raw = operation.getOpType! source.raw :=
  erases.survivor_observation (fun ctx op => op.getOpType! ctx)
    (fun _ _ _ _ _ hs => by simp [hs]) operation survivor

theorem Erasures.getProperties {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) (opcode : OpCode) :
    operation.getProperties! target.raw opcode = operation.getProperties! source.raw opcode :=
  erases.survivor_observation (fun ctx op => op.getProperties! ctx opcode)
    (fun _ _ _ _ _ hs => by simp [hs]) operation survivor

theorem Erasures.getResultTypes {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getResultTypes! target.raw = operation.getResultTypes! source.raw :=
  erases.survivor_observation (fun ctx op => op.getResultTypes! ctx)
    (fun _ _ _ _ _ hs => by simp [hs]) operation survivor

theorem Erasures.getOperands {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getOperands! target.raw = operation.getOperands! source.raw :=
  erases.survivor_observation (fun ctx op => op.getOperands! ctx)
    (fun _ _ _ _ _ hs => by simp [hs]) operation survivor

theorem Erasures.getSuccessors {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getSuccessors! target.raw = operation.getSuccessors! source.raw :=
  erases.survivor_observation (fun ctx op => op.getSuccessors! ctx)
    (fun _ _ _ _ _ hs => by simp [hs]) operation survivor

theorem Erasures.getNumRegions {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getNumRegions! target.raw = operation.getNumRegions! source.raw :=
  erases.survivor_observation (fun ctx op => op.getNumRegions! ctx)
    (fun _ _ _ _ _ hs => by simp [hs]) operation survivor

theorem Erasures.getRegion {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) (index : Nat) :
    operation.getRegion! target.raw index = operation.getRegion! source.raw index :=
  erases.survivor_observation (fun ctx op => op.getRegion! ctx index)
    (fun _ _ _ _ _ hs => by simp [hs]) operation survivor

theorem Erasures.getAttributes {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getAttributes! target.raw = operation.getAttributes! source.raw :=
  erases.survivor_observation (fun ctx op => op.getAttributes! ctx)
    (fun _ _ _ _ _ hs => by simp [hs]) operation survivor

theorem Erasures.getEffects {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getEffects target.raw = operation.getEffects source.raw := by
  simp only [OperationPtr.getEffects, erases.getNumRegions operation survivor,
    erases.getProperties operation survivor]
  rw [erases.getOpType operation survivor]

theorem Erasures.getRegions {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getRegions! target.raw = operation.getRegions! source.raw := by
  ext index ht hs
  · simpa only [OperationPtr.getRegions!.size_eq_getNumRegions!] using
      erases.getNumRegions operation survivor
  · simpa only [OperationPtr.getRegions!.getElem_eq_getRegion!] using
      erases.getRegion operation survivor index

theorem Erasures.getParent {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getParent! target.raw = operation.getParent! source.raw := by
  apply erases.survivor_observation (fun ctx op => op.getParent! ctx) _ operation survivor
  intro ctx deleted inBounds dead other hs
  have different := ((eraseOp_inBounds_iff ctx deleted other inBounds dead).mp hs).2
  simp [OperationPtr.getParent!_wfRewriter_eraseOp hs, different]

/-- Region-bearing operations, in particular function bodies and modules,
cannot occur among the regionless operations in an erasure sequence. -/
theorem Erasures.region_bearing_survives {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (inBounds : operation.InBounds source.raw)
    (hasRegions : operation.getNumRegions! source.raw ≠ 0) : operation.InBounds target.raw := by
  induction erases with
  | refl => exact inBounds
  | tail previous step ih =>
    cases step with
    | erase deleted deletedIn dead =>
      have different : operation ≠ deleted := by
        intro equal
        subst deleted
        exact hasRegions ((previous.getNumRegions operation ih).symm.trans dead.1)
      exact (eraseOp_inBounds_iff _ deleted operation deletedIn dead).mpr ⟨ih, different⟩

/-- Eligibility facts that may be transported back to the original program.
Unusedness is deliberately absent: an earlier deleted user can make an
operation dead only later in the deletion sequence. -/
def Eligible (ctx : IRContext OpCode) (operation : OperationPtr) : Prop :=
  operation.getNumRegions! ctx = 0 ∧ !(operation.getEffects ctx).writes ∧
    !(operation.getEffects ctx).allocates ∧ !HasOpInfo.isTerminator (operation.getOpType! ctx)

theorem Eligible.of_dead {ctx : IRContext OpCode} {operation : OperationPtr}
    (dead : operation.isTriviallyDead ctx) : Eligible ctx operation :=
  ⟨dead.1, dead.2.2.1, dead.2.2.2.1, dead.2.2.2.2⟩

theorem Erasures.eligible_iff {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    Eligible target.raw operation ↔ Eligible source.raw operation := by
  simp only [Eligible, erases.getNumRegions operation survivor,
    erases.getEffects operation survivor, erases.getOpType operation survivor]

theorem Erasures.deleted_eligible {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (original : operation.InBounds source.raw) (deleted : ¬operation.InBounds target.raw) :
    Eligible source.raw operation := by
  induction erases with
  | refl => contradiction
  | @tail middle final previous step ih =>
    cases step with
    | erase removed removedIn dead =>
      by_cases survives : operation.InBounds middle.raw
      · have same : operation = removed := by
          by_cases same : operation = removed
          · exact same
          · exact False.elim (deleted ((eraseOp_inBounds_iff _ removed operation removedIn dead).mpr
              ⟨survives, same⟩))
        subst operation
        exact (previous.eligible_iff removed survives).mp (.of_dead dead)
      · exact ih survives

/-- Lift observations unaffected by any deletion, including region and block
metadata, across the whole finite sequence. -/
theorem Erasures.context_observation {α : Type} (observe : IRContext OpCode → α)
    (stable : ∀ (ctx : WfIRContext OpCode) deleted
      (inBounds : deleted.InBounds ctx.raw) (dead : deleted.isTriviallyDead ctx.raw),
      observe (WfRewriter.eraseOp ctx deleted dead.1 dead.2.1 inBounds).raw = observe ctx.raw)
    {source target : WfIRContext OpCode} (erases : Erasures source target) :
    observe target.raw = observe source.raw := by
  induction erases with
  | refl => rfl
  | tail previous step ih =>
    cases step with
    | erase removed inBounds dead => rw [stable _ removed inBounds dead, ih]

theorem Erasures.block_inBounds_iff {source target : WfIRContext OpCode}
    (erases : Erasures source target) (block : BlockPtr) :
    block.InBounds target.raw ↔ block.InBounds source.raw := by
  have equal : block.InBounds target.raw = block.InBounds source.raw :=
    erases.context_observation (fun ctx => block.InBounds ctx) (by
      intro ctx removed inBounds dead
      simp only [WfRewriter.eraseOp]
      exact propext (Rewriter.eraseOp_inBounds (.block block) trivial))
  rw [equal]

theorem Erasures.region_inBounds_iff {source target : WfIRContext OpCode}
    (erases : Erasures source target) (region : RegionPtr) :
    region.InBounds target.raw ↔ region.InBounds source.raw := by
  have equal : region.InBounds target.raw = region.InBounds source.raw :=
    erases.context_observation (fun ctx => region.InBounds ctx) (by
      intro ctx removed inBounds dead
      simp only [WfRewriter.eraseOp]
      exact propext (Rewriter.eraseOp_inBounds (.region region) trivial))
  rw [equal]

theorem Erasures.block_parent {source target : WfIRContext OpCode}
    (erases : Erasures source target) (block : BlockPtr) :
    block.getParent! target.raw = block.getParent! source.raw :=
  erases.context_observation (fun ctx => block.getParent! ctx) (by intros; simp)

theorem Erasures.block_next {source target : WfIRContext OpCode}
    (erases : Erasures source target) (block : BlockPtr) :
    block.getNextBlock! target.raw = block.getNextBlock! source.raw :=
  erases.context_observation (fun ctx => block.getNextBlock! ctx) (by intros; simp)

theorem Erasures.block_prev {source target : WfIRContext OpCode}
    (erases : Erasures source target) (block : BlockPtr) :
    block.getPrevBlock! target.raw = block.getPrevBlock! source.raw :=
  erases.context_observation (fun ctx => block.getPrevBlock! ctx) (by intros; simp)

theorem Erasures.block_numArguments {source target : WfIRContext OpCode}
    (erases : Erasures source target) (block : BlockPtr) :
    block.getNumArguments! target.raw = block.getNumArguments! source.raw :=
  erases.context_observation (fun ctx => block.getNumArguments! ctx) (by intros; simp)

theorem Erasures.region_parent {source target : WfIRContext OpCode}
    (erases : Erasures source target) (region : RegionPtr) :
    region.getParent! target.raw = region.getParent! source.raw :=
  erases.context_observation (fun ctx => region.getParent! ctx) (by intros; simp)

theorem Erasures.region_firstBlock {source target : WfIRContext OpCode}
    (erases : Erasures source target) (region : RegionPtr) :
    region.getFirstBlock! target.raw = region.getFirstBlock! source.raw :=
  erases.context_observation (fun ctx => region.getFirstBlock! ctx) (by intros; simp)

theorem Erasures.region_lastBlock {source target : WfIRContext OpCode}
    (erases : Erasures source target) (region : RegionPtr) :
    region.getLastBlock! target.raw = region.getLastBlock! source.raw :=
  erases.context_observation (fun ctx => region.getLastBlock! ctx) (by intros; simp)

theorem Erasures.getParentOp {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    operation.getParentOp! target.raw = operation.getParentOp! source.raw := by
  simp only [OperationPtr.getParentOp!, OperationPtr.getParentRegion!, erases.getParent operation survivor,
    erases.block_parent, erases.region_parent]

theorem Erasures.value_inBounds {source target : WfIRContext OpCode}
    (erases : Erasures source target) (value : ValuePtr)
    (survivor : value.InBounds target.raw) : value.InBounds source.raw := by
  induction erases with
  | refl => exact survivor
  | tail previous step ih =>
    cases step with
    | erase removed inBounds dead =>
      apply ih
      cases value with
      | opResult result =>
        have owner : result.op.InBounds (WfRewriter.eraseOp _ removed dead.1 dead.2.1 inBounds).raw := by
          grind
        have different := ((eraseOp_inBounds_iff _ removed result.op inBounds dead).mp owner).2
        exact (Rewriter.eraseOp_inBounds (.value (.opResult result)) different).mp survivor
      | blockArgument argument =>
        exact (Rewriter.eraseOp_inBounds (.value (.blockArgument argument)) trivial).mp survivor

theorem Erasures.value_getType {source target : WfIRContext OpCode}
    (erases : Erasures source target) (value : ValuePtr) (survivor : value.InBounds target.raw) :
    value.getType! target.raw = value.getType! source.raw := by
  induction erases with
  | refl => rfl
  | @tail middle final previous step ih =>
    cases step with
    | erase removed inBounds dead =>
      rw [ValuePtr.getType!_wfRewriter_eraseOp survivor]
      exact ih ((Erasures.single (.erase middle removed inBounds dead)).value_inBounds value survivor)

theorem Erasures.block_argumentTypes {source target : WfIRContext OpCode}
    (erases : Erasures source target) (block : BlockPtr) (inBounds : block.InBounds source.raw) :
    block.getArgumentTypes! target.raw = block.getArgumentTypes! source.raw := by
  have targetBounds := (erases.block_inBounds_iff block).mpr inBounds
  ext index ht hs
  · simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using
      erases.block_numArguments block
  · have ht' : index < block.getNumArguments! target.raw := by
      simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using ht
    have hs' : index < block.getNumArguments! source.raw := by
      simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using hs
    rw [BlockPtr.getArgumentTypes!.getElem_eq_getArgument ht',
      BlockPtr.getArgumentTypes!.getElem_eq_getArgument hs']
    have valueBounds : (ValuePtr.blockArgument (block.getArgument index)).InBounds target.raw := by
      grind
    exact erases.value_getType (.blockArgument (block.getArgument index)) valueBounds

end Veir.DCE
