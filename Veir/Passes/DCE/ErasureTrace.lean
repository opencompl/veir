module

public import Veir.Passes.DCE.Structure

public section

namespace Veir.DCE

/-- A chronological list of actual DCE deletions, with each deletion's local
deadness proof retained. The newest deletion is appended at the right. -/
inductive ErasureTrace : WfIRContext OpCode → List OperationPtr → WfIRContext OpCode → Prop where
  | nil (ctx) : ErasureTrace ctx [] ctx
  | snoc {source middle operations} (trace : ErasureTrace source operations middle)
      (operation : OperationPtr) (inBounds : operation.InBounds middle.raw)
      (dead : operation.isTriviallyDead middle.raw) :
      ErasureTrace source (operations ++ [operation])
        (WfRewriter.eraseOp middle operation dead.1 dead.2.1 inBounds)

theorem ErasureTrace.erasures {source target : WfIRContext OpCode} {operations}
    (trace : ErasureTrace source operations target) : Erasures source target := by
  induction trace with
  | nil => exact .refl _
  | snoc trace operation inBounds dead ih => exact .tail ih (.erase _ operation inBounds dead)

theorem Erasures.exists_trace {source target : WfIRContext OpCode}
    (erases : Erasures source target) : ∃ operations, ErasureTrace source operations target := by
  induction erases with
  | refl => exact ⟨[], .nil _⟩
  | tail previous step ih =>
    obtain ⟨operations, trace⟩ := ih
    cases step with
    | erase operation inBounds dead => exact ⟨operations ++ [operation], .snoc trace operation inBounds dead⟩

theorem ErasureTrace.deleted_iff {source target : WfIRContext OpCode} {operations}
    (trace : ErasureTrace source operations target) (operation : OperationPtr)
    (original : operation.InBounds source.raw) :
    operation ∈ operations ↔ ¬operation.InBounds target.raw := by
  classical
  induction trace with
  | nil => simp [original]
  | snoc trace removed inBounds dead ih =>
    rw [List.mem_append, List.mem_singleton, ih,
      eraseOp_inBounds_iff _ removed operation inBounds dead]
    grind

theorem ErasureTrace.original_inBounds {source target : WfIRContext OpCode} {operations}
    (trace : ErasureTrace source operations target) (operation : OperationPtr)
    (member : operation ∈ operations) : operation.InBounds source.raw := by
  induction trace with
  | nil => simp at member
  | snoc trace removed inBounds dead ih =>
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with earlier | rfl
    · exact ih earlier
    · exact trace.erasures.operation_inBounds operation inBounds

theorem ErasureTrace.nodup {source target : WfIRContext OpCode} {operations}
    (trace : ErasureTrace source operations target) : operations.Nodup := by
  induction trace with
  | nil => simp
  | @snoc middle operations trace removed inBounds dead ih =>
    have original := trace.erasures.operation_inBounds removed inBounds
    have fresh : removed ∉ operations := by
      intro member
      exact ((trace.deleted_iff removed original).mp member) inBounds
    simp [List.nodup_append, ih]
    intro operation member same
    subst operation
    exact fresh member

theorem ErasureTrace.eligible {source target : WfIRContext OpCode} {operations}
    (trace : ErasureTrace source operations target) (operation : OperationPtr)
    (member : operation ∈ operations) : Eligible source.raw operation :=
  trace.erasures.deleted_eligible operation (trace.original_inBounds operation member)
    ((trace.deleted_iff operation (trace.original_inBounds operation member)).mp member)

end Veir.DCE
