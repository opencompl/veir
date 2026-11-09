module

public import Veir.PatternRewriter.Puddle.ExecutionLemmas
public import Veir.PatternRewriter.Puddle.ExecutionBounds
import all Veir.PatternRewriter.Puddle.CreationOperationSemantics
public import Veir.Rewriter.WfRewriter.GetSet
public import Veir.Rewriter.WfRewriter.InBounds
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Semantics
import all Veir.Rewriter.WfRewriter.Basic

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Creating an operation introduces precisely its operation pointer among operation pointers. -/
theorem operation_inBounds_createOp
    {ctx newCtx : WfIRContext OpInfo} {code : OpInfo} {types : Array TypeAttr}
    {operands : Array ValuePtr} {properties : propertiesOf code} {newOp : OperationPtr}
    {hin : ∀ operand ∈ operands, operand.InBounds ctx.raw}
    (h : WfRewriter.createOp ctx code types operands #[] #[] properties none hin = some (newCtx, newOp))
    (op : OperationPtr) : op.InBounds newCtx.raw ↔ op.InBounds ctx.raw ∨ op = newOp := by
  unfold WfRewriter.createOp at h
  split at h
  · contradiction
  · rename_i raw allocated hraw
    cases h
    have hbounds := Rewriter.createOp_inBounds (.operation op) hraw
    simpa using hbounds

/-- Old operations retain their parent, links, successors and regions under unattached allocation. -/
theorem WfIRContext.WithCreatedOps.structural_fields {ctx ctx' : WfIRContext OpInfo}
    (h : Veir.WfIRContext.WithCreatedOps ctx ctx') (op : OperationPtr) (hop : op.InBounds ctx.raw) :
    op.getParent! ctx'.raw = op.getParent! ctx.raw ∧
    op.getPrevOp! ctx'.raw = op.getPrevOp! ctx.raw ∧
    op.getNextOp! ctx'.raw = op.getNextOp! ctx.raw ∧
    op.getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw ∧
    op.getNumRegions! ctx'.raw = op.getNumRegions! ctx.raw := by
  induction h with
  | Nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | @CreatedOp newOp ctx₁ ctx₂ ctx₃ hprev hcreate ih =>
    have ih := ih hop
    obtain ⟨code, types, operands, successors, regions, properties, h₁, h₂, h₃, h₄, hcreate⟩ := hcreate
    have hbound := hprev.inBounds_mono (.operation op) hop
    have hfresh := WfRewriter.createOp_new_not_inBounds newOp hcreate
    have hne : op ≠ newOp := by grind
    have hp := OperationPtr.getParent!_WfRewriter_createOp hcreate (operation := op)
    have hv := OperationPtr.getPrevOp!_WfRewriter_createOp hcreate (operation := op)
    have hn := OperationPtr.getNextOp!_WfRewriter_createOp hcreate (operation := op)
    have hs := OperationPtr.getSuccessors!_WfRewriter_createOp hcreate (operation := op)
    have hr := OperationPtr.getNumRegions!_WfRewriter_createOp hcreate (operation := op)
    exact ⟨by simpa [hne, ih.1] using hp,
      by simpa [hne, ih.2.1] using hv,
      by simpa [hne, ih.2.2.1] using hn,
      by simpa [hne, ih.2.2.2.1] using hs,
      by simpa [hne, ih.2.2.2.2] using hr⟩

/-- Fresh Puddle operations have no structural attachments or nested control-flow structure. -/
def DetachedCreation (op : OperationPtr) (ctx : IRContext OpInfo) : Prop :=
  op.getParent! ctx = none ∧ op.getPrevOp! ctx = none ∧ op.getNextOp! ctx = none ∧
    op.getSuccessors! ctx = #[] ∧ op.getNumRegions! ctx = 0

/-- Later unattached allocation preserves these properties of an existing operation. -/
theorem DetachedCreation.withCreatedOps {ctx ctx' : WfIRContext OpInfo}
    {op : OperationPtr} (hp : DetachedCreation op ctx.raw)
    (h : Veir.WfIRContext.WithCreatedOps ctx ctx') (hop : op.InBounds ctx.raw) :
    DetachedCreation op ctx'.raw := by
  obtain ⟨hparent, hprev, hnext, hsuccessors, hregions⟩ :=
    WfIRContext.WithCreatedOps.structural_fields h op hop
  simpa [DetachedCreation, hparent, hprev, hnext, hsuccessors, hregions] using hp

/-- Each individual creation returns exactly its new pointers, without duplicates or attachments. -/
theorem CreateDecl.run_structure (decl : CreateDecl OpInfo)
    {ctx newCtx : WfIRContext OpInfo} {a b : Assignment OpInfo} {newOps : Array OperationPtr}
    (h : decl.run a ctx = some (newCtx, newOps, b)) :
    (∀ op, op ∈ newOps ↔ op.InBounds newCtx.raw ∧ ¬op.InBounds ctx.raw) ∧
    newOps.toList.Nodup ∧
    (∀ op ∈ newOps, DetachedCreation op newCtx.raw) := by
  cases decl with
  | operation code operandHandles typeHandles propertyHandle opHandle resultHandles =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨operands, hop, types, hty, properties, hprop, u, hguard, h⟩ := h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨createdCtx, op⟩, hcreate, bound, hbindop, final, hbindresults, heq⟩ := h
      cases heq
      have hnew := WfRewriter.createOp_new_inBounds op hcreate
      have hfresh := WfRewriter.createOp_new_not_inBounds op hcreate
      refine ⟨?_, by simp, ?_⟩
      · intro queried
        have hbounds := operation_inBounds_createOp hcreate queried
        simp only [Array.mem_singleton]
        grind
      · intro queried hmem
        simp only [Array.mem_singleton] at hmem
        subst queried
        have hp := OperationPtr.getParent!_WfRewriter_createOp hcreate (operation := op)
        have hv := OperationPtr.getPrevOp!_WfRewriter_createOp hcreate (operation := op)
        have hn := OperationPtr.getNextOp!_WfRewriter_createOp hcreate (operation := op)
        have hs := OperationPtr.getSuccessors!_WfRewriter_createOp hcreate (operation := op)
        have hr := OperationPtr.getNumRegions!_WfRewriter_createOp hcreate (operation := op)
        simpa [DetachedCreation] using And.intro hp (And.intro hv (And.intro hn (And.intro hs hr)))
    · contradiction
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨bound, hb, heq⟩ := h
    cases heq
    simp
  | property code value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨bound, hb, heq⟩ := h
    cases heq
    simp
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨values, _, outValues, _, bound, hb, heq⟩ := h
    cases heq
    simp

/-- Creation returns exactly all newly allocated operations, once each, still detached. -/
theorem CreateProg.runDecls_structure (decls : List (CreateDecl OpInfo))
    {ctx newCtx : WfIRContext OpInfo} {a b : Assignment OpInfo} {newOps : Array OperationPtr}
    (h : CreateProg.runDecls decls ctx a = some (newCtx, newOps, b)) :
    (∀ op, op ∈ newOps ↔ op.InBounds newCtx.raw ∧ ¬op.InBounds ctx.raw) ∧
    newOps.toList.Nodup ∧
    (∀ op ∈ newOps, DetachedCreation op newCtx.raw) := by
  induction decls generalizing ctx a newOps with
  | nil =>
    simp only [CreateProg.runDecls, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | cons decl decls ih =>
    simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨middleCtx, created, middle⟩, hd, ⟨finalCtx, restOps, final⟩, hr, heq⟩ := h
    cases heq
    obtain ⟨hexactd, hnodupd, hdetachedd⟩ := decl.run_structure hd
    obtain ⟨hexactr, hnodupr, hdetachedr⟩ := ih hr
    have hctxd := decl.run_withCreatedOps _ _ _ _ _ hd
    have hctxr := CreateProg.runDecls_withCreatedOps _ _ _ _ _ _ hr
    have hmonod (op : OperationPtr) (hop : op.InBounds ctx.raw) : op.InBounds middleCtx.raw :=
      hctxd.inBounds_mono (.operation op) hop
    have hmonor (op : OperationPtr) (hop : op.InBounds middleCtx.raw) : op.InBounds finalCtx.raw :=
      hctxr.inBounds_mono (.operation op) hop
    refine ⟨?_, ?_, ?_⟩
    · intro op
      simp only [Array.mem_append]
      have hd := hexactd op
      have hr := hexactr op
      grind
    · simp only [Array.toList_append, List.nodup_append]
      refine ⟨hnodupd, hnodupr, ?_⟩
      intro op hd op' hr heq
      have hop := (hexactd op).mp (by simpa using hd)
      have hop' := (hexactr op').mp (by simpa using hr)
      subst op'
      exact hop'.2 hop.1
    · intro op hmem
      rcases Array.mem_append.mp hmem with hd | hr
      · exact (hdetachedd op hd).withCreatedOps hctxr ((hexactd op).mp hd).1
      · exact hdetachedr op hr

/-- The public creation runner satisfies the complete allocation and detachment contract. -/
theorem CreateProg.run_structure (prog : CreateProg OpInfo α)
    {ctx newCtx : WfIRContext OpInfo} {a b : Assignment OpInfo} {newOps : Array OperationPtr}
    (h : prog.run a ctx = some (newCtx, newOps, b)) :
    (∀ op, op ∈ newOps ↔ op.InBounds newCtx.raw ∧ ¬op.InBounds ctx.raw) ∧
    newOps.toList.Nodup ∧ (∀ op ∈ newOps, DetachedCreation op newCtx.raw) :=
  CreateProg.runDecls_structure prog.decls h

/-- Successful local interpretation exposes precisely the creation runner's fresh operations. -/
theorem Pattern.interpret_structure (rule : Pattern OpCode)
    {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (h : rule.interpret ctx root = some (newCtx, some (newOps, newValues))) :
    (∀ op, op ∈ newOps ↔ op.InBounds newCtx.raw ∧ ¬op.InBounds ctx.raw) ∧
    newOps.toList.Nodup ∧ (∀ op ∈ newOps, DetachedCreation op newCtx.raw) := by
  unfold Pattern.interpret at h
  split at h
  · simp_all
  · split at h
    · contradiction
    · rename_i matched hmatch createdCtx createdOps finalAssignment hcreate
      split at h
      · contradiction
      · cases h
        exact rule.creation.run_structure hcreate

/-- Puddle interpretation returns exactly the operations allocated by creation. -/
theorem Pattern.interpret_returnOps (rule : Pattern OpCode) :
    LocalRewritePattern.ReturnOps rule.interpret := by
  intro ctx root newCtx newOps newValues h
  exact (rule.interpret_structure h).1

/-- Puddle interpretation returns pairwise distinct operations for insertion by the driver. -/
theorem Pattern.interpret_returnOpsNodup (rule : Pattern OpCode) :
    LocalRewritePattern.ReturnOpsNodup rule.interpret := by
  intro ctx root newCtx newOps newValues h
  exact (rule.interpret_structure h).2.1

/-- Creating a program leaves the old operation graph's parent/link/control-flow fields intact. -/
theorem CreateProg.run_structural_fields (prog : CreateProg OpInfo α)
    {ctx newCtx : WfIRContext OpInfo} {a b : Assignment OpInfo} {newOps : Array OperationPtr}
    (h : prog.run a ctx = some (newCtx, newOps, b))
    (op : OperationPtr) (hop : op.InBounds ctx.raw) :
    op.getParent! newCtx.raw = op.getParent! ctx.raw ∧
    op.getPrevOp! newCtx.raw = op.getPrevOp! ctx.raw ∧
    op.getNextOp! newCtx.raw = op.getNextOp! ctx.raw ∧
    op.getSuccessors! newCtx.raw = op.getSuccessors! ctx.raw ∧
    op.getNumRegions! newCtx.raw = op.getNumRegions! ctx.raw :=
  WfIRContext.WithCreatedOps.structural_fields (prog.run_withCreatedOps _ _ _ _ _ h) op hop

/-- Creation lists preserve valid SSA-value bindings. -/
theorem CreateProg.valuesInBounds_of_runDecls (decls : List (CreateDecl OpCode))
    {ctx newCtx : WfIRContext OpCode} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (ha : a.ValuesInBounds ctx.raw)
    (h : CreateProg.runDecls decls ctx a = some (newCtx, newOps, b)) :
    b.ValuesInBounds newCtx.raw := by
  induction decls generalizing ctx a newOps with
  | nil => cases h; exact ha
  | cons decl decls ih =>
    simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨middleCtx, created, middle⟩, hd, ⟨finalCtx, restOps, final⟩, hr, heq⟩ := h
    cases heq
    exact ih (decl.valuesInBounds_of_run ha hd) hr

/-- Read a valid SSA value from a bounds-respecting assignment. -/
theorem Assignment.ValuesInBounds.getValue {a : Assignment OpCode} {ctx : IRContext OpCode}
    (ha : a.ValuesInBounds ctx) {handle : Handle OpCode .value} {value : ValuePtr}
    (h : a.getValue handle = some value) : value.InBounds ctx := by
  unfold Assignment.getValue at h
  split at h <;> try contradiction
  cases h
  exact ha handle.id _ (by assumption)

/-- Every pointer obtained by successful replacement lookup is valid. -/
theorem Assignment.ValuesInBounds.getValues {a : Assignment OpCode} {ctx : IRContext OpCode}
    (ha : a.ValuesInBounds ctx) {handles : Array (Handle OpCode .value)} {values : Array ValuePtr}
    (h : a.getValues handles = some values) : ∀ value ∈ values, value.InBounds ctx := by
  have hlist : handles.toList.mapM a.getValue = some values.toList := by
    simp only [Assignment.getValues, Array.mapM_eq_mapM_toList] at h
    cases hm : handles.toList.mapM a.getValue with
    | none => simp [hm] at h
    | some vals =>
      rw [hm] at h
      change some vals.toArray = some values at h
      cases h
      rfl
  have hbound (hs : List (Handle OpCode .value)) (vs : List ValuePtr)
      (h : hs.mapM a.getValue = some vs) : ∀ value ∈ vs, value.InBounds ctx := by
    induction hs generalizing vs with
    | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst vs; simp
    | cons head tail ih =>
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def] at h
      obtain ⟨value, hv, rest, hr, heq⟩ := h
      cases heq
      intro v hmem
      rcases List.mem_cons.mp hmem with rfl | ht
      · exact ha.getValue hv
      · exact ih rest hr v ht
  intro value hm
  exact hbound _ _ hlist value (by simpa using hm)

/-- With an in-bounds input root, successful interpretation returns only in-bounds values. -/
theorem Pattern.interpret_returnValuesInBounds_of_root (rule : Pattern OpCode)
    {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    (hroot : root.InBounds ctx.raw) {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (h : rule.interpret ctx root = some (newCtx, some (newOps, newValues))) :
    ∀ value ∈ newValues, value.InBounds newCtx.raw := by
  unfold Pattern.interpret at h
  split at h
  · simp_all
  · rename_i assignment hmatch
    split at h
    · contradiction
    · rename_i createdCtx createdOps finalAssignment hcreate
      split at h
      · contradiction
      · rename_i returned hvalues
        cases h
        have hb := (rule.matcher.inBounds_of_run hroot hmatch).values
        have hf := CreateProg.valuesInBounds_of_runDecls rule.creation.decls hb hcreate
        exact hf.getValues hvalues

end

end Veir.Puddle
