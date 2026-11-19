module

public import Veir.Passes.InstructionSelection.Branches.Frame
public import Veir.Passes.Legalization.LegalizerHelper
public import Veir.Passes.Legalization.Validity.PhiAllocation

import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.IR.Basic
import all Veir.IR.OpCode

public section
namespace Veir.Legalization.CTreeProofs

/-- One incoming edge passes an extension of the old operand. Every block keeps its operation
order, with the extension inserted immediately before the branch. -/
structure WidenedBranchOperand (ctx ctx' : WfIRContext OpCode) (operand : OpOperandPtr)
    (width : Nat) (ext : OperationPtr) : Prop where
  fresh : ¬ ext.InBounds ctx.raw
  extIn : ext.InBounds ctx'.raw
  extCode : ext.getOpType! ctx'.raw = .gmir .g_anyext
  extOperands : ext.getOperands! ctx'.raw = #[operand.op.getOperand! ctx.raw operand.index]
  extResults : ext.getResultTypes! ctx'.raw = #[(IntegerType.signless width : TypeAttr)]
  extSuccessors : ext.getSuccessors! ctx'.raw = #[]
  allocation : PhiAllocation ctx ctx' (· = ext)
  branchOperands : operand.op.getOperands! ctx'.raw =
    (operand.op.getOperands! ctx.raw).set! operand.index (ext.getResult 0)
  branchCode : operand.op.getOpType! ctx'.raw = operand.op.getOpType! ctx.raw
  branchProperties : ∀ {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
    (code : Dialect), operand.op.getProperties! ctx'.raw code = operand.op.getProperties! ctx.raw code
  successors : operand.op.getSuccessors! ctx'.raw = operand.op.getSuccessors! ctx.raw
  branchResults : operand.op.getResultTypes! ctx'.raw = operand.op.getResultTypes! ctx.raw
  branchRegions : operand.op.getNumRegions! ctx'.raw = operand.op.getNumRegions! ctx.raw
  branchRegion : ∀ i, operand.op.getRegion! ctx'.raw i = operand.op.getRegion! ctx.raw i
  branchParent : operand.op.getParent! ctx'.raw = operand.op.getParent! ctx.raw
  bounds : ∀ (p : GenericPtr), p.InBounds ctx.raw → p.InBounds ctx'.raw
  others : ∀ op, op.InBounds ctx.raw → op ≠ operand.op → OpSame id ctx.raw ctx'.raw op
  ctxSame : CtxSame ctx.raw ctx'.raw
  valueTypes : ∀ (v : ValuePtr), v.InBounds ctx.raw → v.getType! ctx'.raw = v.getType! ctx.raw
  opList : ∀ (block : BlockPtr) (h : block.InBounds ctx.raw),
    block.opList ctx' (ctxSame.blockIn h) =
      (block.opList ctx h).replaceBy operand.op [ext, operand.op]

theorem WidenedBranchOperand.of_create {ctx middle : WfIRContext OpCode} {operand : OpOperandPtr}
    {width : Nat} {ext : OperationPtr} (operandIn : operand.InBounds ctx.raw)
    (created : WfRewriter.createOp! ctx GMIR.g_anyext #[IntegerType.signless width]
      #[operand.op.getOperand! ctx.raw operand.index] #[] #[] () (some (.before operand.op)) =
      some (middle, ext)) :
    WidenedBranchOperand ctx (WfRewriter.replaceOperand! middle operand (ext.getResult 0))
      operand width ext := by
  obtain ⟨_, _, _, _, created⟩ := WfRewriter.createOp_of_createOp! created
  obtain ⟨fresh, extIn, ops, same, types, extCode, extResults, extOperands, extSuccessors⟩ :=
    WfRewriter.createOp_frame created
  have branchIn := (OpOperandPtr.inBounds_def.mp operandIn).1
  have branch := ops operand.op branchIn
  have different : operand.op ≠ ext := fun h => fresh (h ▸ branchIn)
  have operandIn' : operand.InBounds middle.raw := by
    have := WfRewriter.createOp_inBounds_mono (ptr := .opOperand operand) created
    grind
  have extResultIn : (ValuePtr.opResult (ext.getResult 0)).InBounds middle.raw := by
    have := congrArg Array.size extResults
    grind [OperationPtr.getResult]
  simp only [WfRewriter.replaceOperand!, dite_eq_left operandIn', dite_eq_left extResultIn]
  let out := WfRewriter.replaceOperand middle operand (ext.getResult 0) operandIn' extResultIn
  have keepsIn (p : GenericPtr) : p.InBounds out.raw ↔ p.InBounds middle.raw :=
    WfRewriter.replaceOperand_inBounds_iff
  have resultTypes (o : OperationPtr) : o.getResultTypes! out.raw = o.getResultTypes! middle.raw := by
    simp only [OperationPtr.getResultTypes!_def, out, WfRewriter.replaceOperand]
    simp [OperationPtr.getResults!, ValuePtr.getType!_replaceUse]
  have others (o : OperationPtr) (oIn : o.InBounds middle.raw) (h : operand.op ≠ o) :
      OpSame id middle.raw out.raw o := by
    refine ⟨(keepsIn (.operation o)).mpr oIn, ?_, fun _ => ?_, resultTypes o, ?_, ?_, ?_,
      fun _ => ?_, ?_⟩
    all_goals simp [out, WfRewriter.replaceOperand, OperationPtr.getOperands!_replaceUse, h]
  have extSame := others ext extIn different
  have nodes := PhiAllocation.create created
  have ctxSame : CtxSame middle.raw out.raw := by
    refine ⟨fun {b} => (keepsIn (.block b)).mpr, fun _ => ?_, fun _ => ?_,
      fun {r} => (keepsIn (.region r)).mpr, fun _ => ?_, fun _ => ?_⟩
    all_goals simp [out, WfRewriter.replaceOperand]
  change WidenedBranchOperand ctx out operand width ext
  refine {
    fresh, extIn := extSame.inBounds
    extCode := extSame.opType.trans extCode
    extOperands := by rw [extSame.operands, extOperands]; simp
    extResults := (resultTypes ext).trans extResults
    extSuccessors := extSame.successors.trans extSuccessors
    allocation := {
      block := fun {b} h => nodes.block ((keepsIn (.block b)).mp h)
      region := fun {r} h => nodes.region ((keepsIn (.region r)).mp h)
      operation := fun {o} h => nodes.operation ((keepsIn (.operation o)).mp h) }
    branchOperands := ?_
    branchCode := ?_
    branchProperties := fun code => ?_
    successors := ?_
    branchResults := (resultTypes operand.op).trans branch.resultTypes
    branchRegions := ?_
    branchRegion := fun i => ?_
    branchParent := ?_
    bounds := fun p pIn => (keepsIn p).mpr (WfRewriter.createOp_inBounds_mono created pIn)
    others := fun op opIn h => (ops op opIn).trans_id (others op (ops op opIn).inBounds h.symm)
    ctxSame := same.trans ctxSame
    valueTypes := fun v vIn => ?_
    opList := fun b h => ?_
  }
  · simp [out, WfRewriter.replaceOperand, OperationPtr.getOperands!_replaceUse, branch.operands]
  · simpa [out, WfRewriter.replaceOperand] using branch.opType
  · simpa [out, WfRewriter.replaceOperand] using branch.properties code
  · simpa [out, WfRewriter.replaceOperand] using branch.successors
  · simpa [out, WfRewriter.replaceOperand] using branch.numRegions
  · simpa [out, WfRewriter.replaceOperand] using branch.region i
  · simpa [out, WfRewriter.replaceOperand] using branch.parent
  · simpa [out, WfRewriter.replaceOperand] using types v vIn
  · refine Eq.trans ?_ (WfRewriter.createOp_before_opList created h (same.blockIn h))
    unfold BlockPtr.opList
    congr 1
    exact BlockPtr.operationList_rewriter_replaceUse middle.wellFormed rfl

theorem widenBranchOperand_frame {ctx ctx' : WfIRContext OpCode} {operand : OpOperandPtr}
    {width : Nat} (operandIn : operand.InBounds ctx.raw)
    (widened : widenBranchOperand ctx operand width = some ctx') :
    ∃ ext, WidenedBranchOperand ctx ctx' operand width ext := by
  unfold widenBranchOperand at widened
  cases created : WfRewriter.createOp! ctx GMIR.g_anyext #[IntegerType.signless width]
      #[operand.op.getOperand! ctx.raw operand.index] #[] #[] () (some (.before operand.op)) with
  | none => simp [created] at widened
  | some result =>
    obtain ⟨middle, ext⟩ := result
    simp [created] at widened
    subst ctx'
    exact ⟨ext, WidenedBranchOperand.of_create operandIn created⟩

/-- The operand slot, chosen width and fresh extension for one branch argument. -/
structure BranchOperandExtension where
  operand : OpOperandPtr
  width : Nat
  ext : OperationPtr

/-- The sequence of branch operands updated by the incoming-edge fold, in execution order. -/
inductive WidenedIncomingEdges : WfIRContext OpCode → WfIRContext OpCode →
    List BranchOperandExtension → Prop
  | nil : WidenedIncomingEdges ctx ctx []
  | cons {ctx middle ctx' : WfIRContext OpCode} {update : BranchOperandExtension}
      {updates : List BranchOperandExtension}
      (step : WidenedBranchOperand ctx middle update.operand update.width update.ext)
      (rest : WidenedIncomingEdges middle ctx' updates) :
      WidenedIncomingEdges ctx ctx' (update :: updates)

theorem WidenedIncomingEdges.append (first : WidenedIncomingEdges ctx middle before)
    (second : WidenedIncomingEdges middle ctx' after) :
    WidenedIncomingEdges ctx ctx' (before ++ after) := by
  induction first with
  | nil => exact second
  | cons step rest ih => exact .cons step (ih second)

theorem WidenedIncomingEdges.bounds (tr : WidenedIncomingEdges ctx ctx' updates)
    (p : GenericPtr) (h : p.InBounds ctx.raw) : p.InBounds ctx'.raw := by
  induction tr with
  | nil => exact h
  | cons step rest ih => exact ih (step.bounds p h)

theorem WidenedIncomingEdges.ctxSame (tr : WidenedIncomingEdges ctx ctx' updates) :
    CtxSame ctx.raw ctx'.raw := by
  induction tr with
  | nil => exact CtxSame.refl
  | cons step _ ih => exact step.ctxSame.trans ih

theorem WidenedIncomingEdges.valueTypes (tr : WidenedIncomingEdges ctx ctx' updates)
    (v : ValuePtr) (vin : v.InBounds ctx.raw) : v.getType! ctx'.raw = v.getType! ctx.raw := by
  induction tr with
  | nil => rfl
  | cons step _ ih => exact (ih (step.bounds (.value _) vin)).trans (step.valueTypes v vin)

/-- The original operation's instruction and control-flow metadata after rewiring operands. -/
structure PhiOpHeader (ctx ctx' : WfIRContext OpCode) (op : OperationPtr) : Prop where
  inBounds : op.InBounds ctx'.raw
  code : op.getOpType! ctx'.raw = op.getOpType! ctx.raw
  properties : ∀ {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
    (code : Dialect), op.getProperties! ctx'.raw code = op.getProperties! ctx.raw code
  results : op.getResultTypes! ctx'.raw = op.getResultTypes! ctx.raw
  successors : op.getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw
  numRegions : op.getNumRegions! ctx'.raw = op.getNumRegions! ctx.raw
  region : ∀ i, op.getRegion! ctx'.raw i = op.getRegion! ctx.raw i
  parent : op.getParent! ctx'.raw = op.getParent! ctx.raw

theorem PhiOpHeader.of_same {f} (h : OpSame f ctx.raw ctx'.raw op) : PhiOpHeader ctx ctx' op :=
  ⟨h.inBounds, h.opType, h.properties, h.resultTypes, h.successors, h.numRegions, h.region, h.parent⟩

theorem PhiOpHeader.trans (h : PhiOpHeader ctx middle op) (h' : PhiOpHeader middle ctx' op) :
    PhiOpHeader ctx ctx' op :=
  ⟨h'.inBounds, h'.code.trans h.code, fun c => (h'.properties c).trans (h.properties c),
    h'.results.trans h.results, h'.successors.trans h.successors, h'.numRegions.trans h.numRegions,
    fun i => (h'.region i).trans (h.region i), h'.parent.trans h.parent⟩

theorem WidenedIncomingEdges.opHeader (tr : WidenedIncomingEdges ctx ctx' updates)
    {op : OperationPtr} (opIn : op.InBounds ctx.raw) : PhiOpHeader ctx ctx' op := by
  induction tr with
  | nil => exact .of_same (f := id) (OpSame.refl opIn)
  | @cons ctx middle _ u _ step _ ih =>
    have one : PhiOpHeader ctx middle op := by
      by_cases eq : op = u.operand.op
      · subst op
        exact ⟨step.bounds (.operation _) opIn, step.branchCode, step.branchProperties,
          step.branchResults, step.successors, step.branchRegions, step.branchRegion, step.branchParent⟩
      · exact .of_same (step.others op opIn eq)
    exact one.trans (ih one.inBounds)

theorem WidenedIncomingEdges.fresh (tr : WidenedIncomingEdges ctx ctx' updates)
    {u : BranchOperandExtension} (mem : u ∈ updates) : ¬ u.ext.InBounds ctx.raw := by
  induction tr with
  | nil => simp at mem
  | cons step _ ih =>
    rcases List.mem_cons.mp mem with rfl | h
    · exact step.fresh
    · exact fun bound => ih h (step.bounds (.operation _) bound)

theorem WidenedIncomingEdges.freshExtensions (tr : WidenedIncomingEdges ctx ctx' updates) :
    (updates.map BranchOperandExtension.ext).Nodup := by
  induction tr with
  | nil => simp
  | cons step rest ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    rintro mem
    obtain ⟨u, hu, same⟩ := List.mem_map.mp mem
    exact rest.fresh hu (same ▸ step.extIn)

theorem WidenedIncomingEdges.numOperands (tr : WidenedIncomingEdges ctx ctx' updates)
    {op : OperationPtr} (opIn : op.InBounds ctx.raw) :
    op.getNumOperands! ctx'.raw = op.getNumOperands! ctx.raw := by
  induction tr with
  | nil => rfl
  | @cons ctx middle _ u _ step rest ih =>
    rw [ih (step.bounds (.operation _) opIn), ← OperationPtr.getOperands!.size_eq_getNumOperands!,
      ← OperationPtr.getOperands!.size_eq_getNumOperands!]
    by_cases eq : op = u.operand.op
    · subst op; simp [step.branchOperands]
    · simp [(step.others op opIn eq).operands]

theorem WidenedIncomingEdges.opSame (tr : WidenedIncomingEdges ctx ctx' updates)
    {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (other : ∀ update ∈ updates, op ≠ update.operand.op) : OpSame id ctx.raw ctx'.raw op := by
  induction tr with
  | nil => exact OpSame.refl opIn
  | cons step rest ih =>
    have h := step.others op opIn (other _ List.mem_cons_self)
    exact h.trans_id (ih h.inBounds (fun u hu => other u (List.mem_cons_of_mem _ hu)))

theorem WidenedBranchOperand.getOperand (step : WidenedBranchOperand ctx ctx' operand width ext)
    (slot : OpOperandPtr) (slotIn : slot.InBounds ctx.raw) :
    slot.op.getOperand! ctx'.raw slot.index =
      if slot = operand then (ext.getResult 0 : ValuePtr)
      else slot.op.getOperand! ctx.raw slot.index := by
  by_cases owner : slot.op = operand.op
  · obtain ⟨opIn, bound⟩ := OpOperandPtr.inBounds_def.mp slotIn
    have size : slot.index < (slot.op.getOperands! ctx.raw).size := by
      simpa [OperationPtr.getNumOperands!_eq_getNumOperands opIn] using bound
    have h := congrArg (fun xs : Array ValuePtr => xs[slot.index]!) step.branchOperands
    rw [← owner] at h
    simp only [OperationPtr.getOperands!.getElem!_eq_getOperand!] at h
    rw [h]
    by_cases idx : slot.index = operand.index
    · have eq : slot = operand := by cases slot; cases operand; simp_all
      subst operand
      rw [ite_eq_left rfl, Array.getElem!_set!_self _ _ _ size]
    · have ne : slot ≠ operand := fun eq => idx (eq ▸ rfl)
      rw [ite_eq_right ne, Array.getElem!_set!_ne _ _ _ _ (Ne.symm idx),
        OperationPtr.getOperands!.getElem!_eq_getOperand!]
  · have ne : slot ≠ operand := fun eq => owner (eq ▸ rfl)
    rw [ite_eq_right ne, ← OperationPtr.getOperands!.getElem!_eq_getOperand!,
      (step.others slot.op (OpOperandPtr.inBounds_def.mp slotIn).1 owner).operands]
    simp

theorem WidenedIncomingEdges.untouchedOperand (tr : WidenedIncomingEdges ctx ctx' updates)
    {slot : OpOperandPtr} (slotIn : slot.InBounds ctx.raw)
    (untouched : ∀ u ∈ updates, slot ≠ u.operand) :
    slot.op.getOperand! ctx'.raw slot.index = slot.op.getOperand! ctx.raw slot.index := by
  induction tr with
  | nil => rfl
  | cons step rest ih =>
    rw [ih (step.bounds (.opOperand slot) slotIn)
      (fun u hu => untouched u (List.mem_cons_of_mem _ hu)),
      step.getOperand slot slotIn, ite_eq_right (untouched _ List.mem_cons_self)]

theorem WidenedIncomingEdges.opList (tr : WidenedIncomingEdges ctx ctx' updates)
    (b : BlockPtr) (h : b.InBounds ctx.raw) :
    b.opList ctx' (tr.ctxSame.blockIn h) = updates.foldl (init := b.opList ctx h)
      (fun ops u => ops.replaceBy u.operand.op [u.ext, u.operand.op]) := by
  induction tr with
  | nil => rfl
  | cons step rest ih =>
    rw [ih (step.ctxSame.blockIn h), List.foldl_cons, step.opList]

/-- All extensions inserted in front of an operation, in their final execution order. -/
def extensionsBefore (updates : List BranchOperandExtension) (op : OperationPtr) : List OperationPtr :=
  (updates.filter (fun u => u.operand.op == op)).map BranchOperandExtension.ext

theorem WidenedIncomingEdges.opList_flatMap (tr : WidenedIncomingEdges ctx ctx' updates)
    (inBounds : ∀ u ∈ updates, u.operand.InBounds ctx.raw)
    (b : BlockPtr) (bIn : b.InBounds ctx.raw) :
    b.opList ctx' (tr.ctxSame.blockIn bIn) = (b.opList ctx bIn).flatMap
      (fun op => extensionsBefore updates op ++ [op]) := by
  induction tr with
  | nil => simp [extensionsBefore]
  | @cons ctx middle ctx' first tail step rest ih =>
    have noEdge : extensionsBefore tail first.ext = [] := by
      unfold extensionsBefore
      rw [List.filter_eq_nil_iff.mpr (by
        intro u hu
        have old := (OpOperandPtr.inBounds_def.mp (inBounds u (List.mem_cons_of_mem _ hu))).1
        simpa using (show u.operand.op ≠ first.ext from fun eq => step.fresh (eq ▸ old)))]
      rfl
    rw [ih (fun u hu => step.bounds (.opOperand _) (inBounds u (List.mem_cons_of_mem _ hu)))
      (step.ctxSame.blockIn bIn), step.opList b bIn]
    simp only [List.replaceBy, List.flatMap_assoc]
    apply List.flatMap_congr_of_mem
    intro op _
    by_cases h : op = first.operand.op
    · subst op
      simp [extensionsBefore] at noEdge ⊢
      exact noEdge
    · simp [h, extensionsBefore, Ne.symm h]

/-- The generated extension still takes the original operand after the whole fold, and the
corresponding branch slot holds its result. Multiple arguments on the same branch are allowed. -/
theorem WidenedIncomingEdges.extension (tr : WidenedIncomingEdges ctx ctx' updates)
    (inBounds : ∀ u ∈ updates, u.operand.InBounds ctx.raw)
    (distinct : (updates.map BranchOperandExtension.operand).Nodup)
    (u : BranchOperandExtension) (hu : u ∈ updates) :
    ¬ u.ext.InBounds ctx.raw ∧ u.ext.InBounds ctx'.raw ∧
    u.ext.getOpType! ctx'.raw = .gmir .g_anyext ∧
    u.ext.getResultTypes! ctx'.raw = #[(IntegerType.signless u.width : TypeAttr)] ∧
    u.ext.getOperands! ctx'.raw = #[u.operand.op.getOperand! ctx.raw u.operand.index] ∧
    u.operand.op.getOperand! ctx'.raw u.operand.index = u.ext.getResult 0 := by
  induction tr with
  | nil => simp at hu
  | @cons ctx mid last first tail step rest ih =>
    have tailIn (v) (hv : v ∈ tail) := inBounds v (List.mem_cons_of_mem _ hv)
    have tailIn' (v) (hv : v ∈ tail) := step.bounds (.opOperand v.operand) (by simpa using tailIn v hv)
    obtain ⟨single, nodup⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp hu with rfl | hu
    · have extSame := rest.opSame step.extIn (fun v hv eq =>
        step.fresh (eq ▸ (OpOperandPtr.inBounds_def.mp (tailIn v hv)).1))
      have slotIn := inBounds u List.mem_cons_self
      have slot := rest.untouchedOperand (step.bounds (.opOperand _) slotIn)
        (fun v hv eq => single (eq ▸ List.mem_map_of_mem hv))
      refine ⟨step.fresh, extSame.inBounds, extSame.opType.trans step.extCode,
        extSame.resultTypes.trans step.extResults, ?_, ?_⟩
      · simp [extSame.operands, step.extOperands]
      · rw [slot, step.getOperand _ slotIn, ite_eq_left rfl]
    · obtain ⟨fresh, present, code, results, operands, slot⟩ := ih tailIn' nodup hu
      have ne : u.operand ≠ first.operand := fun eq => single (eq ▸ List.mem_map_of_mem hu)
      refine ⟨fun h => fresh (step.bounds (.operation _) h), present, code, results, ?_, slot⟩
      rw [operands, step.getOperand _ (tailIn u hu), ite_eq_right ne]

/-- The slots on an incoming edge corresponding to the selected arguments of the destination. -/
def branchOperandRequests (branch : OperationPtr) (operands : SuccessorOperands)
    (args : List (Nat × Nat)) : List (OpOperandPtr × Nat) :=
  args.map fun (i, width) => (⟨branch, operands.getOperandIndex i⟩, width)

private theorem widenBranchOperand_fold {ctx ctx' : WfIRContext OpCode}
    (branch : OperationPtr) (operands : SuccessorOperands) (args : List (Nat × Nat))
    (inBounds : ∀ slot ∈ branchOperandRequests branch operands args,
      slot.1.InBounds ctx.raw)
    (run : args.foldlM (init := ctx)
      (fun ctx (i, width) => widenBranchOperand ctx ⟨branch, operands.getOperandIndex i⟩ width) =
      some ctx') :
    ∃ updates, WidenedIncomingEdges ctx ctx' updates ∧
      updates.map (fun u => (u.operand, u.width)) = branchOperandRequests branch operands args := by
  induction args generalizing ctx with
  | nil =>
    simp at run
    subst ctx'
    exact ⟨[], .nil, rfl⟩
  | cons head tail ih =>
    obtain ⟨i, width⟩ := head
    let slot : OpOperandPtr := ⟨branch, operands.getOperandIndex i⟩
    have valid : slot.InBounds ctx.raw := inBounds (slot, width) List.mem_cons_self
    rw [List.foldlM_cons] at run
    cases step : widenBranchOperand ctx slot width with
    | none => simp [slot] at step; simp [step] at run
    | some middle =>
      obtain ⟨ext, first⟩ := widenBranchOperand_frame valid step
      have later : ∀ x ∈ branchOperandRequests branch operands tail, x.1.InBounds middle.raw :=
        fun x hx => first.bounds (.opOperand _) (inBounds x (List.mem_cons_of_mem _ hx))
      change (widenBranchOperand ctx slot width >>= _) = some ctx' at run
      have next := ih (ctx := middle) later (by simpa [step] using run)
      obtain ⟨updates, trace, order⟩ := next
      refine ⟨⟨slot, width, ext⟩ :: updates, .cons first trace, ?_⟩
      simpa [branchOperandRequests, slot] using congrArg (List.cons (slot, width)) order

/-- A successful nested fold inserts exactly one extension for each requested operand slot on
each incoming edge, in the order supplied by the pass. -/
theorem widenIncomingEdges_frame {ctx ctx' : WfIRContext OpCode}
    (edges : List (OperationPtr × SuccessorOperands)) (args : List (Nat × Nat))
    (inBounds : ∀ x ∈ edges.flatMap (fun e => branchOperandRequests e.1 e.2 args),
      x.1.InBounds ctx.raw)
    (run : edges.foldlM (init := ctx) (fun ctx (branch, operands) => args.foldlM (init := ctx)
      (fun ctx (i, width) => widenBranchOperand ctx ⟨branch, operands.getOperandIndex i⟩ width)) =
      some ctx') :
    ∃ updates, WidenedIncomingEdges ctx ctx' updates ∧
      updates.map (fun u => (u.operand, u.width)) =
        edges.flatMap (fun e => branchOperandRequests e.1 e.2 args) := by
  induction edges generalizing ctx with
  | nil =>
    simp at run
    subst ctx'
    exact ⟨[], .nil, rfl⟩
  | cons edge tail ih =>
    obtain ⟨branch, operands⟩ := edge
    rw [List.foldlM_cons] at run
    cases step : args.foldlM (init := ctx) (fun ctx (i, width) =>
        widenBranchOperand ctx ⟨branch, operands.getOperandIndex i⟩ width) with
    | none => simp [step] at run
    | some middle =>
      obtain ⟨first, front, order⟩ := widenBranchOperand_fold branch operands args
        (fun x hx => inBounds x (List.mem_append_left _ hx)) step
      obtain ⟨rest, back, order'⟩ := ih (ctx := middle)
        (fun x hx => front.bounds (.opOperand _) (inBounds x (List.mem_append_right _ hx)))
        (by simpa [step] using run)
      exact ⟨first ++ rest, front.append back, by simp [order, order']⟩

end Veir.Legalization.CTreeProofs
