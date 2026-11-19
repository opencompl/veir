module

public import Veir.Passes.Legalization.LegalizerHelper
public import Veir.Passes.LLVMToGMIR.BranchPass
public import Veir.Passes.Legalization.Validity.PhiAllocation
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.IR.Basic
import all Veir.IR.OpCode
import all Veir.Rewriter.InsertPoint

public section

namespace Veir.Legalization.CTreeProofs

/-- Insert an operation at the fixed insertion point used by the block-argument widening fold. -/
def insertAtPoint (ip : InsertPoint) (block : BlockPtr) (newOp : OperationPtr)
    (ops : List OperationPtr) : List OperationPtr :=
  match ip with
  | .before op => ops.replaceBy op [newOp, op]
  | .atEnd target => if target = block then ops ++ [newOp] else ops

private theorem createOp_insertAtPoint {D : Type} [HasOpInfo D] [HasDialect OpCode D]
    {ctx ctx' : WfIRContext OpCode} {opcode : D} {properties : propertiesOf opcode}
    {resultTypes : Array TypeAttr} {operands : Array ValuePtr} {successors : Array BlockPtr}
    {ip : InsertPoint} {newOp : OperationPtr} {h₁ h₂ h₃ h₄}
    (h : WfRewriter.createOp ctx opcode resultTypes operands successors #[] properties
      (some ip) h₁ h₂ h₃ h₄ = some (ctx', newOp))
    {block : BlockPtr} (blockIn : block.InBounds ctx.raw) (blockIn' : block.InBounds ctx'.raw) :
    block.opList ctx' blockIn' = insertAtPoint ip block newOp (block.opList ctx blockIn) := by
  cases ip with
  | before op => exact WfRewriter.createOp_before_opList h blockIn blockIn'
  | atEnd target =>
    simp only [WfRewriter.createOp] at h
    split at h
    next => simp at h
    next raw' newOp' hRaw =>
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [BlockPtr.opList, insertAtPoint]
      rw [BlockPtr.operationList_rewriter_createOp hRaw ctx.wellFormed]
      by_cases eq : target = block
      · subst target
        simp [InsertPoint.idxIn_atEnd_eq]
      · simp [eq]

/-- The frame of one block argument widening and the inserted truncation's metadata. -/
structure WidenArgumentStep (ctx ctx' : WfIRContext OpCode) (ip : InsertPoint)
    (arg : BlockArgumentPtr) (width : Nat) (cast : OperationPtr) :
    Prop where
  ops : ∀ o, o.InBounds ctx.raw → OpSame (substArg arg cast) ctx.raw ctx'.raw o
  ctxSame : CtxSame ctx.raw ctx'.raw
  types : ∀ value : ValuePtr, value.InBounds ctx.raw →
    value.InBounds ctx'.raw ∧ value.getType! ctx'.raw =
      if value = .blockArgument arg then (IntegerType.signless width : TypeAttr) else value.getType! ctx.raw
  castIn : cast.InBounds ctx'.raw
  castNotIn : ¬ cast.InBounds ctx.raw
  allocation : PhiAllocation ctx ctx' (· = cast)
  castType : cast.getOpType! ctx'.raw = .gmir .g_trunc
  castResultTypes : cast.getResultTypes! ctx'.raw = #[(ValuePtr.blockArgument arg).getType! ctx.raw]
  castProperties : cast.getProperties! ctx'.raw (OpCode.gmir .g_trunc) =
    ({ nsw := false, nuw := false } : NswNuwProperties)
  castSuccessors : cast.getSuccessors! ctx'.raw = #[]
  castNumRegions : cast.getNumRegions! ctx'.raw = 0
  castOperands : cast.getOperands! ctx'.raw = #[.blockArgument arg]
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx.raw),
    block.opList ctx' (ctxSame.blockIn blockIn) =
      insertAtPoint ip block cast (block.opList ctx blockIn)

/-- A successful truncation step redirects exactly the uses of its argument and adds one operation. -/
theorem widenBlockArgument_spec {ctx ctx' : WfIRContext OpCode} {arg : BlockArgumentPtr}
    {ip : InsertPoint} {width : Nat} (argIn : arg.InBounds ctx.raw)
    (h : widenBlockArgument ip arg width ctx = some ctx') :
    ∃ cast, WidenArgumentStep ctx ctx' ip arg width cast := by
  simp only [widenBlockArgument, bind, Option.bind] at h
  split at h <;> try contradiction
  rename_i result hCreate
  obtain ⟨ctx₂, cast⟩ := result
  simp only [Option.pure_def, Option.some.injEq] at h
  subst ctx'
  have valueIn : (ValuePtr.blockArgument arg).InBounds ctx.raw := by simpa using argIn
  rw [WfRewriter.setType!_eq valueIn] at hCreate
  obtain ⟨hOps₁, hCtx₁, hIn₁, hTypes₁, hList₁⟩ := WfRewriter.setType_frame (ctx := ctx)
    (arg := arg) (type := (IntegerType.signless width : TypeAttr)) (argIn := valueIn)
  generalize WfRewriter.setType ctx (.blockArgument arg) (IntegerType.signless width : TypeAttr) valueIn = ctx₁
    at hCreate hOps₁ hCtx₁ hIn₁ hTypes₁ hList₁
  obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
  obtain ⟨hNotIn₂, hIn₂, hOps₂, hCtx₂, hTypes₂, hType₂, hResultTypes₂, hOperands₂, hSucc₂⟩ :=
    WfRewriter.createOp_frame hCreate
  have hProps₂ := WfRewriter.createOp_gmir_properties hCreate
  have allocation₂ := PhiAllocation.create hCreate
  have hRegions₂ : cast.getNumRegions! ctx₂.raw = 0 := by
    rw [OperationPtr.getNumRegions!_WfRewriter_createOp hCreate]
    simp
  have hMono₂ : ∀ ptr : GenericPtr, ptr.InBounds ctx₁.raw → ptr.InBounds ctx₂.raw :=
    fun ptr => WfRewriter.createOp_inBounds_mono hCreate
  have hList₂ := fun (block : BlockPtr) (bIn : block.InBounds ctx₁.raw) (bIn' : block.InBounds ctx₂.raw) =>
    createOp_insertAtPoint hCreate bIn bIn'
  /- The uses of the argument become uses of the cast. -/
  have valueIn₂ : (ValuePtr.blockArgument arg).InBounds ctx₂.raw := by
    have := hMono₂ (.value (.blockArgument arg)) ((hIn₁ _).mpr (by simpa using valueIn))
    simpa using this
  have castNum : cast.getNumResults! ctx₂.raw = 1 := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hResultTypes₂]; rfl
  have resultIn₂ : (ValuePtr.opResult (cast.getResult 0)).InBounds ctx₂.raw := by
    simp only [ValuePtr.inBounds_opResult, OperationPtr.getResult_def]
    exact OpResultPtr.inBounds_def.mpr ⟨hIn₂, by grind⟩
  have hNe : ValuePtr.blockArgument arg ≠ ValuePtr.opResult (cast.getResult 0) := by simp
  rw [WfRewriter.replaceValue!_eq hNe valueIn₂ resultIn₂]
  obtain ⟨hOps₃, hCtx₃, hIn₃, hTypes₃⟩ := WfRewriter.replaceValue_frame (ctx := ctx₂)
    (hNe := hNe) (oldIn := valueIn₂) (newIn := resultIn₂)
  have hList₃ := fun (block : BlockPtr) (bIn : block.InBounds ctx₂.raw) bIn' =>
    WfRewriter.replaceValue_opList (ctx := ctx₂) (hNe := hNe) (oldIn := valueIn₂)
      (newIn := resultIn₂) (block := block) bIn bIn'
  generalize WfRewriter.replaceValue ctx₂ (.blockArgument arg) (.opResult (cast.getResult 0)) hNe
    valueIn₂ resultIn₂ = ctx₃ at hOps₃ hCtx₃ hIn₃ hTypes₃ hList₃
  /- The truncation takes the widened argument. -/
  have castIn₃ : cast.InBounds ctx₃.raw := by
    have := (hIn₃ (.operation cast)).mpr (by simpa using hIn₂); simpa using this
  have valueIn₃ : (ValuePtr.blockArgument arg).InBounds ctx₃.raw := by
    have := (hIn₃ (.value (.blockArgument arg))).mpr (by simpa using valueIn₂); simpa using this
  rw [WfRewriter.pushOperand!_eq castIn₃ valueIn₃]
  obtain ⟨hOps₄, hCast₄, hCtx₄, hMono₄, hTypes₄, hList₄⟩ := WfRewriter.pushOperand_frame
    (ctx := ctx₃) (op := cast) (value := .blockArgument arg) (opIn := castIn₃) (valueIn := valueIn₃)
  have hCastMeta :
      let ctx₄ := WfRewriter.pushOperand ctx₃ cast (.blockArgument arg) castIn₃ valueIn₃
      cast.getProperties! ctx₄.raw (OpCode.gmir .g_trunc) =
        cast.getProperties! ctx₃.raw (OpCode.gmir .g_trunc) ∧
      cast.getSuccessors! ctx₄.raw = cast.getSuccessors! ctx₃.raw ∧
      cast.getNumRegions! ctx₄.raw = cast.getNumRegions! ctx₃.raw := by
    simp [WfRewriter.pushOperand]
  have allocation₄ : PhiAllocation ctx₃
      (WfRewriter.pushOperand ctx₃ cast (.blockArgument arg) castIn₃ valueIn₃) (fun _ => False) := by
    constructor
    · intro b hb
      simpa using (WfRewriter.pushOperand_inBounds_iff (ptr := .block b)).mp hb
    · intro r hr
      simpa using (WfRewriter.pushOperand_inBounds_iff (ptr := .region r)).mp hr
    · intro o ho
      simpa using (WfRewriter.pushOperand_inBounds_iff (ptr := .operation o)).mp ho
  generalize WfRewriter.pushOperand ctx₃ cast (.blockArgument arg) castIn₃ valueIn₃ = ctx₄
    at hOps₄ hCast₄ hCtx₄ hMono₄ hTypes₄ hList₄ hCastMeta allocation₄
  have hNotIn : ¬ cast.InBounds ctx.raw := fun h =>
    hNotIn₂ (by have := (hIn₁ (.operation cast)).mpr (by simpa using h); simpa using this)
  have hCastSame₃ := hOps₃ cast hIn₂
  refine ⟨cast, {
    ops := fun o oIn => ?_
    ctxSame := ((hCtx₁.trans hCtx₂).trans hCtx₃).trans hCtx₄
    types := fun v vIn => ?_
    castIn := hCast₄.1
    castNotIn := hNotIn
    allocation := {
      block := fun {b} h => (hIn₁ (.block b)).mp
        (allocation₂.block ((hIn₃ (.block b)).mp (allocation₄.block h)))
      region := fun {r} h => (hIn₁ (.region r)).mp
        (allocation₂.region ((hIn₃ (.region r)).mp (allocation₄.region h)))
      operation := fun {o} h => (allocation₂.operation
        ((hIn₃ (.operation o)).mp ((allocation₄.operation h).resolve_right id))).imp_left
          (hIn₁ (.operation o)).mp }
    castType := hCast₄.2.1.trans (hCastSame₃.opType.trans (hType₂.trans (ofDialect_gmir _)))
    castResultTypes := hCast₄.2.2.1.trans (hCastSame₃.resultTypes.trans hResultTypes₂)
    castProperties := hCastMeta.1.trans ((hCastSame₃.properties _).trans hProps₂)
    castSuccessors := hCastMeta.2.1.trans (hCastSame₃.successors.trans hSucc₂)
    castNumRegions := hCastMeta.2.2.trans (hCastSame₃.numRegions.trans hRegions₂)
    castOperands := by rw [hCast₄.2.2.2, hCastSame₃.operands, hOperands₂]; simp
    opList := fun block bIn => ?_ }⟩
  · have s₁ := hOps₁ o oIn
    have s₂ := hOps₂ o s₁.inBounds
    have s₃ := hOps₃ o s₂.inBounds
    have hNeCast : o ≠ cast := fun hEq => hNotIn (hEq ▸ oIn)
    have s₄ := hOps₄ o s₃.inBounds hNeCast
    exact (((s₁.trans_id s₂).trans s₃).trans_id s₄).congr (fun _ _ => rfl)
  · have v₁ : v.InBounds ctx₁.raw := by
      have := (hIn₁ (.value v)).mpr (by simpa using vIn); simpa using this
    have v₂ : v.InBounds ctx₂.raw := by
      have := hMono₂ (.value v) (by simpa using v₁); simpa using this
    have v₃ : v.InBounds ctx₃.raw := by
      have := (hIn₃ (.value v)).mpr (by simpa using v₂); simpa using this
    refine ⟨by have := hMono₄ (.value v) (by simpa using v₃); simpa using this, ?_⟩
    rw [hTypes₄, hTypes₃, hTypes₂ v v₁, hTypes₁]
  · have b₁ := hCtx₁.blockIn bIn
    have b₂ := hCtx₂.blockIn b₁
    have b₃ := hCtx₃.blockIn b₂
    rw [hList₄ block b₃, hList₃ block b₂, hList₂ block b₁, hList₁ block bIn]

/-- Inserting successive truncations at the original start appends them to the prefix of fresh
operations there. -/
private theorem insertAtStart_after_prefix {ctx : WfIRContext OpCode} {target block : BlockPtr}
    {prefixOps : List OperationPtr} {newOp : OperationPtr}
    (targetIn : target.InBounds ctx.raw) (blockIn : block.InBounds ctx.raw)
    (fresh : ∀ o ∈ prefixOps, ¬ o.InBounds ctx.raw) :
    insertAtPoint (InsertPoint.atStart! target ctx.raw) block newOp
        ((if block = target then prefixOps else []) ++ block.opList ctx blockIn) =
      (if block = target then prefixOps ++ [newOp] else []) ++ block.opList ctx blockIn := by
  have chain := BlockPtr.operationListWF ctx.raw target targetIn ctx.wellFormed
  have first : target.getFirstOp! ctx.raw = (target.opList ctx targetIn).head? := by
    simpa only [BlockPtr.opList, List.head?_eq_getElem?, Array.getElem?_toList] using chain.first
  rw [InsertPoint.atStart!, first]
  cases ht : target.opList ctx targetIn with
  | nil =>
    by_cases hb : block = target
    · subst block
      simp [insertAtPoint, ht]
    · simp [insertAtPoint, hb, Ne.symm hb]
  | cons firstOp rest =>
    have hm : firstOp ∈ target.opList ctx targetIn := by simp [ht]
    have hIn := chain.arrayInBounds (by simpa [BlockPtr.opList] using hm)
    have hParent := (BlockPtr.mem_opList hIn).mp hm
    by_cases hb : block = target
    · subst block
      have noFirst : firstOp ∉ prefixOps := fun h => fresh _ h hIn
      have noRepeat := (List.nodup_cons.mp (ht ▸ BlockPtr.opList_nodup)).1
      have hPrefix := List.replaceBy_of_not_mem (r := [newOp, firstOp]) noFirst
      have hRest := List.replaceBy_of_not_mem (r := [newOp, firstOp]) noRepeat
      simp only [List.replaceBy] at hPrefix hRest
      simp [ht, insertAtPoint, List.replaceBy, List.flatMap_append, hPrefix, hRest]
    · have absent : firstOp ∉ block.opList ctx blockIn := fun h =>
        hb (Option.some.inj (((BlockPtr.mem_opList hIn).mp h).symm.trans hParent))
      simp [insertAtPoint, hb, List.replaceBy_of_not_mem absent]

def selectedArgs (block : BlockPtr) (choices : List (Nat × Nat)) : List BlockArgumentPtr :=
  choices.map fun choice => ⟨block, choice.1⟩

/-- All the truncations inserted by a prefix of the widening fold. `done` lists the selected
arguments latest first. The truncations occur in the block in the original selection order. -/
structure WidenArgumentsFrame (src dst : WfIRContext OpCode) (block : BlockPtr)
    (done : List (Nat × Nat)) (cast : BlockArgumentPtr → OperationPtr) : Prop where
  ops : ∀ o, o.InBounds src.raw → OpSame (lowerArgs (selectedArgs block done) cast) src.raw dst.raw o
  ctxSame : CtxSame src.raw dst.raw
  bounds : ∀ v : ValuePtr, v.InBounds src.raw → v.InBounds dst.raw
  allocations : PhiCastAllocation src dst
  otherTypes : ∀ v : ValuePtr, v.InBounds src.raw →
    (∀ a ∈ selectedArgs block done, v ≠ .blockArgument a) → v.getType! dst.raw = v.getType! src.raw
  args : ∀ i w, (i, w) ∈ done →
    let a : BlockArgumentPtr := ⟨block, i⟩
    a.InBounds src.raw ∧ (ValuePtr.blockArgument a).getType! dst.raw = (IntegerType.signless w : TypeAttr) ∧
    (cast a).InBounds dst.raw ∧ ¬ (cast a).InBounds src.raw ∧
    (cast a).getOpType! dst.raw = .gmir .g_trunc ∧
    (cast a).getResultTypes! dst.raw = #[(ValuePtr.blockArgument a).getType! src.raw] ∧
    (cast a).getOperands! dst.raw = #[.blockArgument a] ∧
    (cast a).getProperties! dst.raw (OpCode.gmir .g_trunc) = ({ nsw := false, nuw := false } : NswNuwProperties) ∧
    (cast a).getSuccessors! dst.raw = #[] ∧ (cast a).getNumRegions! dst.raw = 0
  opList : ∀ b (bIn : b.InBounds src.raw),
    b.opList dst (ctxSame.blockIn bIn) =
      (if b = block then (selectedArgs block done).reverse.map cast else []) ++ b.opList src bIn

private theorem WidenArgumentsFrame.init {src : WfIRContext OpCode} {block : BlockPtr} {cast} :
    WidenArgumentsFrame src src block [] cast :=
  ⟨fun o oIn => (OpSame.refl oIn).congr (fun v _ => by cases v <;> simp [lowerArgs, selectedArgs]),
    CtxSame.refl, fun _ => id, PhiAllocation.refl _, fun _ _ _ => rfl, by simp, by simp [selectedArgs]⟩

private theorem WidenArgumentsFrame.step {src ctx ctx' : WfIRContext OpCode} {block : BlockPtr}
    {done : List (Nat × Nat)} {cast} {i w : Nat} {trunc : OperationPtr}
    (inv : WidenArgumentsFrame src ctx block done cast)
    (argIn : (⟨block, i⟩ : BlockArgumentPtr).InBounds src.raw)
    (newIndex : i ∉ done.map Prod.fst)
    (step : WidenArgumentStep ctx ctx' (InsertPoint.atStart! block src.raw) ⟨block, i⟩ w trunc) :
    WidenArgumentsFrame src ctx' block ((i, w) :: done)
      (fun a => if a = ⟨block, i⟩ then trunc else cast a) := by
  let arg : BlockArgumentPtr := ⟨block, i⟩
  have newArg : arg ∉ selectedArgs block done := by
    intro h
    obtain ⟨⟨j, k⟩, hj, eq⟩ := List.mem_map.mp h
    have eqi : j = i := congrArg BlockArgumentPtr.index eq
    exact newIndex (List.mem_map.mpr ⟨(j, k), hj, eqi⟩)
  have vs : (ValuePtr.blockArgument arg).InBounds src.raw := by simpa [arg] using argIn
  have old : ∀ a ∈ selectedArgs block done, a ≠ arg := fun _ h eq => newArg (eq ▸ h)
  refine ⟨fun o ho => ?_, inv.ctxSame.trans step.ctxSame, fun v hv =>
    (step.types v (inv.bounds v hv)).1,
    PhiAllocation.transCasts inv.allocations (step.allocation.castStep (.inl step.castType)
      step.castSuccessors) (fun o ho => ⟨(step.ops o ho).opType, (step.ops o ho).successors⟩),
    fun v hv hv' => ?_, fun j k hj => ?_, fun b hb => ?_⟩
  · have so := inv.ops o ho
    refine (so.trans (step.ops o so.inBounds)).congr (fun v _ => ?_)
    rcases v with r | a
    · simp [lowerArgs, substArg]
    · change substArg arg trunc (lowerArgs (selectedArgs block done) cast (.blockArgument a)) =
        lowerArgs (arg :: selectedArgs block done) _ (.blockArgument a)
      by_cases eq : a = arg
      · subst a
        simp [lowerArgs, substArg, newArg, arg]
      · have neq : a ≠ ⟨block, i⟩ := eq
        by_cases ha : a ∈ selectedArgs block done <;> simp [lowerArgs, substArg, eq, ha, neq]
  · have ha : v ≠ .blockArgument arg := hv' arg (by simp [selectedArgs, arg])
    rw [(step.types v (inv.bounds v hv)).2, ite_eq_right ha]
    exact inv.otherTypes v hv (fun a h => hv' a (List.mem_cons_of_mem _ h))
  · rcases List.mem_cons.mp hj with eq | hj
    · cases eq
      have before := inv.otherTypes (.blockArgument arg) vs (fun a h eq =>
        old a h (ValuePtr.blockArgument.inj eq).symm)
      have typ := (step.types (.blockArgument arg) (inv.bounds _ vs)).2
      simp only [arg, ↓reduceIte] at typ
      simp only [↓reduceIte]
      exact ⟨argIn, typ, step.castIn, fun h => step.castNotIn (inv.ops _ h).inBounds,
        step.castType, before ▸ step.castResultTypes, step.castOperands, step.castProperties,
        step.castSuccessors, step.castNumRegions⟩
    · let a : BlockArgumentPtr := ⟨block, j⟩
      have ha : a ∈ selectedArgs block done := List.mem_map.mpr ⟨(j, k), hj, rfl⟩
      have ne : a ≠ arg := old a ha
      obtain ⟨bound, typ, cin, fresh, code, results, operands, props, successors, regions⟩ :=
        inv.args j k hj
      have hc := step.ops (cast a) cin
      have vIn : (ValuePtr.blockArgument a).InBounds src.raw := by simpa [a] using bound
      have ta := (step.types (.blockArgument a) (inv.bounds _ vIn)).2
      have ne' : (⟨block, j⟩ : BlockArgumentPtr) ≠ ⟨block, i⟩ := ne
      simp only [ne', ↓reduceIte]
      simp only [a, ValuePtr.blockArgument.injEq, ne', ↓reduceIte] at ta
      exact ⟨bound, ta.trans typ, hc.inBounds, fresh, hc.opType.trans code,
        hc.resultTypes.trans results, by rw [hc.operands, operands]; simp [substArg, ne, a, arg],
        (hc.properties _).trans props, hc.successors.trans successors, hc.numRegions.trans regions⟩
  · have frame := insertAtStart_after_prefix (newOp := trunc)
        (prefixOps := (selectedArgs block done).reverse.map cast)
        (BlockArgumentPtr.inBounds_def.mp argIn).1 hb (by
          intro o ho
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
          obtain ⟨⟨j, k⟩, hj, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
          exact (inv.args j k hj).2.2.2.1)
    rw [step.opList b (inv.ctxSame.blockIn hb), inv.opList b hb, frame]
    have hmap : (selectedArgs block done).reverse.map (fun a => if a = arg then trunc else cast a) =
        (selectedArgs block done).reverse.map cast :=
      List.map_congr_left (fun a ha => by simp [old a (List.mem_reverse.mp ha)])
    change _ = (if b = block then ((arg :: selectedArgs block done).reverse.map _) else []) ++ _
    rw [List.reverse_cons, List.map_append, hmap]
    simp [arg]

/-- Compose the truncation frames over the fold in the executable helper. -/
private theorem WidenArgumentsFrame.foldlM {src ctx ctx' : WfIRContext OpCode} {block : BlockPtr}
    {done todo : List (Nat × Nat)} {cast : BlockArgumentPtr → OperationPtr}
    (inv : WidenArgumentsFrame src ctx block done cast)
    (bounds : ∀ i ∈ todo.map Prod.fst, (⟨block, i⟩ : BlockArgumentPtr).InBounds src.raw)
    (distinct : (todo.map Prod.fst).Nodup) (disjoint : ∀ i ∈ todo.map Prod.fst, i ∉ done.map Prod.fst)
    (h : todo.foldlM (fun c p => widenBlockArgument (InsertPoint.atStart! block src.raw)
      ⟨block, p.1⟩ p.2 c) ctx = some ctx') :
    ∃ casts, WidenArgumentsFrame src ctx' block (todo.reverse ++ done) casts := by
  induction todo generalizing done cast ctx with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst ctx'
    exact ⟨cast, by simpa using inv⟩
  | cons p todo ih =>
    obtain ⟨i, w⟩ := p
    simp only [List.foldlM_cons, bind, Option.bind] at h
    split at h
    next => contradiction
    next middle run =>
      have hIn := bounds i (by simp)
      have hIn' : (⟨block, i⟩ : BlockArgumentPtr).InBounds ctx.raw := by
        simpa using inv.bounds (.blockArgument ⟨block, i⟩) (by simpa using hIn)
      obtain ⟨trunc, truncStep⟩ := widenBlockArgument_spec hIn' run
      have inv' := inv.step hIn (disjoint i (by simp)) truncStep
      simp only [List.map_cons, List.nodup_cons] at distinct
      obtain ⟨casts, final⟩ := ih inv' (fun j hj => bounds j (by simp [hj])) distinct.2
        (fun j hj => by
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨fun eq => distinct.1 (eq ▸ hj), disjoint j (by simp [hj])⟩) h
      exact ⟨casts, by simpa using final⟩

/-- All selected arguments now have their requested widths, and the truncations restoring their
old types appear at the start of the block in the order given by `args`. -/
theorem widenBlockArgument_fold_spec {ctx ctx' : WfIRContext OpCode} {block : BlockPtr}
    {args : List (Nat × Nat)}
    (bounds : ∀ i ∈ args.map Prod.fst, (⟨block, i⟩ : BlockArgumentPtr).InBounds ctx.raw)
    (distinct : (args.map Prod.fst).Nodup)
    (h : args.foldlM (fun c p => widenBlockArgument (InsertPoint.atStart! block ctx.raw)
      ⟨block, p.1⟩ p.2 c) ctx = some ctx') :
    ∃ casts, WidenArgumentsFrame ctx ctx' block args.reverse casts := by
  simpa using WidenArgumentsFrame.foldlM
    (WidenArgumentsFrame.init (cast := fun _ => default)) bounds distinct (by simp) h

end Veir.Legalization.CTreeProofs
