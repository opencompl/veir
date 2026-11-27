import Veir.Parser.LLVMLowering

/-! Every module described by the lowering specification is accepted by the lowering. -/

namespace Veir.LLVMLowering

open LLVMParserProp NameResolutionSketch

namespace Complete

variable {f : ResolvedFunction}

theorem lowerType_inj {a b : LLType} (h : lowerType a = lowerType b) : a = b := by
  cases a; cases b
  have := congrArg Subtype.val h
  simp only [lowerType, TypeAttr.of_val] at this
  grind [IntegerType.signless]

/-! ## Types in a specified lowering -/

theorem MatchesOp.typeOf_result {D : Type} [HasOpInfo D] [HasDialect OpCode D] {code : D}
    {props : propertiesOf code} (h : MatchesOp ctx op code #[t] vs rs props attrs) :
    typeOf ctx.raw (.opResult (op.getResult 0)) = t := by
  have hts : op.getResultTypes! ctx.raw = #[t] := by grind [MatchesOp]
  have hi : 0 < op.getNumResults! ctx.raw := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hts]; simp
  simpa [typeOf, OperationPtr.getResultTypes!.getElem!_eq hi] using congrArg (·[0]!) hts

theorem binTile_typed (h : LowersResolvedInstTile ctx values (.bin (.bin opc ty l r), i) tile)
    (hv : values (.inst i) = some v) : typeOf ctx.raw v = lowerType ty := by
  obtain ⟨_, _, _, _, op, _, _, _, hd, hm⟩ := h
  cases hv.symm.trans hd; exact MatchesOp.typeOf_result hm

theorem LowersBlockArgs.typed {id : BlockId} (h : LowersBlockArgs ctx values f id insts dst)
    (hi : (.phi ty incoming, i) ∈ insts) (hv : values (.inst i) = some v) : typeOf ctx v = lowerType ty := by
  obtain ⟨_, hf, hr⟩ := h
  obtain ⟨phi, hp, rfl, _⟩ := hf.mem_of_matches hi ⟨_, rfl, by simp [ResolvedInst.phiType]⟩
  obtain ⟨_, _, _, he, ht, hd, _⟩ := resolvesList_mem_left hr hp
  cases he; cases hv.symm.trans hd; exact ht

theorem locate_inst {L : List ResolvedBlock} {i : Nat} {x : ResolvedInst} (h : (L.flatMap (·.insts))[i]? = some x) :
    ∃ k, ∃ b : ResolvedBlock, L[k]? = some b ∧ (x, i) ∈ b.insts.zipIdx ((L.take k).map (·.insts.length)).sum := by
  induction L generalizing i with
  | nil => simp at h
  | cons b L ih =>
    rw [List.flatMap_cons, List.getElem?_append] at h
    split at h
    · exact ⟨0, b, by simp, by simpa [List.mk_mem_zipIdx_iff_le_and_getElem?_sub] using h⟩
    · obtain ⟨k, b', hk, hm⟩ := ih h
      refine ⟨k + 1, b', by simpa using hk, ?_⟩
      simp only [List.mk_mem_zipIdx_iff_le_and_getElem?_sub] at hm ⊢
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      exact ⟨by omega, by rw [← hm.2]; congr 1; omega⟩

/-- Every specified definition carries the lowered type of its resolved value. -/
def SpecTyped (ctx : IRContext OpCode) (f : ResolvedFunction) (values : ValueMap) : Prop :=
  ∀ id ty v, f.valueType id = some ty → values id = some v → typeOf ctx v = lowerType ty

theorem instTile_typed (h : ResolvesList (LowersResolvedInstTile ctx values) insts tiles)
    (hm : (.bin (.bin opc ty l r), i) ∈ insts) (hv : values (.inst i) = some v) :
    typeOf ctx.raw v = lowerType ty :=
  have ⟨_, ht⟩ := resolvesList_mem_left h hm; binTile_typed ht hv

theorem LowersFunction.specTyped (hentry : LowersEntry ctx f body values entry)
    (hblocks : ∀ i dst, i ≠ 0 → body i = some dst → LowersBlock ctx f body values i dst)
    (hbody : ∀ i, i < f.blocks.size → ∃ dst, body i = some dst) : SpecTyped ctx.raw f values := by
  obtain ⟨src, tiles, _, hs, _, ha, hp, hnone, hi, _⟩ := hentry
  rintro (i | i) ty v hty hv
  · have ht := functionValues_param_type (blocks := []) (groups := []) (i := i) ha
    rw [functionValues_param ha, ← hp, hv, hty] at ht; simpa using ht
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hty
    obtain ⟨k, b, hk, hm⟩ := locate_inst hx
    have hk' : f.blocks[k]? = some b := by simpa using hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · obtain rfl : b = src := by simp_all
      cases x with
      | bin bin => cases bin; exact instTile_typed hi (by simpa using hm) hv
      | phi => exact absurd (hnone _ (List.fst_mem_of_mem_zipIdx hm)) (by simp [ResolvedInst.phiType])
    · obtain ⟨dst, hd⟩ := hbody k (Array.getElem?_eq_some_iff.mp hk').1
      obtain ⟨src', _, _, hs', _, _, hargs, htiles, _⟩ := hblocks k dst (Nat.pos_iff_ne_zero.mp hpos) hd
      obtain rfl : b = src' := by simp_all
      cases x with
      | bin bin => cases bin; exact instTile_typed htiles hm hv
      | phi => exact LowersBlockArgs.typed hargs hm hv

theorem term_tile (hentry : LowersEntry ctx f body values entry)
    (hblocks : ∀ i dst, i ≠ 0 → body i = some dst → LowersBlock ctx f body values i dst)
    (hbody : ∀ i, i < f.blocks.size → ∃ dst, body i = some dst) (hs : f.blocks[src]? = some b) :
    ∃ tile, LowersTerminatorTile ctx f body values src b.terminator tile := by
  rcases Nat.eq_zero_or_pos src with rfl | hpos
  · obtain ⟨_, _, tile, he, _, _, _, _, _, ht, _⟩ := hentry; cases hs.symm.trans he; exact ⟨tile, ht⟩
  · obtain ⟨dst, hd⟩ := hbody src (Array.getElem?_eq_some_iff.mp hs).1
    obtain ⟨_, _, tile, he, _, _, _, _, ht, _⟩ := hblocks src dst (Nat.pos_iff_ne_zero.mp hpos) hd
    cases hs.symm.trans he; exact ⟨tile, ht⟩

theorem term_edge (h : LowersTerminatorTile ctx f blocks values src t tile) (hd : dst ∈ t.successors) :
    ∃ p args, LowersEdge ctx f blocks values src dst p args := by
  cases t with
  | ret => simp [ResolvedTerminator.successors] at hd
  | br => obtain ⟨_, _, _, he, _⟩ := h; simp [ResolvedTerminator.successors] at hd; exact hd ▸ ⟨_, _, he⟩
  | condBr =>
    obtain ⟨_, _, _, _, _, _, _, _, _, hy, hn, _⟩ := h
    simp only [ResolvedTerminator.successors, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨_, _, hy⟩
    · exact ⟨_, _, hn⟩

theorem LowersEdge.ref_typed {id : ValueId} (h : LowersEdge ctx f blocks values src dst b args)
    (ht : f.blocks[dst]? = some target) (hp : .phi ty incoming ∈ target.insts)
    (ha : PhiInputsAgree incoming) (hi : (src, .ref id) ∈ incoming) :
    ∃ v, values id = some v ∧ typeOf ctx.raw v = lowerType ty := by
  obtain ⟨_, _, block, phis, he, hf, hr⟩ := h
  cases ht.symm.trans he
  obtain ⟨_, hphi, rfl, _⟩ := hf.mem_of_matches hp ⟨_, rfl, by simp [ResolvedInst.phiType]⟩
  obtain ⟨arg, ⟨input, hin, hop⟩, hty⟩ := resolvesList_mem_left hr hphi
  cases ha _ hin _ hi rfl
  exact ⟨_, hop.1, by simpa [ResolvedInst.phiType] using hty.symm⟩

theorem HasPredEdges.src {incoming : List (BlockId × ResolvedValue)} {src : BlockId} (h : HasPredEdges f dst (incoming.map Prod.fst)) (hi : (src, v) ∈ incoming) :
    ∃ b, f.blocks[src]? = some b ∧ dst ∈ b.terminator.successors := by
  have hc : 0 < (incoming.map Prod.fst).count src := List.count_pos_iff.mpr (List.mem_map_of_mem (f := Prod.fst) hi)
  have he := h src
  cases hb : f.blocks[src]? <;> simp only [hb] at he
  · omega
  · exact ⟨_, rfl, List.count_pos_iff.mp (he ▸ hc)⟩

theorem valid_ref {id : ValueId} (h : ValidResolvedValue f.header.params.length
    (f.blocks.toList.flatMap (·.insts)).length (.ref id)) : ∃ ty, f.valueType id = some ty := by
  cases id with
  | param i => exact ⟨_, by simp [ResolvedFunction.valueType, show i < _ from h]; rfl⟩
  | inst i =>
    rcases hx : (f.blocks.toList.flatMap (·.insts))[i]'h with (⟨_, ty, _, _⟩ | ⟨ty, _⟩) <;>
      exact ⟨ty, by simp [ResolvedFunction.valueType, List.getElem?_eq_getElem h, hx]⟩

/-- The lowering's phi type checks pass. -/
def PhiTyped (f : ResolvedFunction) : Prop :=
  ∀ (dst : BlockId) (target : ResolvedBlock) ty incoming src (id : ValueId), f.blocks[dst]? = some target → .phi ty incoming ∈ target.insts →
    (src, ResolvedValue.ref id) ∈ incoming → f.valueType id = some ty

/-- The lowering's branch condition type checks pass. -/
def CondTyped (f : ResolvedFunction) : Prop :=
  ∀ (src : BlockId) (b : ResolvedBlock) (id : ValueId) yes no, f.blocks[src]? = some b → b.terminator = .condBr (.ref id) yes no →
    f.valueType id = some (.int 1)

theorem mem_of_get {i : Nat} (h : f.blocks[i]? = some b) : b ∈ f.blocks.toList :=
  Array.mem_toList_iff.mpr (Array.mem_of_getElem? h)

theorem LowersFunction.typed (h : LowersFunction ctx f op) : PhiTyped f ∧ CondTyped f := by
  have hc := checkBlocks_accepts_iff.mp h.checkBlocks
  obtain ⟨hv, _, body, _, values, _, _, hs, _, hentry, hblocks⟩ := h
  have hbody i (hi : i < f.blocks.size) : ∃ dst, body[i]? = some dst := ⟨body[i], by simp [hs, hi]⟩
  have spec := LowersFunction.specTyped hentry hblocks hbody
  refine ⟨fun dst target ty incoming src id ht hp hi => ?_, fun src b id yes no hb ht => ?_⟩
  · obtain ⟨ha, hpred⟩ := (hc.2.2 target dst (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using ht))).2 ty incoming hp
    obtain ⟨_, hb, hd⟩ := HasPredEdges.src hpred hi
    obtain ⟨_, he⟩ := term_tile hentry hblocks hbody hb
    obtain ⟨_, _, he⟩ := term_edge he hd
    obtain ⟨v, hvv, htv⟩ := LowersEdge.ref_typed he ht hp ha hi
    obtain ⟨ty', hty'⟩ := valid_ref (((hv _ (mem_of_get ht)).1 _ hp) _ hi).2
    rw [hty', lowerType_inj ((spec _ _ _ hty' hvv).symm.trans htv)]
  · obtain ⟨_, htile⟩ := term_tile hentry hblocks hbody hb
    have hvt := (hv _ (mem_of_get hb)).2
    rw [ht] at htile hvt
    obtain ⟨x, _, _, _, _, _, _, hx, htx, _⟩ := htile
    obtain ⟨ty', hty'⟩ := valid_ref hvt.1
    rw [hty', lowerType_inj ((spec _ _ _ hty' hx.1).symm.trans htx)]

/-! ## Monotone lowering steps -/

variable {ctx ctx' ctx'' : WfIRContext OpCode}

/-- Lowering steps keep pointers allocated, block signatures fixed, and region owners unchanged. -/
structure Grew (ctx ctx' : WfIRContext OpCode) : Prop where
  bounds : ∀ p : GenericPtr, p.InBounds ctx.raw → p.InBounds ctx'.raw
  arguments : ∀ b : BlockPtr, b.InBounds ctx.raw → b.getArgumentTypes! ctx'.raw = b.getArgumentTypes! ctx.raw
  regions : ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw

theorem Grew.refl : Grew ctx ctx := ⟨fun _ h => h, fun _ _ => rfl, fun _ => rfl⟩

theorem Grew.trans (h : Grew ctx ctx') (h' : Grew ctx' ctx'') : Grew ctx ctx'' :=
  ⟨fun p hp => h'.bounds p (h.bounds p hp), fun b hb => (h'.arguments b (h.bounds (.block b) hb)).trans
    (h.arguments b hb), fun r => (h'.regions r).trans (h.regions r)⟩

theorem Grew.of (hf : LoweringFrame ctx ctx' ws ins ex)
    (hr : ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw) : Grew ctx ctx' :=
  ⟨hf.bounds, hf.arguments, hr⟩

/-- Every successful run of `x` grows the context. -/
def Grows (x : LowerM α) : Prop := ∀ ctx a ctx', x.run ctx = .ok (a, ctx') → Grew ctx ctx'

theorem Grows.pure {a : α} : Grows (pure a : LowerM α) := fun _ _ _ h => by
  cases lowerM_pure_ok.mp h; exact Grew.refl

theorem Grows.bind {x : LowerM α} {k : α → LowerM β} (hx : Grows x) (hk : ∀ a, Grows (k a)) :
    Grows (x >>= k) := fun _ _ _ h =>
  have ⟨_, _, h₁, h₂⟩ := lowerM_bind_ok.mp h; (hx _ _ _ h₁).trans (hk _ _ _ _ h₂)

theorem Grows.mapM {xs : List α} {g : α → LowerM β} (hg : ∀ x, Grows (g x)) : Grows (xs.mapM g) := by
  induction xs with
  | nil => exact Grows.pure
  | cons x xs ih => rw [List.mapM_cons]; exact (hg x).bind fun _ => ih.bind fun _ => Grows.pure

theorem Grows.forM {xs : List α} {g : α → LowerM Unit} (hg : ∀ x, Grows (g x)) : Grows (xs.forM g) := by
  induction xs with
  | nil => exact Grows.pure
  | cons x xs ih => exact (hg x).bind fun _ => ih

section Primitives

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem emit_regions {code : Llvm} {props : propertiesOf code} {insert : Bool}
    (h : (emit code types operands regions props block insert).run ctx = .ok (op, ctx'))
    (r : RegionPtr) (hr : r ∉ regions) : r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  simp [emit] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  rename_i ho hrs
  by_cases hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw
  · rw [dite_eq_left hi] at h
    rcases hc : WfRewriter.createOp ctx code types operands #[] regions props _ ho (by simp) hrs hi with _ | ⟨c, o⟩ <;> simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [RegionPtr.getParent!_WfRewriter_createOp hc]; simp [hr]
  · simp [hi] at h

theorem Grows.emit {code : Llvm} {props : propertiesOf code} {insert : Bool} :
    Grows (emit code types operands #[] props block insert) := fun _ _ _ h =>
  .of (emit_spec h).1 fun r => emit_regions h r (by simp)

theorem Grows.emitBranch {code : Llvm} {props : propertiesOf code} :
    Grows (emitBranch code operands successors props block) := fun ctx _ ctx' h => by
  refine .of (emitBranch_frame h) fun r => ?_
  simp [LLVMLowering.emitBranch] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  rename_i ho hs hi
  rcases hc : WfRewriter.createOp ctx code #[] operands successors #[] props (some (.atEnd block))
    ho hs (by simp) (by simpa using hi) with _ | ⟨c, op⟩ <;> simp [hc] at h
  obtain rfl : c = ctx' := h
  rw [RegionPtr.getParent!_WfRewriter_createOp hc]; simp

theorem Grows.pushValue : Grows (pushValue op v) := fun _ _ _ h => by
  obtain ⟨ho, hv, rfl⟩ := pushValue_ok h
  exact .of (LoweringFrame.pushOperand ho hv) fun r => by simp [WfRewriter.pushOperand]

theorem Grows.attachInst : Grows (attachInst block op) := fun ctx _ _ h => by
  obtain ⟨ho, hi, hc⟩ := attachInst_ok h
  have hr := WfRewriter_insertOp_raw hc
  exact ⟨fun p hp => by grind, fun b hb => by apply Array.ext <;> grind,
    fun r => RegionPtr.getParent!_wfRewriter_insertOp hc⟩

theorem Grows.throw : Grows (throw e : LowerM α) := fun _ _ _ h => by simp at h

theorem Grows.forIn {xs : List α} {g : α → β → LowerM (ForInStep β)} (hg : ∀ x b, Grows (g x b)) :
    Grows (forIn xs b g) := by
  induction xs generalizing b with
  | nil => exact Grows.pure
  | cons x xs ih => rw [List.forIn_cons]; exact (hg x b).bind fun r => by cases r <;> first | exact Grows.pure | exact ih

end Primitives

theorem wfCreateBlock_spec
    (h : WfRewriter.createBlock ctx ts (some (.atEnd region)) hi = some (ctx', b)) :
    Grew ctx ctx' ∧ b.InBounds ctx'.raw ∧ b.getArgumentTypes! ctx'.raw = ts := by
  have hbr := createBlock_raw h
  have hm := Rewriter.createBlock_inBounds_mono (heq := hbr)
  unfold Rewriter.createBlock at hbr; simp only [Option.bind_eq_bind, Option.bind] at hbr
  split at hbr <;> try contradiction
  split at hbr <;> try contradiction
  simp only [Option.some.injEq, Prod.mk.injEq] at hbr; rcases hbr with ⟨hc, rfl⟩
  refine ⟨⟨hm, fun b hb => ?_, fun r => ?_⟩, by grind, Array.ext (by grind (gen := 20)) (by grind (gen := 20))⟩
  · apply Array.ext <;> grind (gen := 20)
  · rw [← hc]; simp_getset; grind

section Creation

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem createBlock_ok (h : (createBlock region ts).run ctx = .ok (b, ctx')) :
    Grew ctx ctx' ∧ b.InBounds ctx'.raw ∧ b.getArgumentTypes! ctx'.raw = ts := by
  simp [createBlock] at h
  split at h <;> try simp at h
  rename_i hi
  rcases hc : WfRewriter.createBlock ctx ts (some (.atEnd region)) (by simpa using hi) with _ | ⟨c, o⟩ <;> simp [hc] at h
  obtain ⟨rfl, rfl⟩ := h
  exact wfCreateBlock_spec hc

theorem wfCreateBlock_total (hs : AllocationSafe ctx.raw) (hr : region.InBounds ctx.raw) :
    ∃ hi : (some (BlockInsertPoint.atEnd region)).maybe BlockInsertPoint.InBounds ctx.raw, ∃ ctx' b,
      WfRewriter.createBlock ctx ts (some (.atEnd region)) hi = some (ctx', b) ∧ AllocationSafe ctx'.raw := by
  obtain ⟨raw, b, hc, hs'⟩ := hs.createBlock_total (ts := ts) ctx.wellFormed.inBounds hr
  exact ⟨by grind, ⟨raw, by grind [Rewriter.createBlock_WellFormed]⟩, b, createBlock_of_raw hc, hs'⟩

theorem createBlock_total (hs : AllocationSafe ctx.raw) (hr : region.InBounds ctx.raw) :
    ∃ b ctx', (createBlock region ts).run ctx = .ok (b, ctx') ∧ AllocationSafe ctx'.raw := by
  obtain ⟨hi, c, b, hc, hs'⟩ := wfCreateBlock_total (ts := ts) hs hr
  exact ⟨b, c, by simp [createBlock, hi, hc], hs'⟩

theorem createBody_ok (h : (createBody ts).run ctx = .ok ((region, entry), ctx')) :
    (∀ p : GenericPtr, p.InBounds ctx.raw → p.InBounds ctx'.raw) ∧ region.InBounds ctx'.raw ∧
      region.getParent! ctx'.raw = none ∧ entry.InBounds ctx'.raw ∧ entry.getArgumentTypes! ctx'.raw = ts := by
  simp [createBody] at h
  rcases hcr : WfRewriter.createRegion ctx with _ | ⟨c, r⟩ <;> simp [hcr] at h
  split at h <;> try simp at h
  rename_i hi
  rcases hc : WfRewriter.createBlock c ts (some (.atEnd r)) (by simpa using hi) with _ | ⟨d, o⟩ <;> simp [hc] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  have hraw : Rewriter.createRegion ctx.raw = some (c.raw, r) := by
    unfold WfRewriter.createRegion at hcr; split at hcr <;> grind
  obtain ⟨hg, hb, ht⟩ := wfCreateBlock_spec hc
  exact ⟨fun p hp => hg.bounds p (by grind), hg.bounds (.region _) (by grind),
    (hg.regions _).trans (by grind), hb, ht⟩

theorem createBody_total (hs : AllocationSafe ctx.raw) :
    ∃ p ctx', (createBody ts).run ctx = .ok (p, ctx') ∧ AllocationSafe ctx'.raw := by
  obtain ⟨raw, r, hc, hs'⟩ := hs.allocateRegion
  let c : WfIRContext OpCode := ⟨raw, by grind [IRContext.wellFormed_Rewriter_createRegion]⟩
  have hcr : WfRewriter.createRegion ctx = some (c, r) := by
    unfold WfRewriter.createRegion; split <;> rename_i heq <;> simp_all <;> grind
  obtain ⟨hi, d, b, hb, hs''⟩ := wfCreateBlock_total (ctx := c) (ts := ts) hs' (show r.InBounds raw by grind)
  exact ⟨(r, b), d, by simp [createBody, hcr, show (BlockInsertPoint.atEnd r).InBounds c.raw by simpa using hi, hb], hs''⟩

end Creation

section Wiring

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem insertOp_of_raw {ho : op.InBounds ctx.raw} {hi : ip.InBounds ctx.raw}
    (h : Rewriter.insertOp ctx.raw op ip ho hi (by grind) = some raw) :
    ∃ hw, WfRewriter.insertOp ctx op ip ho hi = some ⟨raw, hw⟩ := by
  unfold WfRewriter.insertOp; split <;> simp_all; subst raw; grind [Rewriter.insertOp_WellFormed]

theorem pushValue_run (ho : op.InBounds ctx.raw) (hv : v.InBounds ctx.raw) :
    (pushValue op v).run ctx = .ok ((), WfRewriter.pushOperand ctx op v ho hv) := by
  simp [pushValue, ho, hv]

theorem attachInst_total (hs : AllocationSafe ctx.raw) (ho : op.InBounds ctx.raw)
    (hb : block.InBounds ctx.raw) (hp : op.getParent! ctx.raw = none) :
    ∃ ctx', (attachInst block op).run ctx = .ok ((), ctx') ∧ AllocationSafe ctx'.raw ∧
      LoweringFrame ctx ctx' [op] [block] [] := by
  obtain ⟨raw, hr⟩ := insertOp_total ctx.wellFormed.inBounds ho hb hp
  obtain ⟨hw, hi⟩ := insertOp_of_raw hr
  exact ⟨⟨raw, hw⟩, by simp [attachInst, ho, show (InsertPoint.atEnd block).InBounds ctx.raw by grind, hi],
    hs.insertOp hr, LoweringFrame.insertOp hi hp⟩

/-- Every reference among an instruction's operands is defined. -/
def OperandsDefined (values : ValueMap) : ResolvedBinary → Prop
  | .bin _ _ l r => ∀ id, (l = .ref id ∨ r = .ref id) → (values id).isSome

theorem lowerOperand_push_total {D : Type} [HasOpInfo D] [HasDialect OpCode D] {code : D}
    {props : propertiesOf code} (hs : AllocationSafe ctx.raw)
    (hm : MatchesOp ctx op code ts vs rs props attrs) (hb : block.InBounds ctx.raw)
    (hd : op.getParent! ctx.raw = none) (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (hr : ∀ id, val = .ref id → (values id).isSome) :
    ∃ v c ctx', (lowerOperand (lookupValue values) block ty val).run ctx = .ok (v, c) ∧
      (pushValue op v).run c = .ok ((), ctx') ∧ AllocationSafe ctx'.raw ∧
      LoweringFrame ctx ctx' [op] [block] [] ∧ MatchesOp ctx' op code ts (vs.push v) rs props attrs ∧
      op.getParent! ctx'.raw = none := by
  obtain ⟨os, hc⟩ := ctx.wellFormed.opChain block hb
  obtain ⟨c, v, hl, hs'⟩ := lowerOperand_total (ty := ty) hs hb hr
  obtain ⟨hf, hvi, _⟩ := lowerOperand_spec hl hc hv
  have hp := pushValue_run (hf.bounds (.operation op) hm.1) hvi
  obtain ⟨hf', hm', hd', _⟩ := lowerOperand_push_spec hm hc hd hl hp hv
  exact ⟨v, c, _, hl, hp, hs'.pushOperand, hf', hm', hd'⟩

theorem wireBinary_total (hs : AllocationSafe ctx.raw) (ha : BinaryAllocated ctx inst op)
    (hb : block.InBounds ctx.raw) (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (hr : OperandsDefined values inst) :
    ∃ ctx', (wireBinary (lookupValue values) block (inst, op)).run ctx = .ok ((), ctx') ∧
      AllocationSafe ctx'.raw ∧ LoweringFrame ctx ctx' [op] [block] [] := by
  rcases inst with ⟨opc, ty, lhs, rhs⟩
  obtain ⟨vl, c, d, hl, hp, hs, hf, hm, hd⟩ := lowerOperand_push_total hs ha.1 hb ha.2 hv
    (fun id h => hr id (.inl h))
  obtain ⟨vr, e, g, hr', hq, hs, hg, hm, hd⟩ := lowerOperand_push_total (ty := ty) hs hm
    (hf.bounds (.block block) hb) hd (fun i v h => hf.bounds (.value v) (hv i v h)) (fun id h => hr id (.inr h))
  obtain ⟨k, hk, hs, hh⟩ := attachInst_total hs hm.1 ((hf.trans hg).bounds (.block block) hb) hd
  refine ⟨k, ?_, hs, ((hf.trans hg).trans hh).mono (by simp) (by simp) (by simp)⟩
  simp only [wireBinary, lowerM_bind_ok]
  exact ⟨vl, c, hl, (), d, hp, vr, e, hr', (), g, hq, hk⟩

theorem wireList_total {ys : List (ResolvedBinary × OperationPtr)} (hs : AllocationSafe ctx.raw)
    (hb : block.InBounds ctx.raw) (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (ha : ∀ x ∈ ys, BinaryAllocated ctx x.1 x.2 ∧ OperandsDefined values x.1) (hn : (ys.map Prod.snd).Nodup) :
    ∃ ctx', (ys.forM (wireBinary (lookupValue values) block)).run ctx = .ok ((), ctx') ∧
      AllocationSafe ctx'.raw ∧ LoweringFrame ctx ctx' (ys.map Prod.snd) [block] [] := by
  induction ys generalizing ctx with
  | nil => exact ⟨ctx, rfl, hs, LoweringFrame.refl.mono (by simp) (by simp) (by simp)⟩
  | cons x ys ih =>
    obtain ⟨hx, hd⟩ := List.nodup_cons.mp hn
    obtain ⟨c, h₁, hs, hf⟩ := wireBinary_total hs (ha x List.mem_cons_self).1 hb hv (ha x List.mem_cons_self).2
    obtain ⟨d, h₂, hs, hg⟩ := ih hs (hf.bounds (.block block) hb) (fun i v h => hf.bounds (.value v) (hv i v h))
      (fun y hy => ⟨(ha y (List.mem_cons_of_mem _ hy)).1.frame hf fun he => hx (by
        simpa [← List.mem_singleton.mp he] using List.mem_map_of_mem (f := Prod.snd) hy),
        (ha y (List.mem_cons_of_mem _ hy)).2⟩) hd
    exact ⟨d, lowerM_bind_ok.mpr ⟨(), c, h₁, h₂⟩, hs,
      (hf.trans hg).mono (by grind) (by simp) (by simp)⟩

end Wiring

/-! ## Terminators -/

def TermReady (ctx : WfIRContext OpCode) (f : ResolvedFunction) (blocks : Array BlockPtr)
    (values : ValueMap) (src : BlockId) : ResolvedTerminator → Prop
  | .ret v => ∀ id, v = .ref id → (values id).isSome
  | .br dst => dst ≠ 0 ∧ EdgeReady ctx f blocks values src dst
  | .condBr c y n => y ≠ 0 ∧ n ≠ 0 ∧ EdgeReady ctx f blocks values src y ∧
      EdgeReady ctx f blocks values src n ∧
      ∀ id, c = .ref id → ∃ v, values id = some v ∧ typeOf ctx.raw v = lowerType (.int 1)

theorem TermReady.frame {blocks : Array BlockPtr} (h : TermReady ctx f blocks values src t)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    TermReady ctx' f blocks values src t := by
  cases t with
  | ret => exact h
  | br => exact ⟨h.1, h.2.frame hf hv⟩
  | condBr =>
    obtain ⟨hy, hn, ey, en, hc⟩ := h
    refine ⟨hy, hn, ey.frame hf hv, en.frame hf hv, fun id he => ?_⟩
    obtain ⟨v, h, ht⟩ := hc id he
    exact ⟨v, h, (hf.valueTypes v (hv id v h)).trans ht⟩

theorem TermReady.nonzero {blocks : Array BlockPtr} (h : TermReady ctx f blocks values src t) :
    ∀ dst ∈ t.successors, dst ≠ 0 := by
  cases t <;> simp_all [ResolvedTerminator.successors, TermReady]

theorem term_total {blocks : Array BlockPtr} (hs : AllocationSafe ctx.raw) (hb : block.InBounds ctx.raw)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) (ht : TermReady ctx f blocks values src t) :
    ∃ ctx', (lowerTerminator f blocks (lookupValue values) block src t).run ctx = .ok ((), ctx') ∧
      AllocationSafe ctx'.raw ∧ LoweringFrame ctx ctx' [] [block] [] := by
  obtain ⟨os, hc⟩ := ctx.wellFormed.opChain block hb
  suffices h : ∃ ctx', (lowerTerminator f blocks (lookupValue values) block src t).run ctx = .ok ((), ctx') ∧
      AllocationSafe ctx'.raw by
    obtain ⟨c, h, hs⟩ := h; exact ⟨c, h, hs, (lowerTerminator_spec h ht.nonzero hc hv).1⟩
  cases t with
  | ret =>
    obtain ⟨d, op, h, hs⟩ := lowerReturn_total (ty := f.header.retType) hs hc hv ht
    exact ⟨d, lowerM_bind_ok.mpr ⟨op, d, h, rfl⟩, hs⟩
  | br => exact lowerTerminator_br_total hs hc ht.2 ht.1 hv
  | condBr => exact lowerTerminator_condBr_total hs hc ht.2.2.1 ht.2.2.2.1 ht.1 ht.2.1 hv ht.2.2.2.2

/-! ## Blocks -/

abbrev Plan := BlockLoweringPlan (BlockId × ResolvedTerminator)

def PlanReady (ctx : WfIRContext OpCode) (f : ResolvedFunction) (blocks : Array BlockPtr)
    (values : ValueMap) (p : Plan) (ops : List OperationPtr) : Prop :=
  p.block.InBounds ctx.raw ∧ ResolvesList (BinaryAllocated ctx) p.insts ops ∧
    (∀ i ∈ p.insts, OperandsDefined values i) ∧ TermReady ctx f blocks values p.terminator.1 p.terminator.2

theorem resolvesList_zip (h : ResolvesList R xs ys) :
    (∀ p ∈ xs.zip ys, R p.1 p.2) ∧ (xs.zip ys).map Prod.snd = ys := by
  induction h with
  | nil => simp
  | cons hr _ ih => exact ⟨by simpa [hr] using ih.1, by simp [ih.2]⟩

theorem PlanReady.frame {blocks : Array BlockPtr} (h : PlanReady ctx f blocks values p ops)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hw : ∀ o ∈ ops, o ∉ ws)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) : PlanReady ctx' f blocks values p ops :=
  ⟨hf.bounds (.block _) h.1, resolvesList_transfer h.2.1 fun _ _ hm ha => ha.frame hf (hw _ hm),
    h.2.2.1, h.2.2.2.frame hf hv⟩

theorem plan_total {blocks : Array BlockPtr} (hs : AllocationSafe ctx.raw)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) (hp : PlanReady ctx f blocks values p ops)
    (hn : ops.Nodup) :
    ∃ ctx', ((p.insts.zip ops).forM (wireBinary (lookupValue values) p.block) >>= fun _ =>
      lowerTerminator f blocks (lookupValue values) p.block p.terminator.1 p.terminator.2).run ctx =
        .ok ((), ctx') ∧ AllocationSafe ctx'.raw ∧ LoweringFrame ctx ctx' ops [p.block] [] := by
  obtain ⟨hb, ha, hd, ht⟩ := hp
  obtain ⟨hz, hm⟩ := resolvesList_zip ha
  obtain ⟨c, h₁, hs, hf⟩ := wireList_total hs hb hv
    (fun x hx => ⟨hz x hx, hd _ (List.of_mem_zip hx).1⟩) (by rw [hm]; exact hn)
  have hv' id v h := hf.bounds (.value v) (hv id v h)
  obtain ⟨d, h₂, hs, hg⟩ := term_total hs (hf.bounds (.block _) hb) hv' (ht.frame hf hv)
  exact ⟨d, lowerM_bind_ok.mpr ⟨(), c, h₁, h₂⟩, hs,
    (hf.trans hg).mono (fun o ho => .inl (by simpa [hm] using ho)) (by simp) (by simp)⟩

theorem mapM_total {xs : List α} {g : α → LowerM β} (P : WfIRContext OpCode → Prop)
    (hg : ∀ x ctx, P ctx → ∃ b ctx', (g x).run ctx = .ok (b, ctx') ∧ P ctx') (h : P ctx) :
    ∃ ys ctx', (xs.mapM g).run ctx = .ok (ys, ctx') ∧ P ctx' := by
  induction xs generalizing ctx with
  | nil => exact ⟨[], ctx, rfl, h⟩
  | cons x xs ih =>
    obtain ⟨b, c, h₁, hc⟩ := hg x ctx h
    obtain ⟨ys, d, h₂, hd⟩ := ih hc
    exact ⟨b :: ys, d, by rw [List.mapM_cons]; exact lowerM_bind_ok.mpr ⟨b, c, h₁, lowerM_bind_ok.mpr ⟨ys, d, h₂, rfl⟩⟩, hd⟩

theorem forIn_total {xs : List α} {g : α → PUnit → LowerM (ForInStep PUnit)}
    (I : List α → WfIRContext OpCode → Prop)
    (hg : ∀ x xs ctx, I (x :: xs) ctx → ∃ ctx', (g x ⟨⟩).run ctx = .ok (.yield ⟨⟩, ctx') ∧ I xs ctx')
    (h : I xs ctx) : ∃ ctx', (forIn xs ⟨⟩ g).run ctx = .ok (⟨⟩, ctx') ∧ I [] ctx' := by
  induction xs generalizing ctx with
  | nil => exact ⟨ctx, rfl, h⟩
  | cons x xs ih =>
    obtain ⟨c, h₁, hc⟩ := hg x xs ctx h
    obtain ⟨d, h₂, hd⟩ := ih hc
    exact ⟨d, by rw [List.forIn_cons]; exact lowerM_bind_ok.mpr ⟨_, c, h₁, h₂⟩, hd⟩

theorem allocGroups_spec {plans : List Plan} {groups : List (List OperationPtr)}
    (h : (plans.mapM fun (p : Plan) => p.insts.mapM (lowerInst p.block)).run ctx = .ok (groups, ctx')) :
    LoweringFrame ctx ctx' [] [] [] ∧
      ResolvesList (fun p ops => ResolvesList (BinaryAllocated ctx') p.insts ops) plans groups ∧
      groups.flatten.Nodup ∧ ∀ op ∈ groups.flatten, ¬op.InBounds ctx.raw := by
  induction plans generalizing ctx groups with
  | nil => cases h; exact ⟨LoweringFrame.refl, .nil, List.nodup_nil, by simp⟩
  | cons p plans ih =>
    simp only [List.mapM_cons, lowerM_bind_ok, lowerM_pure_ok, Prod.mk.injEq] at h
    obtain ⟨ops, c, ho, tail, d, hd, rfl, rfl⟩ := h
    obtain ⟨hf, ha, hn, hnew⟩ := allocateBinaryList_spec ho
    obtain ⟨hg, hs, hnodup, hnew'⟩ := ih hd
    have hin o (hm : o ∈ ops) : o.InBounds c.raw := (resolvesList_right_member ha hm).choose_spec.inBounds
    refine ⟨hf.trans hg, .cons (resolvesList_transfer ha fun _ _ _ h => h.frame hg (by simp)) hs,
      List.nodup_append.mpr ⟨hn, hnodup, fun a ha b hb he => hnew' b hb (he ▸ hin a ha)⟩, ?_⟩
    simp only [List.flatten_cons, List.mem_append]
    exact fun o ho => ho.elim (hnew o) fun hm hi => hnew' o hm (hf.bounds (.operation o) hi)

theorem lowerBlocks_total {plans : List Plan} {V : List (List OperationPtr) → ValueMap}
    {blocks : Array BlockPtr} (hs : AllocationSafe ctx.raw)
    (hready : ∀ groups c, LoweringFrame ctx c [] [] [] →
      ResolvesList (fun p ops => ResolvesList (BinaryAllocated c) p.insts ops) plans groups →
      (∀ id v, V groups id = some v → v.InBounds c.raw) ∧ ∀ p ∈ plans, p.block.InBounds c.raw ∧
        (∀ i ∈ p.insts, OperandsDefined (V groups) i) ∧
        TermReady c f blocks (V groups) p.terminator.1 p.terminator.2) :
    ∃ ctx', (lowerBlocks plans (fun g => lookupValue (V g)) fun values p =>
      lowerTerminator f blocks values p.block p.terminator.1 p.terminator.2).run ctx = .ok ((), ctx') ∧
        AllocationSafe ctx'.raw := by
  obtain ⟨groups, c, ha, hs⟩ := mapM_total (xs := plans) (g := fun p => p.insts.mapM (lowerInst p.block))
    (fun c => AllocationSafe c.raw) (fun p _ hs => have ⟨c, o, h, hs⟩ := allocateBinaryList_total hs; ⟨o, c, h, hs⟩) hs
  obtain ⟨hf, hr, hn, _⟩ := allocGroups_spec ha
  obtain ⟨hv, hp⟩ := hready groups c hf hr
  obtain ⟨hz, hm⟩ := resolvesList_zip hr
  obtain ⟨d, hl, hs, _⟩ := forIn_total (ctx := c) (xs := plans.zip groups) (g := fun x _ => match x with
      | (p, ops) => do
        (p.insts.zip ops).forM (wireBinary (lookupValue (V groups)) p.block)
        lowerTerminator f blocks (lookupValue (V groups)) p.block p.terminator.1 p.terminator.2
        pure (ForInStep.yield PUnit.unit)) (fun rest d =>
      AllocationSafe d.raw ∧ (∀ id v, V groups id = some v → v.InBounds d.raw) ∧
      (∀ x ∈ rest, PlanReady d f blocks (V groups) x.1 x.2) ∧ (rest.flatMap Prod.snd).Nodup)
    (fun ⟨p, ops⟩ rest d ⟨hs, hv, hp, hn⟩ => by
      obtain ⟨hn₁, hn₂, hdisj⟩ := List.nodup_append.mp (by simpa using hn)
      obtain ⟨e, he, hs, hf⟩ := plan_total hs hv (hp _ List.mem_cons_self) hn₁
      obtain ⟨_, c₁, h₁, h₂⟩ := lowerM_bind_ok.mp he
      refine ⟨e, lowerM_bind_ok.mpr ⟨(), c₁, h₁, lowerM_bind_ok.mpr ⟨(), e, h₂, rfl⟩⟩, hs,
        fun i v h => hf.bounds (.value v) (hv i v h), fun x hx => (hp x (List.mem_cons_of_mem _ hx)).frame hf
          (fun o ho hm => hdisj o hm o (List.mem_flatMap.mpr ⟨x, hx, ho⟩) rfl) hv, hn₂⟩)
    ⟨hs, hv, fun x hx => have ⟨hb, hd, ht⟩ := hp x.1 (List.of_mem_zip hx).1; ⟨hb, hz x hx, hd, ht⟩,
      by rw [List.flatMap_def, hm]; exact hn⟩
  exact ⟨d, lowerM_bind_ok.mpr ⟨groups, c, ha, lowerM_bind_ok.mpr ⟨⟨⟩, d, hl, rfl⟩⟩, hs⟩

/-! ## Function values -/

theorem allocated_facts {c : WfIRContext OpCode} (h : ResolvesList (BinaryAllocated c) insts ops) :
    ops.map (fun op => typeOf c.raw (allocatedResult op)) = insts.map (lowerType ∘ binaryType) ∧
      ∀ op ∈ ops, (allocatedResult op).InBounds c.raw := by
  induction h with
  | nil => simp
  | @cons inst op _ _ ha _ ih =>
    rcases inst with ⟨_, _, _, _⟩
    exact ⟨by rw [List.map_cons, ih.1]; simp [allocatedResult, MatchesOp.typeOf_result ha.1, binaryType],
      List.forall_mem_cons.mpr ⟨MatchesOp.result_inBounds ha.1 (by simp), ih.2⟩⟩

theorem blockArg_facts {c : IRContext OpCode} {ts : List LLType} (hb : block.InBounds c)
    (ht : block.getArgumentTypes! c = (ts.map lowerType).toArray) (hj : ts[j]? = some ty) :
    (ValuePtr.blockArgument ⟨block, j⟩).InBounds c ∧ typeOf c (.blockArgument ⟨block, j⟩) = lowerType ty := by
  have hn : j < block.getNumArguments! c := by
    rw [← BlockPtr.getArgumentTypes!.size_eq_getNumArguments!, ht]; simpa using (List.getElem?_eq_some_iff.mp hj).1
  have he := BlockPtr.getArgumentTypes!.getElem!_eq_getArgument hn
  rw [ht] at he
  refine ⟨by grind, ?_⟩
  show (block.getArgument j).getType! c = _
  rw [← he]; simp [hj]

theorem defs_facts {c : WfIRContext OpCode} {b : ResolvedBlock}
    (ha : ResolvesList (BinaryAllocated c) (b.insts.filterMap ResolvedInst.binary) ops)
    (hargs : ∀ j ty, (b.insts.filterMap ResolvedInst.phiType)[j]? = some ty →
      (ValuePtr.blockArgument ⟨block, j⟩).InBounds c.raw ∧
        typeOf c.raw (.blockArgument ⟨block, j⟩) = lowerType ty) :
    (blockDefinitions block 0 b.insts ops).map (typeOf c.raw) = b.insts.map (lowerType ∘ instructionType) ∧
      ∀ v ∈ blockDefinitions block 0 b.insts ops, v.InBounds c.raw :=
  have ⟨ht, hb⟩ := allocated_facts ha
  ⟨blockDefinitions_map_typeOf ht fun j ty h => by simpa using (hargs j ty h).2,
    blockDefinitions_inBounds hb fun j hj => by
      simpa using (hargs j _ (List.getElem?_eq_getElem hj)).1⟩

/-- Every resolved value has a lowered definition of its type. -/
def Typed (c : WfIRContext OpCode) (f : ResolvedFunction) (values : ValueMap) : Prop :=
  ∀ id ty, f.valueType id = some ty → ∃ v, values id = some v ∧ typeOf c.raw v = lowerType ty

theorem functionValues_facts {c : WfIRContext OpCode} {body : List (ResolvedBlock × BlockPtr)}
    (hb : entry.InBounds c.raw)
    (he : entry.getArgumentTypes! c.raw = f.header.params.toArray.map (lowerType ·.ty))
    (hf : body.map Prod.fst = f.blocks.toList)
    (hd : ResolvesList (fun (b, block) ops =>
      (blockDefinitions block 0 b.insts ops).map (typeOf c.raw) = b.insts.map (lowerType ∘ instructionType) ∧
        ∀ v ∈ blockDefinitions block 0 b.insts ops, v.InBounds c.raw) body groups) :
    (∀ id v, functionValues f entry body groups id = some v → v.InBounds c.raw) ∧
      Typed c f (functionValues f entry body groups) := by
  refine ⟨?_, fun id ty hty => Option.map_eq_some_iff.mp ?_⟩
  · rintro (i | i) v h
    · rw [functionValues_param he] at h
      exact BlockPtr.getArguments!_inBounds c.wellFormed.inBounds hb (Array.mem_of_getElem? h)
    · obtain ⟨_, _, _, hz, hv⟩ := by simpa using Array.mem_of_getElem? h
      exact ((resolvesList_zip hd).1 _ hz).2 v hv
  · cases id
    · rw [functionValues_param_type he, hty]; rfl
    · rw [functionValues_inst_type hf (resolvesList_transfer hd fun _ _ _ h => h.1), hty]; rfl

/-- The function's blocks exist with the signatures the lowering gives them. -/
structure Created (c : WfIRContext OpCode) (f : ResolvedFunction) (entry : BlockPtr)
    (blocks : Array BlockPtr) : Prop where
  size : blocks.size = f.blocks.size
  first : blocks[0]? = some entry
  bounds : ∀ b ∈ blocks, b.InBounds c.raw
  entryArgs : entry.getArgumentTypes! c.raw = f.header.params.toArray.map (lowerType ·.ty)
  args : ∀ k b block, k ≠ 0 → f.blocks[k]? = some b → blocks[k]? = some block →
    block.getArgumentTypes! c.raw = (b.insts.filterMap fun i => i.phiType.map lowerType).toArray

theorem Created.frame (h : Created ctx f entry blocks) (hf : LoweringFrame ctx ctx' ws ins ex) :
    Created ctx' f entry blocks := by
  have hb b (hm : b ∈ blocks) := h.bounds b hm
  have he := hb _ (Array.mem_of_getElem? h.first)
  refine ⟨h.size, h.first, fun b hm => hf.bounds (.block b) (hb b hm), (hf.arguments _ he).trans h.entryArgs,
    fun k b block hk hs hd => (hf.arguments _ (hb _ (Array.mem_of_getElem? hd))).trans (h.args k b block hk hs hd)⟩

theorem selectPhiInputs_mem (h : selectPhiInputs src insts = some inputs) (hm : (ty, v) ∈ inputs) :
    ∃ incoming, .phi ty incoming ∈ insts ∧ (src, v) ∈ incoming := by
  induction insts generalizing inputs with
  | nil => cases h; simp at hm
  | cons inst rest ih =>
    cases inst with
    | bin => obtain ⟨incoming, hi, he⟩ := ih h hm; exact ⟨incoming, List.mem_cons_of_mem _ hi, he⟩
    | phi ty' incoming =>
      obtain ⟨w, hw, tail, ht, rfl⟩ := by simpa [selectPhiInputs, Option.bind_eq_some_iff] using h
      rcases List.mem_cons.mp hm with he | hm
      · cases he; obtain ⟨_, _, rfl, _⟩ := List.lookup_eq_some_iff.mp hw
        exact ⟨_, List.mem_cons_self, by simp⟩
      · obtain ⟨incoming, hi, he⟩ := ih ht hm; exact ⟨incoming, List.mem_cons_of_mem _ hi, he⟩

theorem edgeReady {blocks : Array BlockPtr} (hc : Created c f entry blocks) (hT : Typed c f V)
    (hP : PhiTyped f) (hck : checkBlocks f = .ok ()) (hs : f.blocks[src]? = some b)
    (hd : dst ∈ b.terminator.successors) : EdgeReady c f blocks V src dst := by
  obtain ⟨_, hdst, hphi⟩ := checkBlocks_accepts_iff.mp hck
  have hlt := (hdst b (mem_of_get hs) dst hd).2
  obtain ⟨inputs, hi⟩ := selectPhiInputs_exists (src := src) (insts := f.blocks[dst].insts) fun ty incoming hm =>
    HasPredEdges.phiInput ((hphi _ dst (List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hlt]))).2 ty incoming hm).2 hs hd
  refine ⟨⟨_, blocks[dst]'(hc.size ▸ hlt), inputs, Array.getElem?_eq_getElem hlt, Array.getElem?_eq_getElem _,
    hc.bounds _ (Array.getElem_mem _), hi, fun ty id hm => ?_⟩⟩
  obtain ⟨incoming, hpm, him⟩ := selectPhiInputs_mem hi hm
  exact hT id ty (hP dst _ ty incoming src id (Array.getElem?_eq_getElem hlt) hpm him)

theorem termReady {blocks : Array BlockPtr} (hc : Created c f entry blocks) (hT : Typed c f V)
    (hP : PhiTyped f) (hC : CondTyped f) (hv : ValidResolvedFunction f) (hck : checkBlocks f = .ok ())
    (hs : f.blocks[src]? = some b) : TermReady c f blocks V src b.terminator := by
  have hval := (hv _ (mem_of_get hs)).2
  have hdst := (checkBlocks_accepts_iff.mp hck).2.1 b (mem_of_get hs)
  have he := fun dst hd => edgeReady (V := V) hc hT hP hck hs (dst := dst) hd
  rcases ht : b.terminator with v | dst | ⟨cnd, y, n⟩ <;> rw [ht] at hval hdst he
  · rintro id rfl
    obtain ⟨ty, h⟩ := valid_ref hval; obtain ⟨_, h', _⟩ := hT _ _ h; simp [h']
  · exact ⟨(hdst dst (by simp [ResolvedTerminator.successors])).1, he dst (by simp [ResolvedTerminator.successors])⟩
  · exact ⟨(hdst y (by simp [ResolvedTerminator.successors])).1, (hdst n (by simp [ResolvedTerminator.successors])).1,
      he y (by simp [ResolvedTerminator.successors]), he n (by simp [ResolvedTerminator.successors]),
      fun id hid => hT id _ (hC src b id y n hs (hid ▸ ht))⟩

theorem operandsDefined {k : Nat} {b : ResolvedBlock} (hv : ValidResolvedFunction f) (hT : Typed c f V) (hs : f.blocks[k]? = some b)
    (hi : i ∈ b.insts.filterMap ResolvedInst.binary) : OperandsDefined V i := by
  obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp hi
  cases x with
  | phi => cases he
  | bin =>
    cases he; rcases i with ⟨_, _, l, r⟩
    have hval := (hv _ (mem_of_get hs)).1 _ hx
    rintro id (rfl | rfl)
    all_goals first
      | (obtain ⟨ty, h⟩ := valid_ref hval.1; obtain ⟨_, h', _⟩ := hT _ _ h; simp [h'])
      | (obtain ⟨ty, h⟩ := valid_ref hval.2; obtain ⟨_, h', _⟩ := hT _ _ h; simp [h'])

theorem resolvesList_of_map {g : α → γ} (h : ResolvesList R (xs.map g) ys) :
    ResolvesList (fun x y => R (g x) y) xs ys := by
  induction xs generalizing ys with
  | nil => cases h; exact .nil
  | cons x xs ih => cases h with | cons hr ht => exact .cons hr (ih ht)

theorem resolvesList_transfer_mem (h : ResolvesList R xs ys)
    (ht : ∀ x y, x ∈ xs → R x y → S x y) : ResolvesList S xs ys := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (ht _ _ List.mem_cons_self hr) (ih fun x y hm => ht x y (List.mem_cons_of_mem _ hm))

theorem resolvesList_zipIdx {xs : List α} (h : ResolvesList (fun x y => R x.1 y) (xs.zipIdx k) ys) :
    ResolvesList R xs ys := by
  induction xs generalizing k ys with
  | nil => cases h; exact .nil
  | cons x xs ih => cases h with | cons hr ht => exact .cons hr (ih ht)

/-- The block plans built by `lowerFunction`. -/
def plansOf (f : ResolvedFunction) (blocks : Array BlockPtr) : List Plan :=
  (f.blocks.toList.zip blocks.toList).zipIdx.map fun ((b, block), id) =>
    ⟨block, b.insts.filterMap ResolvedInst.binary, (id, b.terminator)⟩

theorem zipIdx_get {blocks : Array BlockPtr} {k : Nat} {b : ResolvedBlock} (h : ((b, block), k) ∈ (f.blocks.toList.zip blocks.toList).zipIdx) :
    f.blocks[k]? = some b ∧ blocks[k]? = some block := by
  simpa using List.getElem?_zip_eq_some.mp (List.mk_mem_zipIdx_iff_getElem?.mp h)

theorem blockArgs_ready {blocks : Array BlockPtr} {k : Nat} {b : ResolvedBlock} (hc : Created c f entry blocks) (hck : checkBlocks f = .ok ())
    (hs : f.blocks[k]? = some b) (hd : blocks[k]? = some block)
    (hj : (b.insts.filterMap ResolvedInst.phiType)[j]? = some ty) :
    (ValuePtr.blockArgument ⟨block, j⟩).InBounds c.raw ∧ typeOf c.raw (.blockArgument ⟨block, j⟩) = lowerType ty := by
  by_cases hk : k = 0
  · subst hk
    obtain ⟨⟨e, he, hn⟩, _⟩ := checkBlocks_accepts_iff.mp hck
    cases hs.symm.trans he
    simp [List.filterMap_eq_nil_iff.mpr hn] at hj
  · exact blockArg_facts (hc.bounds _ (Array.mem_of_getElem? hd))
      (by rw [hc.args k b block hk hs hd, ← List.map_filterMap]) hj

theorem allocatedValues {blocks : Array BlockPtr} (hc : Created c f entry blocks)
    (hck : checkBlocks f = .ok ())
    (hr : ResolvesList (fun p ops => ResolvesList (BinaryAllocated c) p.insts ops) (plansOf f blocks) groups) :
    (∀ id v, functionValues f entry (f.blocks.toList.zip blocks.toList) groups id = some v → v.InBounds c.raw) ∧
      Typed c f (functionValues f entry (f.blocks.toList.zip blocks.toList) groups) := by
  have hbody : ResolvesList (fun (b, block) ops =>
      (blockDefinitions block 0 b.insts ops).map (typeOf c.raw) = b.insts.map (lowerType ∘ instructionType) ∧
        ∀ v ∈ blockDefinitions block 0 b.insts ops, v.InBounds c.raw) (f.blocks.toList.zip blocks.toList) groups :=
    resolvesList_zipIdx (resolvesList_transfer_mem (resolvesList_of_map hr)
    fun ⟨⟨b, block⟩, k⟩ _ hm ha => have ⟨hs, hd⟩ := zipIdx_get hm; defs_facts ha fun _ _ hj => blockArgs_ready hc hck hs hd hj)
  exact functionValues_facts (hc.bounds _ (Array.mem_of_getElem? hc.first)) hc.entryArgs
    (List.map_fst_zip (by simp [hc.size])) hbody

theorem hready_of {blocks : Array BlockPtr} (hc : Created c f entry blocks) (hv : ValidResolvedFunction f)
    (hck : checkBlocks f = .ok ()) (hP : PhiTyped f) (hC : CondTyped f)
    (hr : ResolvesList (fun p ops => ResolvesList (BinaryAllocated c) p.insts ops) (plansOf f blocks) groups) :
    (∀ id v, functionValues f entry (f.blocks.toList.zip blocks.toList) groups id = some v → v.InBounds c.raw) ∧
      ∀ p ∈ plansOf f blocks, p.block.InBounds c.raw ∧
        (∀ i ∈ p.insts, OperandsDefined (functionValues f entry (f.blocks.toList.zip blocks.toList) groups) i) ∧
        TermReady c f blocks (functionValues f entry (f.blocks.toList.zip blocks.toList) groups)
          p.terminator.1 p.terminator.2 := by
  obtain ⟨hB, hT⟩ := allocatedValues hc hck hr
  refine ⟨hB, fun p hp => ?_⟩
  obtain ⟨⟨⟨b, block⟩, k⟩, hm, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hs, hd⟩ := zipIdx_get hm
  exact ⟨hc.bounds _ (Array.mem_of_getElem? hd), fun i hi => operandsDefined hv hT hs hi,
    termReady hc hT hP hC hv hck hs⟩

theorem grows_lookupValue {id : ValueId} : Grows (lookupValue values id) := fun _ _ _ h => by
  cases (lookupValue_ok.mp h).2; exact Grew.refl

theorem grows_lowerOperand (hl : ∀ id, Grows (lookup id)) : Grows (lowerOperand lookup block ty v) := by
  cases v with
  | ref id => exact hl id
  | intConst => cases ty; exact Grows.emit.bind fun _ => Grows.pure

theorem grows_wireBinary (hl : ∀ id, Grows (lookup id)) : Grows (wireBinary lookup block x) := by
  rcases x with ⟨⟨_, _, _, _⟩, _⟩
  exact (grows_lowerOperand hl).bind fun _ => Grows.pushValue.bind fun _ =>
    (grows_lowerOperand hl).bind fun _ => Grows.pushValue.bind fun _ => Grows.attachInst

theorem grows_lowerTypedOperand (hl : ∀ id, Grows (lookup id)) :
    Grows (lowerTypedOperand lookup block err ty v) := fun _ _ _ h =>
  grows_lowerOperand hl _ _ _ (lowerTypedOperand_ok.mp h).1

theorem grows_lowerEdge (hl : ∀ id, Grows (lookup id)) : Grows (lowerEdge f blocks lookup block src dst) := by
  rw [lowerEdge_eq]
  repeat' split
  all_goals first | exact Grows.throw | exact (Grows.mapM fun _ => grows_lowerTypedOperand hl).bind fun _ => Grows.pure

theorem grows_lowerTerminator (hl : ∀ id, Grows (lookup id)) :
    Grows (lowerTerminator f blocks lookup block src t) := by
  cases t with
  | ret => exact ((grows_lowerOperand hl).bind fun _ => Grows.emit).bind fun _ => Grows.pure
  | br => exact (grows_lowerEdge hl).bind fun _ => Grows.emitBranch
  | condBr =>
    rw [lowerTerminator_condBr_eq]
    exact (grows_lowerTypedOperand hl).bind fun _ => (grows_lowerEdge hl).bind fun _ =>
      (grows_lowerEdge hl).bind fun _ => Grows.emitBranch

theorem grows_lowerInst : Grows (lowerInst block inst) := by
  rcases inst with ⟨_ | _ | _, _, _, _⟩ <;> exact Grows.emit

theorem grows_lowerBlocks (hl : ∀ groups id, Grows (lookup groups id))
    (ht : ∀ values p, (∀ id, Grows (values id)) → Grows (terminate values p)) :
    Grows (lowerBlocks plans lookup terminate) :=
  (Grows.mapM fun _ => Grows.mapM fun _ => grows_lowerInst).bind fun _ =>
    (Grows.forIn fun (_, _) _ => (Grows.forM fun _ => grows_wireBinary (hl _)).bind fun _ =>
      (ht _ _ (hl _)).bind fun _ => Grows.pure).bind fun _ => Grows.pure

theorem createBlocks_ok
    (h : (xs.mapM (createBlock region ∘ ts)).run ctx = .ok (blocks, ctx')) :
    Grew ctx ctx' ∧ ResolvesList (fun x b => b.InBounds ctx'.raw ∧ b.getArgumentTypes! ctx'.raw = ts x)
      xs blocks := by
  induction xs generalizing ctx blocks with
  | nil => cases h; exact ⟨Grew.refl, .nil⟩
  | cons x xs ih =>
    simp only [List.mapM_cons, lowerM_bind_ok, lowerM_pure_ok, Prod.mk.injEq] at h
    obtain ⟨b, c, hb, bs, d, hs, rfl, rfl⟩ := h
    obtain ⟨hg, hi, ht⟩ := createBlock_ok hb
    obtain ⟨hf, hl⟩ := ih hs
    exact ⟨hg.trans hf, .cons ⟨hf.bounds (.block b) hi, (hf.arguments b hi).trans ht⟩ hl⟩

theorem resolvesList_lookup (h : ResolvesList R xs ys) :
    xs.length = ys.length ∧ ∀ (i : Nat) x y, xs[i]? = some x → ys[i]? = some y → R x y := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    refine ⟨by simp [ih.1], ?_⟩
    intro i x y hx hy
    cases i with
    | zero => simp at hx hy; cases hx; cases hy; exact hr
    | succ i => exact ih.2 i x y (by simpa using hx) (by simpa using hy)

theorem created_of_tail {tail : List BlockPtr}
    (he : f.blocks[0]? = some entrySrc)
    (hb : entry.InBounds ctx.raw)
    (ht : entry.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty))
    (hl : ResolvesList (fun (b : ResolvedBlock) p => p.InBounds ctx.raw ∧
      p.getArgumentTypes! ctx.raw = (b.insts.filterMap (fun i => i.phiType.map lowerType)).toArray)
      (f.blocks.toList.drop 1) tail) : Created ctx f entry (entry :: tail).toArray := by
  have h0 : 0 < f.blocks.size := (Array.getElem?_eq_some_iff.mp he).1
  have hlen := (resolvesList_lookup hl).1
  refine ⟨by simp at hlen ⊢; omega, rfl, ?_, ht, ?_⟩
  · intro b hm
    simp only [List.mem_toArray, List.mem_cons] at hm
    exact hm.elim (fun h => h ▸ hb) (fun h => (resolvesList_right_member hl h).choose_spec.1)
  · intro k b p hk hs hd
    rcases k with _ | k
    · contradiction
    exact (resolvesList_lookup hl).2 k b p (by simpa [List.getElem?_drop, Nat.add_comm] using hs)
      (by simpa using hd) |>.2

theorem lowerFunction_total_of_checks (hs : AllocationSafe ctx.raw) (hb : parent.InBounds ctx.raw)
    (hv : ValidResolvedFunction f) (hc : checkBlocks f = .ok ()) (hP : PhiTyped f) (hC : CondTyped f) :
    ∃ op ctx', (lowerFunction parent f).run ctx = .ok (op, ctx') ∧ AllocationSafe ctx'.raw ∧
      parent.InBounds ctx'.raw := by
  obtain ⟨⟨entrySrc, he, _⟩, _⟩ := checkBlocks_accepts_iff.mp hc
  obtain ⟨⟨r, entry⟩, c, hbody, hs⟩ := createBody_total (ts := f.header.params.toArray.map (lowerType ·.ty)) hs
  obtain ⟨hmono, hr, hdetached, hent, htypes⟩ := createBody_ok hbody
  let ts (b : ResolvedBlock) := (b.insts.filterMap (fun i => i.phiType.map lowerType)).toArray
  obtain ⟨tail, d, htail, hs, _⟩ := mapM_total (xs := f.blocks.toList.drop 1)
    (g := createBlock r ∘ ts) (fun c => AllocationSafe c.raw ∧ r.InBounds c.raw)
    (fun b c ⟨hs, hr⟩ => by
      obtain ⟨p, d, h, hs⟩ := createBlock_total (ts := ts b) hs hr
      exact ⟨p, d, h, hs, (createBlock_ok h).1.bounds (.region r) hr⟩) ⟨hs, hr⟩
  obtain ⟨hg, hl⟩ := createBlocks_ok htail
  have hcreated := created_of_tail he (hg.bounds (.block entry) hent) ((hg.arguments entry hent).trans htypes) hl
  let blocks := (entry :: tail).toArray
  let V := functionValues f entry (f.blocks.toList.zip blocks.toList)
  obtain ⟨e, hw, hs⟩ := lowerBlocks_total (V := V) (plans := plansOf f blocks) hs
    (fun _ _ hf ha => hready_of (hcreated.frame hf) hv hc hP hC ha)
  have hg' := grows_lowerBlocks (lookup := fun groups => lookupValue (V groups))
    (fun _ _ => grows_lookupValue) (fun _ _ hl => grows_lowerTerminator hl) _ _ _ hw
  have hparent := hg'.bounds (.block parent) (hg.bounds (.block parent) (hmono (.block parent) hb))
  have hregion := hg'.bounds (.region r) (hg.bounds (.region r) hr)
  have howner := (hg'.regions r).trans ((hg.regions r).trans hdetached)
  obtain ⟨g, op, hgop, hs⟩ := emit_total (code := Llvm.func) (insert := true) (ctx := e)
    (block := parent) (tys := #[]) (vs := #[]) (rs := #[r])
    (props := { sym_name := ⟨f.header.name.toUTF8⟩
                function_type := { inputs := (f.header.params.toArray.map (lowerType ·.ty)).map Subtype.val,
                                   outputs := #[(lowerType f.header.retType).val] }
                extra := defaultFuncExtra })
    hs (fun _ => hparent) (by simp) (by simpa) (by simpa) (by simp)
  refine ⟨op, g, ?_, hs, (emit_spec hgop).1.bounds (.block parent) hparent⟩
  simp only [lowerFunction, lowerM_bind_ok]
  exact ⟨(), ctx, by simp [StateT.run, StateT.lift, hc, Functor.map, Except.map],
    (r, entry), c, hbody, tail, d, htail, (), e, hw, hgop⟩

theorem lowerFunction_total (hs : AllocationSafe ctx.raw) (hb : parent.InBounds ctx.raw)
    (h : LowersFunction specCtx f specOp) :
    ∃ op ctx', (lowerFunction parent f).run ctx = .ok (op, ctx') ∧ AllocationSafe ctx'.raw ∧
      parent.InBounds ctx'.raw :=
  lowerFunction_total_of_checks hs hb h.1 h.checkBlocks (LowersFunction.typed h).1 (LowersFunction.typed h).2

theorem lowerFunctions_total_of_checks {parent : BlockPtr} {fs : List ResolvedFunction} (hs : AllocationSafe ctx.raw) (hb : parent.InBounds ctx.raw)
    (h : ∀ f ∈ fs, ValidResolvedFunction f ∧ checkBlocks f = .ok () ∧ PhiTyped f ∧ CondTyped f) :
    ∃ ctx', (fs.forM fun f => do let _ ← lowerFunction parent f).run ctx = .ok ((), ctx') := by
  induction fs generalizing ctx with
  | nil => exact ⟨ctx, rfl⟩
  | cons f fs ih =>
    obtain ⟨hv, hc, hp, ht⟩ := h f (by simp)
    obtain ⟨op, c, he, hs, hb⟩ := lowerFunction_total_of_checks hs hb hv hc hp ht
    obtain ⟨d, hd⟩ := ih hs hb (fun g hg => h g (List.mem_cons_of_mem f hg))
    exact ⟨d, by
      rw [List.forM_eq_forM, List.forM_cons]
      exact lowerM_bind_ok.mpr ⟨(), c, lowerM_bind_ok.mpr ⟨op, c, he, rfl⟩, hd⟩⟩

theorem lowerFunctions_total (hs : AllocationSafe ctx.raw) (hb : parent.InBounds ctx.raw)
    (h : ResolvesList (LowersFunction specCtx) fs ops) :
    ∃ ctx', (fs.forM fun f => do let _ ← lowerFunction parent f).run ctx = .ok ((), ctx') :=
  lowerFunctions_total_of_checks hs hb fun _ hf =>
    let ⟨_, h⟩ := resolvesList_mem_left h hf
    ⟨h.1, h.checkBlocks, LowersFunction.typed h⟩

end Complete

theorem lowerModule_total_of_checks
    (h : ∀ f ∈ m.funcs, ValidResolvedFunction f ∧ checkBlocks f = .ok () ∧ Complete.PhiTyped f ∧ Complete.CondTyped f) :
    ∃ ctx₂ root₂, lowerModule m = .ok (ctx₂, root₂) := by
  obtain ⟨c, r, hc, hs⟩ := createModule_total
  obtain ⟨_, _, hm, _, _, _, _⟩ := createRawModule_sound hc
  let d := WfRewriter.setAttributes c r defaultModuleAttrs hm.1
  have hd : createModule = some (d, r) := by simp [createModule, hc, hm.1, d]
  obtain ⟨reg, b, hmod, hblocks, hchain, _, _⟩ := createModule_sound hd
  have hget : (r.getRegion! d.raw 0).getFirstBlock! d.raw = some b := by
    rw [← OperationPtr.getRegions!.getElem!_eq_getRegion!, hmod.regions_eq]
    simpa using hblocks.first
  have hsafe : AllocationSafe d.raw := by
    have hn : d.raw.nextID = c.raw.nextID := rfl
    constructor <;> intro p hp <;> rw [hn]
    · exact hs.operations p ((setAttributes_inBounds (.operation p)).mp hp)
    · exact hs.blocks p ((setAttributes_inBounds (.block p)).mp hp)
    · exact hs.regions p ((setAttributes_inBounds (.region p)).mp hp)
  obtain ⟨e, he⟩ := Complete.lowerFunctions_total_of_checks hsafe hchain.blockInBounds h
  refine ⟨e, r, ?_⟩
  simp only [lowerModule, hd, hget]
  rw [he]
  rfl

theorem lowerModule_total (h : LowersModule ctx m root) :
    ∃ ctx₂ root₂, lowerModule m = .ok (ctx₂, root₂) := by
  obtain ⟨_, _, _, _, _, _, _, hfs⟩ := h
  exact lowerModule_total_of_checks fun f hf =>
    let ⟨_, h⟩ := resolvesList_mem_left hfs hf
    ⟨h.1, h.checkBlocks, Complete.LowersFunction.typed h⟩

theorem WellFormedResolvedFunction.block {f : ResolvedFunction} (h : WellFormedResolvedFunction f)
    (hb : f.blocks[i]? = some b) :
    (i = 0 → ∀ inst ∈ b.insts, inst.phiType = none) ∧
    b.insts.Pairwise (fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none) ∧
    (∀ inst ∈ b.insts, WellFormedResolvedInst f i inst) ∧
    WellFormedResolvedTerminator f b.terminator :=
  h.2.2 b i (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hb))

theorem WellFormedResolvedFunction.checks {f : ResolvedFunction} (h : WellFormedResolvedFunction f) :
    checkBlocks f = .ok () ∧ Complete.PhiTyped f ∧ Complete.CondTyped f := by
  refine ⟨?_, ?_, ?_⟩
  · apply checkBlocks_accepts_iff.mpr
    have he : f.blocks[0]? = some (getElem f.blocks 0 h.2.1) := by simp [h.2.1]
    refine ⟨⟨_, he, (WellFormedResolvedFunction.block h he).1 rfl⟩, ?_, fun b i hi => ?_⟩
    · intro b hb
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
      have hw := (WellFormedResolvedFunction.block h (by simpa using hi : f.blocks[i]? = some b)).2.2.2
      have hv := (h.1 b hb).2
      cases ht : b.terminator <;> simp_all [ValidResolvedTerminator, WellFormedResolvedTerminator,
        ResolvedTerminator.successors]
    · obtain ⟨_, ho, ht, _⟩ := h.2.2 b i hi
      exact ⟨ho, fun ty incoming hm => ⟨(ht _ hm).2.1, (ht _ hm).1⟩⟩
  · exact fun dst b ty incoming src id hb hi hm => (WellFormedResolvedFunction.block h hb).2.2.1 _ hi |>.2.2 _ hm
  · intro src b id yes no hb ht
    have hw := (WellFormedResolvedFunction.block h hb).2.2.2
    exact (ht ▸ hw).1

theorem lowerModule_total_of_valid (h : ValidResolvedModule m) :
    ∃ ctx root, lowerModule m = .ok (ctx, root) :=
  lowerModule_total_of_checks fun f hf => ⟨(h f hf).1, WellFormedResolvedFunction.checks (h f hf)⟩

end Veir.LLVMLowering
