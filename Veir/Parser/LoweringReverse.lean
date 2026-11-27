import Veir.Parser.LoweringSound
import Veir.Parser.LoweringUnique

/-! Reversing a lowering recovers the resolved module up to `ResolvedModule.Equiv`. -/

namespace Veir.LLVMLowering

open LLVMParserProp NameResolutionSketch Unique

namespace Reverse

theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, String.fromUTF8, s.isValidUTF8]

theorem reverseIntType_lowerType (ty : LLType) : reverseIntType (lowerType ty).val = .ok ty := by
  cases ty; rfl

theorem getElem?_ofList {l : List (α × β)} [BEq α] [LawfulBEq α] [Hashable α]
    (hn : (l.map Prod.fst).Nodup) (hm : (k, v) ∈ l) : (Std.HashMap.ofList l)[k]? = some v :=
  Std.HashMap.getElem?_ofList_of_mem (k := k) (by simp)
    (by simpa [List.Nodup, List.pairwise_map] using hn) hm

theorem getElem?_ofList_none {l : List (α × β)} [BEq α] [LawfulBEq α] [Hashable α]
    (hn : ∀ p ∈ l, p.1 ≠ k) : (Std.HashMap.ofList l)[k]? = none :=
  Std.HashMap.getElem?_ofList_of_contains_eq_false (by simpa using fun b h => hn _ h rfl)

theorem normalize_ofInt (w : Nat) (n : Int) :
    (ResolvedValue.intConst (IntegerAttr.ofInt n (.signless w)).value).normalize (.int w) =
      (ResolvedValue.intConst n).normalize (.int w) := by
  simp only [IntegerAttr.ofInt, IntegerAttr.normalizeValue, ResolvedValue.normalize]
  split <;> simp only [IntegerType.signless, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.ofInt_toInt]


theorem ok_bind {ε α β : Type _} (a : α) (g : α → Except ε β) : (Except.ok a >>= g) = g a := rfl

theorem map_ok {ε α β : Type _} (g : α → β) (a : α) : (g <$> Except.ok a : Except ε β) = .ok (g a) := rfl

theorem pure_eq_ok {ε α : Type _} (a : α) : (pure a : Except ε α) = .ok a := rfl

attribute [local simp] ok_bind map_ok pure_eq_ok

theorem mapM_ok {g : α → Except ε β} {P : α → β → Prop} :
    ∀ {xs : List α}, (∀ x ∈ xs, ∃ y, g x = .ok y ∧ P x y) → ∃ ys, xs.mapM g = .ok ys ∧ ResolvesList P xs ys
  | [], _ => ⟨[], rfl, .nil⟩
  | x :: xs, h => by
    obtain ⟨y, hy, hp⟩ := h x (by simp)
    obtain ⟨ys, hys, hr⟩ := mapM_ok (xs := xs) fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨y :: ys, by rw [List.mapM_cons, hy, ok_bind, hys, ok_bind]; rfl, .cons hp hr⟩

theorem mapM_ok' {g : α → Except ε β} {xs : List α} {Q : List β → Prop} (P : α → β → Prop) (h : ∀ x ∈ xs, ∃ y, g x = .ok y ∧ P x y)
    (hq : ∀ ys, ResolvesList P xs ys → Q ys) : ∃ ys, xs.mapM g = .ok ys ∧ Q ys :=
  let ⟨ys, hok, hr⟩ := mapM_ok h; ⟨ys, hok, hq ys hr⟩

/-! ## Operands -/

/-- `ids` names each valid reference by the pointer it lowers to, and no constant result. -/
def IdsAgree (raw : IRContext OpCode) (f : ResolvedFunction) (values : ValueMap)
    (ids : Std.HashMap ValuePtr ValueId) : Prop :=
  (∀ id v, ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length (.ref id) →
    values id = some v → ids[v]? = some id) ∧
  ∀ c : OperationPtr, c.getOpType! raw = .llvm .mlir__constant → ids[ValuePtr.opResult (c.getResult 0)]? = none

/-- A decoded value agrees with the source value once literals are normalized. -/
def Decodes (ty : LLType) (r' r : ResolvedValue) : Prop := r'.normalize ty = r.normalize ty

theorem reverseOperand_tile {ctx : WfIRContext OpCode} (hI : IdsAgree ctx.raw f values ids)
    (h : OperandTile ctx values ty r v cs)
    (hv : ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length r) :
    ∃ r', reverseOperand ctx.raw ids v = .ok r' ∧ Decodes ty r' r := by
  cases r with
  | ref id => exact ⟨_, by simp [reverseOperand, hI.1 id v hv h.1], rfl⟩
  | intConst n =>
    obtain ⟨w⟩ := ty
    obtain ⟨c, rfl, rfl, hm⟩ := h
    have ht : c.getOpType! ctx.raw = .llvm .mlir__constant := congrArg Prod.fst hm.2.2
    have hn := hI.2 c ht
    simp only [OperationPtr.getResult] at hn
    exact ⟨_, by simp [reverseOperand, hn, ht, hm.2.1, OperationPtr.getResult], normalize_ofInt w n⟩


/-! ## Instructions -/

theorem OperandTile.const {ctx : WfIRContext OpCode} (h : OperandTile ctx values ty r v cs) :
    ∀ c ∈ cs, c.getOpType! ctx.raw = .llvm .mlir__constant := by
  cases r with
  | ref => simp [h.2]
  | intConst =>
    obtain ⟨w⟩ := ty; obtain ⟨c, rfl, -, hm⟩ := h
    have ht : c.getOpType! ctx.raw = .llvm .mlir__constant := congrArg Prod.fst hm.2.2
    simpa using ht

theorem reverseInst_const (h : c.getOpType! raw = .llvm .mlir__constant) :
    reverseInst raw val c = .ok none := by
  simp [reverseInst, h, reverseBinOp]

theorem filterMapM_ok {g : α → Except ε (Option β)} : ∀ {xs : List α}, (∀ x ∈ xs, ∃ y, g x = .ok y) →
    xs.filterMapM g = .ok (xs.filterMap fun x => (g x).toOption.join)
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (by simp)
    have := filterMapM_ok (xs := xs) fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases y <;> simp [hy, this, Except.toOption]

theorem reverseInst_bin {ctx : WfIRContext OpCode}
    (hm : MatchesOp ctx op (binOpcode opc) #[lowerType ty] #[vl, vr] #[] default)
    (hl : val vl = .ok l) (hr : val vr = .ok r) :
    reverseInst ctx.raw val op = .ok (some (.bin (.bin opc ty l r))) := by
  have ht : op.getOpType! ctx.raw = .llvm (binOpcode opc) := congrArg Prod.fst hm.2.2
  have hts : op.getResultTypes! ctx.raw = #[lowerType ty] := congrArg (·.2.1) hm.2.2
  have hos : op.getOperands! ctx.raw = #[vl, vr] := congrArg (·.2.2.1) hm.2.2
  cases opc
  all_goals simp only [reverseInst, ht, binOpcode, reverseBinOp, reverseBinary, hts, hos]
  case or =>
    have hp : op.getProperties! ctx.raw Llvm.or = default := hm.2.1
    have hd : (default : propertiesOf Llvm.or).disjoint = false := rfl
    simp [hp, hd, reverseIntType_lowerType, hl, hr]
  all_goals simp [reverseIntType_lowerType, hl, hr]

/-- Two instructions agree once their literals are normalized. -/
def NormEq (a b : ResolvedInst) : Prop := a.normalizeLiterals = b.normalizeLiterals

abbrev NumInsts (f : ResolvedFunction) : Nat := (f.blocks.toList.flatMap (·.insts)).length

theorem reverseInst_tile {ctx : WfIRContext OpCode} (hI : IdsAgree ctx.raw f values ids)
    (h : LowersResolvedInstTile ctx values (inst, k) tile)
    (hv : ValidResolvedInst f.header.params.length (NumInsts f) nb inst) :
    (∀ x ∈ tile, ∃ y, reverseInst ctx.raw (reverseOperand ctx.raw ids) x = .ok y) ∧
      ResolvesList NormEq (tile.filterMap fun x => (reverseInst ctx.raw (reverseOperand ctx.raw ids) x).toOption.join)
        ([inst].filter (·.phiType.isNone)) := by
  cases inst with
  | phi => cases (h : tile = []); simp [ResolvedInst.phiType, ResolvesList.nil]
  | bin b =>
    obtain ⟨opc, ty, l, r⟩ := b
    obtain ⟨vl, vr, cl, cr, op, rfl, htl, htr, -, hm⟩ := h
    obtain ⟨l', hl, hdl⟩ := reverseOperand_tile hI htl hv.1
    obtain ⟨r', hr, hdr⟩ := reverseOperand_tile hI htr hv.2
    have hc : ∀ c ∈ cl ++ cr, reverseInst ctx.raw (reverseOperand ctx.raw ids) c = .ok none := fun c hc =>
      reverseInst_const ((List.mem_append.mp hc).elim (OperandTile.const htl c) (OperandTile.const htr c))
    have hb := reverseInst_bin hm hl hr
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨_, hc x hx⟩
      · simp at hx; exact ⟨_, hx ▸ hb⟩
    · rw [List.filterMap_append, List.filterMap_eq_nil_iff.mpr (fun c hc' => by simp [hc c hc', Except.toOption])]
      simp [hb, Except.toOption, ResolvedInst.phiType]
      exact .cons (by simp only [Decodes] at hdl hdr; simp [NormEq, ResolvedInst.normalizeLiterals, hdl, hdr]) .nil

/-! ## Terminators -/

/-- The phis of a block, in order. -/
def phis (b : ResolvedBlock) : List ResolvedInst := b.insts.filter fun i => decide (i.phiType ≠ none)

/-- A decoded phi input from `src` is one of the phi's incoming values from `src`. -/
def PhiArg (src : BlockId) : ResolvedInst → ResolvedValue → Prop
  | .phi ty incoming, v => ∃ input, (src, input) ∈ incoming ∧ Decodes ty v input
  | .bin _, _ => False

/-- A decoded edge from `src` targets a block of `f` and passes one input per phi. -/
def EdgeArgs (f : ResolvedFunction) (src : BlockId) (e : ReverseEdge) : Prop :=
  ∃ target, f.blocks[e.1]? = some target ∧ ResolvesList (PhiArg src) (phis target) e.2.toList

/-- The facts about the decoding context shared by all blocks of a function. -/
structure DecodeCtx (ctx : WfIRContext OpCode) (f : ResolvedFunction) (body : Array BlockPtr)
    (values : ValueMap) (ids : Std.HashMap ValuePtr ValueId) (blockIds : Std.HashMap BlockPtr BlockId) : Prop where
  valid : ValidResolvedFunction f
  ids : IdsAgree ctx.raw f values ids
  blockIds : ∀ (j : Nat) b, body[j]? = some b → blockIds[b]? = some j
  args : ∀ (j : Nat) b target, j ≠ 0 → body[j]? = some b → f.blocks[j]? = some target →
    (b.getArguments! ctx.raw).size = (phis target).length

theorem edgeValues {ctx : WfIRContext OpCode} (hI : IdsAgree ctx.raw f values ids)
    (hr : ResolvesList (fun phi arg => PhiPassesArg ctx values src phi arg ∧
      phi.phiType.map lowerType = some (typeOf ctx.raw arg.1)) phs args)
    (hv : ∀ ty incoming, .phi ty incoming ∈ phs → ∀ e ∈ incoming,
      ValidResolvedValue f.header.params.length (NumInsts f) e.2) :
    ∃ vals, (args.map Prod.fst).mapM (reverseOperand ctx.raw ids) = .ok vals ∧
      ResolvesList (PhiArg src) phs vals ∧ ∀ c ∈ argOps args, c.getOpType! ctx.raw = .llvm .mlir__constant := by
  induction hr with
  | nil => exact ⟨[], rfl, .nil, by simp [argOps]⟩
  | @cons phi arg _ _ hp _ ih =>
    obtain ⟨vals, hvals, hr, hc⟩ := ih fun ty incoming hm => hv ty incoming (List.mem_cons_of_mem _ hm)
    cases phi with
    | phi ty incoming =>
      obtain ⟨input, hin, ht⟩ := hp.1
      obtain ⟨r, hr', hd⟩ := reverseOperand_tile hI ht (hv ty incoming (by simp) _ hin)
      refine ⟨r :: vals, by simp [hr', hvals], .cons ⟨input, hin, hd⟩ hr, fun c hc' => ?_⟩
      simp only [argOps, List.flatMap_cons, List.mem_append] at hc'
      exact hc'.elim (OperandTile.const ht c) (hc c)
    | bin => exact hp.1.elim

theorem phi_valid {dst : Nat} (hvalid : ValidResolvedFunction f) (ht : f.blocks[dst]? = some target)
    (hm : ResolvedInst.phi ty incoming ∈ phis target) :
    ∀ e ∈ incoming, ValidResolvedValue f.header.params.length (NumInsts f) e.2 := fun e he =>
  ((hvalid target (List.mem_of_getElem? (by simpa using ht : f.blocks.toList[dst]? = some target))).1 _
    (List.mem_filter.mp hm).1 e he).2

theorem reverseEdge_ok (hD : DecodeCtx ctx f body values ids blockIds)
    (h : LowersEdge ctx f (body[·]?) values src dst b args) :
    ∃ e, reverseEdge ctx.raw blockIds (reverseOperand ctx.raw ids) b (args.map Prod.fst) = .ok e ∧
      e.1 = dst ∧ EdgeArgs f src e ∧ args.length = (b.getArguments! ctx.raw).size ∧
      ∀ c ∈ argOps args, c.getOpType! ctx.raw = .llvm .mlir__constant := by
  obtain ⟨hne, hb, target, phs, ht, hf, hr⟩ := h
  cases FilterRel.eq_filter hf
  obtain ⟨vals, hvals, hpa, hc⟩ := edgeValues hD.ids hr fun _ _ hm => phi_valid hD.valid ht hm
  have hl : args.length = (b.getArguments! ctx.raw).size := by
    rw [hD.args dst b target hne hb ht, ← resolves_length hr]; rfl
  refine ⟨(dst, vals.toArray), ?_, rfl, ⟨target, ht, by simpa [phis] using hpa⟩, hl, hc⟩
  simp [reverseEdge, hD.blockIds dst b hb, hne, hl, hvals]

theorem MatchesTermOp.eqs {code : Llvm} {props : propertiesOf code}
    (h : MatchesTermOp ctx op code args succs props) :
    op.getOpType! ctx.raw = .llvm code ∧ (op.getOperands! ctx.raw).toList = args.toList ∧
      (op.getSuccessors! ctx.raw).toList = succs.toList ∧ op.getProperties! ctx.raw code = props :=
  ⟨congrArg Prod.fst h.2.2, congrArg (·.2.2.1.toList) h.2.2, congrArg (·.2.2.2.2.1.toList) h.2.2, h.2.1⟩

/-- A decoded terminator agrees with its source and lists one edge per successor. -/
def TermDecodes (f : ResolvedFunction) (src : BlockId) (t : ResolvedTerminator) :
    ResolvedTerminator × List ReverseEdge → Prop
  | (t', edges) => t'.normalizeLiterals f.header.retType = t.normalizeLiterals f.header.retType ∧
      edges.map Prod.fst = t.successors ∧ ∀ e ∈ edges, EdgeArgs f src e

theorem reverseTerminator_tile (hD : DecodeCtx ctx f body values ids blockIds)
    (h : LowersTerminatorTile ctx f (body[·]?) values src t tile)
    (hv : ValidResolvedTerminator f.header.params.length (NumInsts f) f.blocks.size t) :
    ∃ pre term, tile = pre ++ [term] ∧ (∀ c ∈ pre, c.getOpType! ctx.raw = .llvm .mlir__constant) ∧
      ∃ d, reverseTerminator ctx.raw blockIds (reverseOperand ctx.raw ids) term = .ok d ∧
        TermDecodes f src t d := by
  cases t with
  | ret v =>
    obtain ⟨x, cs, op, ho, hm, rfl⟩ := h
    obtain ⟨hty, hops, hsucc, -⟩ := MatchesTermOp.eqs hm
    obtain ⟨r, hr, hd⟩ := reverseOperand_tile hD.ids ho hv
    refine ⟨cs, op, rfl, OperandTile.const ho, (.ret r, []), ?_, ?_⟩
    · simp [reverseTerminator, hty, hops, hsucc, hr]
    · exact ⟨by simpa [ResolvedTerminator.normalizeLiterals, Decodes] using hd, rfl, by simp⟩
  | br dst =>
    obtain ⟨b, args, op, he, hm, rfl⟩ := h
    obtain ⟨hty, hops, hsucc, -⟩ := MatchesTermOp.eqs hm
    obtain ⟨e, hok, rfl, hea, -, hc⟩ := reverseEdge_ok hD he
    refine ⟨argOps args, op, rfl, hc, (.br e.1, [e]), ?_, ?_⟩
    · simp [reverseTerminator, hty, hops, hsucc, argPtrs, hok]
    · exact ⟨rfl, rfl, by simpa using hea⟩
  | condBr c yes no =>
    obtain ⟨x, cs, y, n, ys, ns, op, hc, -, hy, hn, hm, rfl⟩ := h
    obtain ⟨hty, hops, hsucc, hprops⟩ := MatchesTermOp.eqs hm
    obtain ⟨r, hr, hd⟩ := reverseOperand_tile hD.ids hc hv.1
    obtain ⟨e₁, hok₁, rfl, hea₁, hl₁, hc₁⟩ := reverseEdge_ok hD hy
    obtain ⟨e₂, hok₂, rfl, hea₂, hl₂, hc₂⟩ := reverseEdge_ok hD hn
    refine ⟨cs ++ argOps ys ++ argOps ns, op, rfl, by simp_all [or_imp, OperandTile.const hc],
      (.condBr r e₁.1 e₂.1, [e₁, e₂]), ?_, ?_⟩
    · simp [reverseTerminator, hty, hops, hsucc, hprops, argPtrs, ← hl₁, ← hl₂, hok₁, hok₂, hr]
    · refine ⟨by simpa [ResolvedTerminator.normalizeLiterals, Decodes] using hd, rfl, by simp [hea₁, hea₂]⟩

/-! ## Blocks -/

/-- The instruction ID of the first instruction of block `i`. -/
def blockOffset (f : ResolvedFunction) (i : BlockId) : Nat := ((f.blocks.toList.take i).map (·.insts.length)).sum

/-- The source block `src`, numbered `i`, lowers to the ops `ops`. -/
def LowersBlockOps (ctx : WfIRContext OpCode) (f : ResolvedFunction) (body : Array BlockPtr) (values : ValueMap)
    (i : BlockId) (src : ResolvedBlock) (ops : List OperationPtr) : Prop :=
  ∃ instTiles termTile, ResolvesList (LowersResolvedInstTile ctx values) (src.insts.zipIdx (blockOffset f i)) instTiles ∧
    LowersTerminatorTile ctx f (body[·]?) values i src.terminator termTile ∧ ops = instTiles.flatten ++ termTile

/-- A decoded block's non-phi instructions and terminator agree with `src`. -/
def BlockDecodes (f : ResolvedFunction) (i : BlockId) (src : ResolvedBlock) :
    List ResolvedInst × ResolvedTerminator × List ReverseEdge → Prop
  | (insts, d) => ResolvesList NormEq insts (src.insts.filter (·.phiType.isNone)) ∧ TermDecodes f i src.terminator d

theorem reverseInst_tiles {ctx : WfIRContext OpCode} (hI : IdsAgree ctx.raw f values ids)
    {xs : List (ResolvedInst × Nat)} (hi : ResolvesList (LowersResolvedInstTile ctx values) xs tiles)
    (hv : ∀ x ∈ xs, ValidResolvedInst f.header.params.length (NumInsts f) nb x.1) :
    (∀ x ∈ tiles.flatten, ∃ y, reverseInst ctx.raw (reverseOperand ctx.raw ids) x = .ok y) ∧
      ResolvesList NormEq
        (tiles.flatten.filterMap fun x => (reverseInst ctx.raw (reverseOperand ctx.raw ids) x).toOption.join)
        ((xs.map Prod.fst).filter (·.phiType.isNone)) := by
  induction hi with
  | nil => exact ⟨by simp, .nil⟩
  | @cons x tile _ _ hx _ ih =>
    obtain ⟨hok, hr⟩ := reverseInst_tile hI hx (hv x (by simp))
    obtain ⟨hok', hr'⟩ := ih fun y hy => hv y (List.mem_cons_of_mem _ hy)
    refine ⟨by simp only [List.flatten_cons, List.mem_append]; exact fun y hy => hy.elim (hok y) (hok' y), ?_⟩
    rw [List.flatten_cons, List.filterMap_append, List.map_cons, ← List.singleton_append, List.filter_append]
    exact resolves_append hr hr'

theorem reverseBlock_ok (hD : DecodeCtx ctx f body values ids blockIds)
    (h : LowersBlockOps ctx f body values i src ops) (hsrc : src ∈ f.blocks.toList) :
    ∃ d, reverseBlock ctx.raw blockIds (reverseOperand ctx.raw ids) ops = .ok d ∧ BlockDecodes f i src d := by
  obtain ⟨tiles, tt, hi, ht, rfl⟩ := h
  obtain ⟨pre, term, rfl, hpre, d, hd, htd⟩ := reverseTerminator_tile hD ht (hD.valid src hsrc).2
  obtain ⟨hok, hr⟩ := reverseInst_tiles hD.ids hi fun x hx =>
    (hD.valid src hsrc).1 _ (List.fst_mem_of_mem_zipIdx hx)
  have hc : ∀ c ∈ pre, reverseInst ctx.raw (reverseOperand ctx.raw ids) c = .ok none :=
    fun c hc => reverseInst_const (hpre c hc)
  rw [← List.append_assoc]
  refine ⟨((tiles.flatten ++ pre).filterMap fun x => (reverseInst ctx.raw (reverseOperand ctx.raw ids) x).toOption.join,
    d), ?_, ?_⟩
  · simp only [reverseBlock, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.reverse_reverse]
    rw [filterMapM_ok (fun x hx => (List.mem_append.mp hx).elim (hok x) (fun hx => ⟨_, hc x hx⟩)), ok_bind, hd]
    rfl
  · refine ⟨?_, htd⟩
    have hn : pre.filterMap (fun x => (reverseInst ctx.raw (reverseOperand ctx.raw ids) x).toOption.join) = [] :=
      List.filterMap_eq_nil_iff.mpr fun c hc' => by simp [hc c hc', Except.toOption]
    rw [List.filterMap_append, hn, List.append_nil]
    simpa using hr

/-! ## Phis -/

theorem mem_incomingEdges {E : List (List ReverseEdge)} :
    (s, vals) ∈ incomingEdges E dst ↔ ∃ es, E[s]? = some es ∧ (dst, vals) ∈ es := by
  simp only [incomingEdges, List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq, Prod.mk.injEq,
    List.mk_mem_zipIdx_iff_getElem?, Prod.exists]
  grind

theorem countP_incomingEdges_aux (E : List (List ReverseEdge)) (n : Nat) :
    ((E.zipIdx n).flatMap fun (es, src) => (es.filter (·.1 == dst)).map fun (_, values) => (src, values)).countP
      (·.1 = s) = if n ≤ s then (E[s - n]?.map fun es => (es.map Prod.fst).count dst).getD 0 else 0 := by
  induction E generalizing n with
  | nil => simp
  | cons e E ih =>
    rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append, ih]
    simp only [List.countP_map, Function.comp_def]
    by_cases hn : n = s
    · subst hn; simp [List.count_eq_countP, List.countP_filter, Function.comp_def, Nat.not_succ_le_self]
    · by_cases hs : n ≤ s
      · have : s - n = (s - (n + 1)) + 1 := by omega
        simp [hn, hs, show n + 1 ≤ s by omega, this]
      · simp [hn, hs, show ¬ n + 1 ≤ s by omega]

theorem countP_incomingEdges (E : List (List ReverseEdge)) :
    (incomingEdges E dst).countP (·.1 = s) = (E[s]?.map fun es => (es.map Prod.fst).count dst).getD 0 := by
  simpa [incomingEdges] using countP_incomingEdges_aux (dst := dst) (s := s) E 0

theorem perm_of_agree {l₁ l₂ : List (Nat × α)} [DecidableEq α] (hsub : ∀ x ∈ l₁, x ∈ l₂)
    (hag : ∀ x ∈ l₂, ∀ y ∈ l₂, x.1 = y.1 → x.2 = y.2)
    (hc : ∀ s, l₁.countP (·.1 = s) = l₂.countP (·.1 = s)) : l₁.Perm l₂ := by
  refine List.perm_iff_count.mpr fun a => ?_
  by_cases ha : a ∈ l₂
  · have key {l : List (Nat × α)} (hl : ∀ x ∈ l, x ∈ l₂) : l.count a = l.countP (·.1 = a.1) := by
      rw [List.count_eq_countP]
      exact List.countP_congr fun x hx => by
        simpa [Prod.ext_iff] using fun h => hag x (hl x hx) a ha h
    rw [key hsub, key fun _ h => h, hc]
  · rw [List.count_eq_zero.mpr ha, List.count_eq_zero.mpr fun h => ha (hsub a h)]

theorem resolvesList_map_fst {P : α × β → α × γ → Prop} (hP : ∀ x y, P x y → y.1 = x.1)
    (h : ResolvesList P xs ys) : ys.map Prod.fst = xs.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons hp _ ih => simp [hP _ _ hp, ih]

theorem resolvesList_mem_right (h : ResolvesList R xs ys) (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => simp at hy
  | cons hr _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hr⟩ := ih hy; exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- The decoded edges of each block agree with its terminator. -/
def EdgesAgree (f : ResolvedFunction) (E : List (List ReverseEdge)) : Prop :=
  E.length = f.blocks.size ∧ ∀ (s : Nat) es sb, E[s]? = some es → f.blocks[s]? = some sb →
    es.map Prod.fst = sb.terminator.successors ∧ ∀ e ∈ es, EdgeArgs f s e

/-- The normalized incoming pairs of a phi of type `ty`. -/
def normIncoming (ty : LLType) (xs : List (BlockId × ResolvedValue)) : List (BlockId × ResolvedValue) :=
  xs.map fun (src, v) => (src, v.normalize ty)

theorem count_edges (hE : EdgesAgree f E) (s : Nat) :
    (E[s]?.map fun es => (es.map Prod.fst).count dst).getD 0 =
      ((f.blocks[s]?.map (·.terminator.successors)).getD []).count dst := by
  cases he : E[s]? with
  | none =>
    have : f.blocks.size ≤ s := hE.1 ▸ List.getElem?_eq_none_iff.mp he
    simp [Array.getElem?_eq_none this]
  | some es =>
    obtain ⟨sb, hs⟩ : ∃ sb, f.blocks[s]? = some sb :=
      Option.isSome_iff_exists.mp (by simp [← hE.1, (List.getElem?_eq_some_iff.mp he).1])
    simp [hs, (hE.2 s es sb he hs).1]

theorem reversePhi_ok {E : List (List ReverseEdge)} {i : Nat} (hE : EdgesAgree f E)
    (ht : f.blocks[dst]? = some target) (hp : (phis target)[i]? = some (ResolvedInst.phi ty incoming))
    (hag : PhiInputsAgree incoming)
    (hc : ∀ s, incoming.countP (·.1 = s) = ((f.blocks[s]?.map (·.terminator.successors)).getD []).count dst) :
    ∃ inputs, (incomingEdges E dst).mapM (reversePhiInput i) = Except.ok inputs ∧
      (normIncoming ty inputs).Perm (normIncoming ty incoming) := by
  obtain ⟨inputs, hok, hr⟩ := mapM_ok (P := fun (x : BlockId × Array ResolvedValue) (y : BlockId × ResolvedValue) =>
      y.1 = x.1 ∧ ∃ input, (x.1, input) ∈ incoming ∧ Decodes ty y.2 input) (xs := incomingEdges E dst)
    (g := reversePhiInput i) fun ⟨s, vals⟩ hm => by
    obtain ⟨es, hes, hd⟩ := mem_incomingEdges.mp hm
    obtain ⟨sb, hsb⟩ : ∃ sb, f.blocks[s]? = some sb := Option.isSome_iff_exists.mp
      (by simp [← hE.1, (List.getElem?_eq_some_iff.mp hes).1])
    obtain ⟨target', ht', hr⟩ := (hE.2 s es sb hes hsb).2 _ hd
    cases ht.symm.trans ht'
    have hi : i < (phis target).length := (List.getElem?_eq_some_iff.mp hp).1
    have hv := resolves_getElem hr i hi
    simp only [List.getElem?_eq_some_iff.mp hp |>.2] at hv
    obtain ⟨input, hin, hdec⟩ := hv
    have hl : i < vals.size := by have := resolves_length hr; simp at this; omega
    exact ⟨(s, vals[i]), by simp [reversePhiInput, hl], rfl, input, hin, by simpa using hdec⟩
  refine ⟨inputs, hok, perm_of_agree ?_ ?_ fun s => ?_⟩
  · simp only [normIncoming, List.mem_map]
    rintro _ ⟨⟨s, v⟩, hm, rfl⟩
    obtain ⟨x, -, rfl, input, hin, hdec⟩ := resolvesList_mem_right hr hm
    exact ⟨_, hin, by simp only [Decodes] at hdec; simp [hdec]⟩
  · simp only [normIncoming, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
    simp [hag x hx y hy h]
  · have hf := resolvesList_map_fst (fun _ _ h => h.1) hr
    have e1 (l : List (BlockId × ResolvedValue)) : (normIncoming ty l).countP (·.1 = s) = l.countP (·.1 = s) := by
      simp [normIncoming, List.countP_map, Function.comp_def]
    rw [e1, e1, hc, ← count_edges hE, ← countP_incomingEdges]
    simpa [Function.comp_def, List.countP_map] using congrArg (List.countP (· = s)) hf

/-- Two phis agree up to literal spelling and input order. -/
def PhiEq (a b : ResolvedInst) : Prop := a.normalizeLiterals.Equiv b.normalizeLiterals

theorem reversePhis_ok {E : List (List ReverseEdge)} (hE : EdgesAgree f E)
    (ht : f.blocks[dst]? = some target)
    (htypes : (b.getArgumentTypes! raw).toList = (phis target).filterMap (·.phiType.map lowerType))
    (hphi : ∀ ty incoming, .phi ty incoming ∈ phis target → PhiInputsAgree incoming ∧
      ∀ s, incoming.countP (·.1 = s) = ((f.blocks[s]?.map (·.terminator.successors)).getD []).count dst) :
    ∃ ps, reversePhis raw b (incomingEdges E dst) = .ok ps ∧ ResolvesList PhiEq ps (phis target) := by
  suffices h : ∀ (ps : List ResolvedInst) k, (∀ j p, ps[j]? = some p → (phis target)[k + j]? = some p) →
      ∃ out, ((ps.filterMap (·.phiType.map lowerType)).zipIdx k).mapM (fun (ty, i) => do
        let inputs ← (incomingEdges E dst).mapM (reversePhiInput i)
        return ResolvedInst.phi (← reverseIntType ty.val) inputs) = .ok out ∧ ResolvesList PhiEq out ps by
    simpa [reversePhis, htypes] using h (phis target) 0 (by simp)
  intro ps
  induction ps with
  | nil => exact fun _ _ => ⟨[], rfl, .nil⟩
  | cons p ps ih =>
    intro k hk
    have hp : (phis target)[k]? = some p := by simpa using hk 0 p rfl
    obtain ⟨out, hout, hr⟩ := ih (k + 1) fun j q hq => by simpa [Nat.add_assoc, Nat.add_comm 1] using hk (j + 1) q hq
    have hmem := List.mem_of_getElem? hp
    cases p with
    | bin => simp [phis, ResolvedInst.phiType] at hmem
    | phi ty incoming =>
      obtain ⟨inputs, hin, hperm⟩ := reversePhi_ok hE ht hp (hphi _ _ hmem).1 (hphi _ _ hmem).2
      refine ⟨.phi ty inputs :: out, ?_, .cons ⟨rfl, hperm⟩ hr⟩
      have hfm : (ResolvedInst.phi ty incoming :: ps).filterMap (·.phiType.map lowerType) =
          lowerType ty :: ps.filterMap (·.phiType.map lowerType) := rfl
      rw [hfm, List.zipIdx_cons, List.mapM_cons, hout]
      simp [hin, reverseIntType_lowerType]

/-! ## Value numbering -/

/-- The result `reverseValueIds` numbers for an op, if any. -/
def binResult (raw : IRContext OpCode) (op : OperationPtr) : Option ValuePtr :=
  (reverseBinOp (op.getOpType! raw)).map fun _ => .opResult (op.getResult 0)

/-- The values `reverseValueIds` numbers in one block. -/
def blockDefs (raw : IRContext OpCode) (entry : BlockPtr) (p : BlockPtr × List OperationPtr) : List ValuePtr :=
  (if p.1 = entry then [] else (p.1.getArguments! raw).toList) ++ p.2.filterMap (binResult raw)

theorem reverseValueIds_eq : reverseValueIds raw entry blocks = Std.HashMap.ofList
    ((entry.getArguments! raw).toList.zipIdx.map (fun p => (p.1, ValueId.param p.2)) ++
      (blocks.flatMap (blockDefs raw entry)).zipIdx.map fun p => (p.1, .inst p.2)) := rfl

theorem binResult_const (h : c.getOpType! raw = .llvm .mlir__constant) : binResult raw c = none := by
  simp [binResult, h, reverseBinOp]

theorem tile_defs {ctx : WfIRContext OpCode} (h : LowersResolvedInstTile ctx values x tile) :
    (tile.filterMap (binResult ctx.raw)).map some =
      if x.1.phiType = none then [values (.inst x.2)] else [] := by
  obtain ⟨inst | ⟨ty, incoming⟩, k⟩ := x
  · obtain ⟨opc, ty, l, r⟩ := inst
    obtain ⟨vl, vr, cl, cr, op, rfl, htl, htr, hval, hm⟩ := h
    have ht : op.getOpType! ctx.raw = .llvm (binOpcode opc) := congrArg Prod.fst hm.2.2
    have hc : ∀ c ∈ cl ++ cr, binResult ctx.raw c = none := fun c hc =>
      binResult_const ((List.mem_append.mp hc).elim (OperandTile.const htl c) (OperandTile.const htr c))
    rw [List.filterMap_append, List.filterMap_eq_nil_iff.mpr hc]
    cases opc <;> simp [binResult, ht, binOpcode, reverseBinOp, hval, ResolvedInst.phiType]
  · cases (h : tile = []); simp [ResolvedInst.phiType]

theorem defs_block {ctx : WfIRContext OpCode} {xs : List (ResolvedInst × Nat)}
    (ht : ResolvesList (LowersResolvedInstTile ctx values) xs tiles)
    (hx : xs.Pairwise fun a b => b.1.phiType ≠ none → a.1.phiType ≠ none)
    (hf : FilterRel (fun x y => x = y ∧ x.1.phiType ≠ none) xs phs)
    (hr : ResolvesList (fun x arg => values (.inst x.2) = some arg) phs args) :
    (args ++ tiles.flatten.filterMap (binResult ctx.raw)).map some = xs.map fun x => values (.inst x.2) := by
  induction ht generalizing phs args with
  | nil => cases hf; cases hr; rfl
  | @cons x tile xs tiles hx' _ ih =>
    have hd := tile_defs hx'
    obtain ⟨hhead, hx⟩ := List.pairwise_cons.mp hx
    cases hf with
    | keep hm hf =>
      obtain ⟨rfl, hp⟩ := hm
      cases hr with
      | cons ha hr =>
        have hn : tile.filterMap (binResult ctx.raw) = [] := by simpa [hp] using hd
        rw [List.flatten_cons, List.filterMap_append, hn, List.nil_append, List.cons_append, List.map_cons,
          ih hx hf hr, List.map_cons, ha]
    | drop hn hf =>
      have hp : x.1.phiType = none := Classical.byContradiction fun h => hn ⟨x, rfl, h⟩
      have hnone : ∀ y ∈ xs, y.1.phiType = none := fun y hy =>
        Classical.byContradiction fun h => hhead y hy h hp
      cases FilterRel.eq_filter hf
      rw [List.filter_eq_nil_iff.mpr (by simpa using hnone)] at hf hr
      cases hr
      have := ih hx hf .nil
      rw [List.nil_append] at this
      simp only [hp, ↓reduceIte] at hd
      rw [List.nil_append, List.flatten_cons, List.filterMap_append, List.map_append, hd, this,
        List.map_cons]; rfl

theorem phiArgs_const {ctx : WfIRContext OpCode}
    (hr : ResolvesList (fun phi arg => PhiPassesArg ctx values src phi arg ∧
      phi.phiType.map lowerType = some (typeOf ctx.raw arg.1)) phs args) :
    ∀ c ∈ argOps args, c.getOpType! ctx.raw = .llvm .mlir__constant := by
  induction hr with
  | nil => simp [argOps]
  | @cons phi arg _ _ hp _ ih =>
    intro c hc
    simp only [argOps, List.flatMap_cons, List.mem_append] at hc
    cases phi with
    | phi => obtain ⟨_, _, ht⟩ := hp.1; exact hc.elim (OperandTile.const ht c) (ih c)
    | bin => exact hp.1.elim

theorem LowersEdge.const (h : LowersEdge ctx f blocks values src dst b args) :
    ∀ c ∈ argOps args, c.getOpType! ctx.raw = .llvm .mlir__constant :=
  let ⟨_, _, _, _, _, _, hr⟩ := h; phiArgs_const hr

theorem termTile_defs (h : LowersTerminatorTile ctx f blocks values src t tile) :
    tile.filterMap (binResult ctx.raw) = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun c hc => ?_
  cases t with
  | ret =>
    obtain ⟨_, cs, op, ho, hm, rfl⟩ := h
    rcases List.mem_append.mp hc with hc | hc
    · exact binResult_const (OperandTile.const ho c hc)
    · simp at hc; subst hc; simp [binResult, (MatchesTermOp.eqs hm).1, reverseBinOp]
  | br =>
    obtain ⟨_, _, op, he, hm, rfl⟩ := h
    rcases List.mem_append.mp hc with hc | hc
    · exact binResult_const (LowersEdge.const he c hc)
    · simp at hc; subst hc; simp [binResult, (MatchesTermOp.eqs hm).1, reverseBinOp]
  | condBr =>
    obtain ⟨_, _, _, _, _, _, op, ho, _, hy, hn, hm, rfl⟩ := h
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with ((hc | hc) | hc) | rfl
    · exact binResult_const (OperandTile.const ho c hc)
    · exact binResult_const (LowersEdge.const hy c hc)
    · exact binResult_const (LowersEdge.const hn c hc)
    · simp [binResult, (MatchesTermOp.eqs hm).1, reverseBinOp]

/-- The facts of `LowersFunction`, stated uniformly for the entry block and the others. -/
structure FunctionShape (ctx : WfIRContext OpCode) (f : ResolvedFunction) (body : Array BlockPtr)
    (entry : BlockPtr) (values : ValueMap) : Prop where
  valid : ValidResolvedFunction f
  nodup : body.toList.Nodup
  size : body.size = f.blocks.size
  entryEq : body[0]? = some entry
  params : ∀ i, values (.param i) = (entry.getArguments! ctx.raw)[i]?
  entryTypes : entry.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty)
  block : ∀ (i : Nat) src, f.blocks[i]? = some src → ∃ b ops, body[i]? = some b ∧
    b.OpChain ctx.raw ops.toArray ∧ LowersBlockOps ctx f body values i src ops ∧
    (i = 0 → ∀ inst ∈ src.insts, inst.phiType = none) ∧
    (i ≠ 0 → src.insts.Pairwise (fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none) ∧
      LowersBlockArgs ctx.raw values f i (src.insts.zipIdx (blockOffset f i)) b)

theorem LowersFunction.shape (h : LowersFunction ctx f op) :
    ∃ region body entry values,
      MatchesOp ctx op Llvm.func #[] #[] #[region]
        (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
          { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
            outputs := #[(lowerType f.header.retType).val] } defaultFuncExtra) ∧
      region.BlockChain ctx.raw body ∧ FunctionShape ctx f body entry values := by
  obtain ⟨hv, region, body, entry, values, hm, hc, hs, he, ⟨src₀, tiles₀, tt₀, hs₀, hb₀, hty, hpar, hnp, hi₀, ht₀, ho₀⟩, hb⟩ := h
  refine ⟨region, body, entry, values, hm, hc, hv, ?_, hs, he, hpar, hty, fun i src hsrc => ?_⟩
  · exact List.nodup_iff_eq_of_getElem_eq.mpr fun i j hi hj he =>
      Classical.byContradiction fun hne => RegionPtr.BlockChain_array_injective hc i j (by simpa using hi)
        (by simpa using hj) hne (by simpa using he)
  by_cases hi : i = 0
  · subst hi
    cases hs₀.symm.trans hsrc
    exact ⟨entry, _, hb₀, ho₀, ⟨tiles₀, tt₀, by simpa [blockOffset] using hi₀, ht₀, rfl⟩, fun _ => hnp,
      fun h => absurd rfl h⟩
  · obtain ⟨b, hbi⟩ : ∃ b, body[i]? = some b := Option.isSome_iff_exists.mp
      (by simp [hs, (Array.getElem?_eq_some_iff.mp hsrc).1])
    obtain ⟨src', tiles, tt, hs', hb', hp, ha, hti, htt, ho⟩ := hb i b hi hbi
    cases hs'.symm.trans hsrc
    exact ⟨b, _, hbi, ho, ⟨tiles, tt, hti, htt, rfl⟩, fun h => absurd h hi, fun _ => ⟨hp, ha⟩⟩

theorem filterRel_nil (h : ∀ x ∈ xs, ¬ ∃ y, R x y) : FilterRel R xs [] := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .drop (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem pairwise_of_none {xs : List (ResolvedInst × Nat)} (h : ∀ x ∈ xs, x.1.phiType = none) :
    xs.Pairwise fun a b => b.1.phiType ≠ none → a.1.phiType ≠ none := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    exact List.pairwise_cons.mpr ⟨fun y hy hn => absurd (h y (by simp [hy])) hn, ih fun y hy => h y (by simp [hy])⟩

theorem FunctionShape.ne_entry {i : Nat} (hS : FunctionShape ctx f body entry values) (hi : i ≠ 0)
    (hb : body[i]? = some b) : b ≠ entry := by
  rintro rfl
  have := List.nodup_iff_eq_of_getElem_eq.mp hS.nodup i 0 (by simpa using (Array.getElem?_eq_some_iff.mp hb).1)
    (by simpa using (Array.getElem?_eq_some_iff.mp hS.entryEq).1)
    (by simp [(Array.getElem?_eq_some_iff.mp hb).2, (Array.getElem?_eq_some_iff.mp hS.entryEq).2])
  exact hi this

theorem blockDefs_eq {i : Nat} (hS : FunctionShape ctx f body entry values) (hsrc : f.blocks[i]? = some src)
    (hb : body[i]? = some b) :
    (blockDefs ctx.raw entry (b, opsOf ctx b)).map some =
      (src.insts.zipIdx (blockOffset f i)).map fun x => values (.inst x.2) := by
  obtain ⟨b', ops, hb', ho, ⟨tiles, tt, hti, htt, rfl⟩, h0, hn⟩ := hS.block i src hsrc
  cases hb.symm.trans hb'
  rw [opsOf_eq ho, blockDefs]
  simp only [List.filterMap_append, termTile_defs htt, List.append_nil]
  by_cases hi : i = 0
  · subst hi
    have he : b = entry := Option.some.inj (hb.symm.trans hS.entryEq)
    have hnone : ∀ x ∈ src.insts.zipIdx (blockOffset f 0), x.1.phiType = none :=
      fun x hx => h0 rfl _ (List.fst_mem_of_mem_zipIdx hx)
    simpa [he] using defs_block (args := []) hti (pairwise_of_none hnone)
      (filterRel_nil fun x hx ⟨_, _, h⟩ => h (hnone x hx)) .nil
  · obtain ⟨hp, phs, hf, hr⟩ := hn hi
    simp only [hS.ne_entry hi hb, ite_false]
    refine defs_block hti ?_ hf (resolvesList_transfer hr fun _ _ _ ⟨_, _, _, _, h, _⟩ => h)
    have : ((src.insts.zipIdx (blockOffset f i)).map Prod.fst).Pairwise
        fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none := by
      rw [List.zipIdx_map_fst]; exact hp
    exact List.pairwise_map.mp this

theorem flatMap_offsets {bs : List ResolvedBlock} {ps : List γ} (part : γ → List δ)
    (V : ResolvedInst × Nat → δ) (o : Nat) (hl : ps.length = bs.length)
    (h : ∀ (i : Nat) b p, bs[i]? = some b → ps[i]? = some p →
      part p = (b.insts.zipIdx (o + ((bs.take i).map (·.insts.length)).sum)).map V) :
    ps.flatMap part = ((bs.flatMap (·.insts)).zipIdx o).map V := by
  induction bs generalizing ps o with
  | nil => cases ps <;> simp_all
  | cons b bs ih =>
    obtain _ | ⟨p, ps⟩ := ps
    · simp at hl
    rw [List.flatMap_cons, List.flatMap_cons, List.zipIdx_append, List.map_append, h 0 b p rfl rfl,
      ih (o + b.insts.length) (by simpa using hl) fun i b' p' hb hp => by
        simpa [Nat.add_assoc] using h (i + 1) b' p' hb hp]
    simp

/-- The values `reverseValueIds` numbers as instructions, in order. -/
noncomputable def defsOf (ctx : WfIRContext OpCode) (body : Array BlockPtr) (entry : BlockPtr) : List ValuePtr :=
  (body.toList.map fun b => (b, opsOf ctx b)).flatMap (blockDefs ctx.raw entry)

theorem defsOf_getElem? (hS : FunctionShape ctx f body entry values) (hk : k < NumInsts f) :
    (defsOf ctx body entry)[k]? = values (.inst k) := by
  have he : (defsOf ctx body entry).map some =
      ((f.blocks.toList.flatMap (·.insts)).zipIdx 0).map fun x => values (.inst x.2) := by
    rw [defsOf, List.map_flatMap]
    refine flatMap_offsets _ _ 0 (by simp [hS.size]) fun i src p hsrc hp => ?_
    obtain ⟨b, hb, rfl⟩ := List.getElem?_map ▸ hp |> Option.map_eq_some_iff.mp
    simpa [blockOffset] using blockDefs_eq hS (by simpa using hsrc) (by simpa using hb)
  have := congrArg (·[k]?) he
  simp only [List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add] at this
  rw [List.getElem?_eq_getElem hk] at this
  obtain ⟨a, h₁, h₂⟩ := by simpa using this
  rw [h₁, h₂]

section ValueNumbering

variable {raw : IRContext OpCode} {b entry : BlockPtr} {v : ValuePtr} {ops : List OperationPtr}

theorem mem_getArguments (h : v ∈ (b.getArguments! raw).toList) : ∃ j, v = .blockArgument ⟨b, j⟩ := by
  simp only [BlockPtr.getArguments!, Array.toList_map, List.mem_map] at h
  obtain ⟨j, -, rfl⟩ := h
  exact ⟨j, rfl⟩

theorem getArguments_nodup : (b.getArguments! raw).toList.Nodup := by
  simp only [BlockPtr.getArguments!, Array.toList_map, Array.toList_range, List.Nodup, List.pairwise_map]
  exact (List.nodup_range).imp fun h he => h (by cases he; rfl)

theorem mem_blockDefs (hv : v ∈ blockDefs raw entry (b, ops)) :
    (∃ op ∈ ops, v = .opResult (op.getResult 0) ∧ reverseBinOp (op.getOpType! raw) ≠ none) ∨
      (b ≠ entry ∧ ∃ j, v = .blockArgument ⟨b, j⟩) := by
  simp only [blockDefs, List.mem_append, List.mem_filterMap, binResult, Option.map_eq_some_iff] at hv
  rcases hv with hv | ⟨op, hop, bin, hbin, rfl⟩
  · split at hv
    · simp at hv
    · exact .inr ⟨‹_›, mem_getArguments hv⟩
  · exact .inl ⟨op, hop, rfl, by simp [hbin]⟩

theorem blockDefs_nodup (hn : ops.Nodup) : (blockDefs raw entry (b, ops)).Nodup := by
  refine List.nodup_append.mpr ⟨?_, ?_, fun x hx y hy => ?_⟩
  · split
    · exact List.nodup_nil
    · exact getArguments_nodup
  · refine List.pairwise_filterMap.mpr (hn.imp fun hne x hx y hy he => hne ?_)
    simp only [binResult, Option.map_eq_some_iff] at hx hy
    obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, rfl⟩ := hy
    cases he; rfl
  · split at hx
    · simp at hx
    · obtain ⟨j, rfl⟩ := mem_getArguments hx
      simp only [List.mem_filterMap, binResult, Option.map_eq_some_iff] at hy
      obtain ⟨_, _, _, _, rfl⟩ := hy
      nofun

theorem FunctionShape.chain (hS : FunctionShape ctx f body entry values) (hb : b ∈ body.toList) :
    b.OpChain ctx.raw (opsOf ctx b).toArray := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨src, hsrc⟩ : ∃ src, f.blocks[i]? = some src := Option.isSome_iff_exists.mp
    (by simpa [← hS.size] using (List.getElem?_eq_some_iff.mp hi).1)
  obtain ⟨b', ops, hb', ho, -⟩ := hS.block i src hsrc
  cases (by simpa using hi : body[i]? = some b).symm.trans hb'
  simpa [opsOf_eq ho] using ho

/-- The block that defines a value. -/
def ownerBlock (raw : IRContext OpCode) : ValuePtr → Option BlockPtr
  | .blockArgument a => some a.block
  | .opResult r => r.op.getParent! raw

theorem keys_nodup (hS : FunctionShape ctx f body entry values) :
    ((entry.getArguments! ctx.raw).toList ++ defsOf ctx body entry).Nodup := by
  have owner {b v} (hb : b ∈ body.toList) (hv : v ∈ blockDefs ctx.raw entry (b, opsOf ctx b)) :
      ownerBlock ctx.raw v = some b := by
    rcases mem_blockDefs hv with ⟨op, hop, rfl, -⟩ | ⟨-, j, rfl⟩
    · exact (hS.chain hb).opParent (by simpa using hop)
    · rfl
  refine List.nodup_append.mpr ⟨getArguments_nodup, ?_, fun x hx y hy => ?_⟩
  · refine List.pairwise_flatMap.mpr ⟨fun p hp => ?_, List.pairwise_map.mpr ?_⟩
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
      exact blockDefs_nodup (by simpa using BlockPtr.OpChain_array_toList_Nodup (hS.chain hb))
    · exact hS.nodup.imp_of_mem fun hb hc hne x hx y hy he => hne
        (Option.some.inj ((owner hb hx).symm.trans (he ▸ owner hc hy)))
  · obtain ⟨j, rfl⟩ := mem_getArguments hx
    obtain ⟨_, hp, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hp
    rcases mem_blockDefs hy with ⟨_, _, rfl, -⟩ | ⟨hne, _, rfl⟩
    · nofun
    · exact fun he => hne (by cases he; rfl)

theorem idsAgree (hS : FunctionShape ctx f body entry values) :
    IdsAgree ctx.raw f values (reverseValueIds ctx.raw entry (body.toList.map fun b => (b, opsOf ctx b))) := by
  have hn := keys_nodup hS
  rw [reverseValueIds_eq]
  have hkeys : (((entry.getArguments! ctx.raw).toList.zipIdx.map fun p => (p.1, ValueId.param p.2)) ++
      (defsOf ctx body entry).zipIdx.map fun p => (p.1, ValueId.inst p.2)).map Prod.fst =
      (entry.getArguments! ctx.raw).toList ++ defsOf ctx body entry := by
    simp only [List.map_append, List.map_map, Function.comp_def]
    rw [List.zipIdx_map_fst, List.zipIdx_map_fst]
  refine ⟨fun id v hv hval => getElem?_ofList (hkeys ▸ hn) ?_, fun c hc => getElem?_ofList_none fun p hp he => ?_⟩
  · cases id with
    | param i =>
      refine List.mem_append_left _ (List.mem_map.mpr ⟨(v, i), List.mk_mem_zipIdx_iff_getElem?.mpr ?_, rfl⟩)
      simpa [← hS.params i] using hval
    | inst k =>
      refine List.mem_append_right _ (List.mem_map.mpr ⟨(v, k), List.mk_mem_zipIdx_iff_getElem?.mpr ?_, rfl⟩)
      exact (defsOf_getElem? hS hv).trans hval
  · have hm : p.1 ∈ (entry.getArguments! ctx.raw).toList ++ defsOf ctx body entry :=
      hkeys ▸ List.mem_map_of_mem hp
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j, hj⟩ := mem_getArguments hm
      rw [hj] at he; cases he
    · obtain ⟨_, hq, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hq
      rcases mem_blockDefs hm with ⟨op, -, hop, hb⟩ | ⟨-, _, hj⟩
      · rw [hop] at he
        cases he
        exact hb (by simp [hc, reverseBinOp])
      · rw [hj] at he; cases he

end ValueNumbering

/-! ## Functions -/

theorem resolvesList_of_lookup (hl : xs.length = ys.length)
    (h : ∀ (i : Nat) x y, xs[i]? = some x → ys[i]? = some y → R x y) : ResolvesList R xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [ResolvesList.nil]
  | cons x xs ih =>
    obtain _ | ⟨y, ys⟩ := ys
    · simp at hl
    exact .cons (h 0 x y rfl rfl) (ih (by simpa using hl) fun i x y hx hy => h (i + 1) x y hx hy)

theorem resolvesList_map {S : γ → δ → Prop} {g : α → γ} {h : β → δ} (hr : ResolvesList R xs ys)
    (hs : ∀ x y, R x y → S (g x) (h y)) : ResolvesList S (xs.map g) (ys.map h) := by
  induction hr with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (hs _ _ hr) ih

theorem phis_append {insts : List ResolvedInst}
    (h : insts.Pairwise fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none) :
    insts = insts.filter (fun i => decide (i.phiType ≠ none)) ++ insts.filter (·.phiType.isNone) := by
  induction insts with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, h⟩ := List.pairwise_cons.mp h
    by_cases hp : x.phiType = none
    · have hn : ∀ y ∈ xs, y.phiType = none := fun y hy => Classical.byContradiction fun h => hx y hy h hp
      have h₁ : xs.filter (fun i => decide (i.phiType ≠ none)) = [] :=
        List.filter_eq_nil_iff.mpr fun y hy => by simp [hn y hy]
      have h₂ : xs.filter (·.phiType.isNone) = xs := List.filter_eq_self.mpr fun y hy => by simp [hn y hy]
      simp only [List.filter_cons, hp, h₁, h₂]; simp
    · simpa [hp] using ih h

/-- A rebuilt block agrees with its source up to literal spelling and phi input order. -/
def BlockEquivN (ret : LLType) (rb src : ResolvedBlock) : Prop :=
  ResolvesList ResolvedInst.Equiv (rb.insts.map (·.normalizeLiterals)) (src.insts.map (·.normalizeLiterals)) ∧
    rb.terminator.normalizeLiterals ret = src.terminator.normalizeLiterals ret

theorem blockEquivN {src : ResolvedBlock}
    (hp : src.insts.Pairwise fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none)
    (hphis : ResolvesList PhiEq ps (phis src)) (hd : BlockDecodes f i src (insts, t, edges)) :
    BlockEquivN f.header.retType ⟨ps ++ insts, t⟩ src := by
  refine ⟨?_, hd.2.1⟩
  rw [phis_append hp, List.map_append, List.map_append]
  exact resolves_append (resolvesList_map hphis fun _ _ h => h)
    (resolvesList_map hd.1 fun _ _ h => h ▸ ResolvedInst.Equiv.refl _)

theorem FunctionShape.index (hS : FunctionShape ctx f body entry values) (hb : b ∈ body.toList) :
    ∃ (i : Nat) (src : ResolvedBlock), body[i]? = some b ∧ f.blocks[i]? = some src ∧
      ∀ (j : Nat), body[j]? = some b → j = i := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  have hl : i < body.size := by simpa using (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨src, hsrc⟩ : ∃ src, f.blocks[i]? = some src :=
    Option.isSome_iff_exists.mp (by simp [← hS.size, hl])
  refine ⟨i, src, by simpa using hi, hsrc, fun j hj => ?_⟩
  exact ((hS.nodup.getElem?_inj (by simpa using hl)).mp (by rw [hi]; simpa using hj.symm)).symm

theorem filter_zipIdx_length {l : List α} (p : α → Bool) :
    ((l.zipIdx o).filter fun x => p x.1).length = (l.filter p).length := by
  rw [← List.zipIdx_map_fst o l, List.filter_map, List.length_map, List.zipIdx_map_fst]; rfl

theorem FunctionShape.decodeCtx (hS : FunctionShape ctx f body entry values) :
    DecodeCtx ctx f body values (reverseValueIds ctx.raw entry (body.toList.map fun b => (b, opsOf ctx b)))
      (Std.HashMap.ofList body.toList.zipIdx) := by
  refine ⟨hS.valid, idsAgree hS, fun j b hb => getElem?_ofList ?_ ?_, fun j b target hj hb ht => ?_⟩
  · simpa [List.zipIdx_map_fst] using hS.nodup
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hb)
  · obtain ⟨b', ops, hb', -, -, -, hn⟩ := hS.block j target ht
    cases hb.symm.trans hb'
    obtain ⟨-, phs, hf, hr⟩ := hn hj
    cases FilterRel.eq_filter hf
    have h₁ := resolves_length hr
    have h₂ := filter_zipIdx_length (o := blockOffset f j) (l := target.insts) fun i => decide (i.phiType ≠ none)
    simp [phis] at h₁ h₂ ⊢; omega

theorem decoded_ok (hS : FunctionShape ctx f body entry values) (hD : DecodeCtx ctx f body values ids blockIds) :
    ∃ DEC, (body.toList.map fun b => (b, opsOf ctx b)).mapM
        (fun x => reverseBlock ctx.raw blockIds (reverseOperand ctx.raw ids) x.2) = .ok DEC ∧
      DEC.length = f.blocks.size ∧
      ∀ (i : Nat) src d, f.blocks[i]? = some src → DEC[i]? = some d → BlockDecodes f i src d := by
  obtain ⟨DEC, hok, hr⟩ := mapM_ok (xs := body.toList.map fun b => (b, opsOf ctx b))
      (g := fun x => reverseBlock ctx.raw blockIds (reverseOperand ctx.raw ids) x.2)
      (P := fun x d => ∀ (i : Nat) src, body[i]? = some x.1 → f.blocks[i]? = some src → BlockDecodes f i src d)
      fun x hx => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, src, hbi, hsrc, huniq⟩ := hS.index hb
    obtain ⟨b', ops, hb', ho, hL, -⟩ := hS.block i src hsrc
    cases hbi.symm.trans hb'
    obtain ⟨d, hd, hdec⟩ := reverseBlock_ok hD hL (List.mem_of_getElem? (by simpa using hsrc))
    refine ⟨d, by simpa [opsOf_eq ho] using hd, fun j src' hj hs => ?_⟩
    cases huniq j hj
    cases hsrc.symm.trans hs
    exact hdec
  refine ⟨DEC, hok, by simp [← resolves_length hr, hS.size], fun i src d hsrc hd => ?_⟩
  have hi : i < body.size := by simpa [hS.size] using (Array.getElem?_eq_some_iff.mp hsrc).1
  have hl := resolves_length hr
  have := resolves_getElem hr i (by simpa using hi)
  simp only [List.getElem_map] at this
  exact (Option.some.inj ((List.getElem?_eq_getElem (by simpa [← hl] using hi)).symm.trans hd)) ▸
    this i src (by simp [hi]) hsrc

theorem pairwise_none {xs : List ResolvedInst} (h : ∀ x ∈ xs, x.phiType = none) :
    xs.Pairwise fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none :=
  List.pairwise_iff_getElem.mpr fun _ _ _ _ _ hn => absurd (h _ (List.getElem_mem _)) hn

theorem filterMap_phis (b : ResolvedBlock) :
    (phis b).filterMap (·.phiType.map lowerType) = b.insts.filterMap (·.phiType.map lowerType) := by
  rw [phis]
  induction b.insts with
  | nil => rfl
  | cons x xs ih => cases hx : x.phiType <;> simp_all

theorem phi_mem_zipIdx {xs : List α} (h : x ∈ xs) : ∃ k, (x, k) ∈ xs.zipIdx o := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
  exact ⟨o + k, List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr ⟨by omega, by simpa using hk⟩⟩

theorem filterMap_zipIdx_fst (g : α → Option β) (l : List α) (o : Nat) :
    (l.zipIdx o).filterMap (fun x => g x.1) = l.filterMap g := by
  induction l generalizing o <;> simp_all [List.zipIdx_cons, List.filterMap_cons]

theorem rebuiltBlock_ok (hS : FunctionShape ctx f body entry values) (hE : EdgesAgree f E)
    (hsrc : f.blocks[i]? = some src) (hb : body[i]? = some b) (hd : BlockDecodes f i src (insts, t, edges)) :
    ∃ rb, (do
      let phis ← if i == 0 then pure [] else reversePhis ctx.raw b (incomingEdges E i)
      return ResolvedBlock.mk (phis ++ insts) t) = Except.ok rb ∧ BlockEquivN f.header.retType rb src := by
  obtain ⟨b', ops, hb', -, -, h0, hn⟩ := hS.block i src hsrc
  cases hb.symm.trans hb'
  by_cases hi : i = 0
  · subst hi
    have hnone : phis src = [] := List.filter_eq_nil_iff.mpr fun x hx => by simp [h0 rfl x hx]
    exact ⟨_, rfl, blockEquivN (pairwise_none (h0 rfl)) (by rw [hnone]; exact .nil) hd⟩
  · obtain ⟨hp, hargs⟩ := hn hi
    have htypes : (b.getArgumentTypes! ctx.raw).toList = (phis src).filterMap (·.phiType.map lowerType) := by
      rw [blockArgs_types hargs, filterMap_phis, List.toList_toArray]
      exact filterMap_zipIdx_fst (fun x : ResolvedInst => x.phiType.map lowerType) src.insts _
    obtain ⟨ps, hps, hrel⟩ := reversePhis_ok hE hsrc htypes fun ty incoming hm => by
      obtain ⟨k, hk⟩ := phi_mem_zipIdx (o := blockOffset f i) (List.mem_filter.mp hm).1
      exact hargs.phiIncoming hk
    exact ⟨_, by simp [hi, hps], blockEquivN hp hrel hd⟩

theorem rebuilt_ok (hS : FunctionShape ctx f body entry values) (hlen : DEC.length = f.blocks.size)
    (hdec : ∀ (i : Nat) src d, f.blocks[i]? = some src → DEC[i]? = some d → BlockDecodes f i src d) :
    ∃ RB, ((body.toList.zip DEC).zipIdx.mapM fun ((block, insts, terminator, _), dst) => do
        let phis ← if dst == 0 then pure [] else
          reversePhis ctx.raw block (incomingEdges (DEC.map fun (d : List ResolvedInst × ResolvedTerminator × List ReverseEdge) => d.2.2) dst)
        return ResolvedBlock.mk (phis ++ insts) terminator) = .ok RB ∧ RB.length = f.blocks.size ∧
      ∀ (i : Nat) rb src, RB[i]? = some rb → f.blocks[i]? = some src → BlockEquivN f.header.retType rb src := by
  have hE : EdgesAgree f (DEC.map fun d => d.2.2) := ⟨by simp [hlen], fun s es sb hes hsb => by
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ hes)
    exact (hdec s sb d hsb hd).2.2⟩
  refine mapM_ok' (fun (x : (BlockPtr × List ResolvedInst × ResolvedTerminator × List ReverseEdge) × Nat) rb =>
      ∀ src, f.blocks[x.2]? = some src → BlockEquivN f.header.retType rb src) (fun x hx => ?_) fun RB hr => ?_
  · obtain ⟨⟨b, insts, t, edges⟩, i⟩ := x
    obtain ⟨hb, hd⟩ := List.getElem?_zip_eq_some.mp (List.mk_mem_zipIdx_iff_getElem?.mp hx)
    obtain ⟨src, hsrc⟩ : ∃ src, f.blocks[i]? = some src := Option.isSome_iff_exists.mp
      (by simp [← hlen, (List.getElem?_eq_some_iff.mp hd).1])
    obtain ⟨rb, hrb, heq⟩ := rebuiltBlock_ok hS hE hsrc (by simpa using hb) (hdec i src _ hsrc hd)
    exact ⟨rb, hrb, fun src' hs => by cases hsrc.symm.trans hs; exact heq⟩
  refine ⟨by simp [← resolves_length hr, hS.size, hlen], fun i rb src hrb hsrc => ?_⟩
  have hi : i < ((body.toList.zip DEC).zipIdx).length :=
    (resolves_length hr) ▸ (List.getElem?_eq_some_iff.mp hrb).1
  have := resolves_getElem hr i hi
  rw [← Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hrb)]
  exact this src (by simpa using hsrc)

theorem params_erase_aux (l : List LLType) (n : Nat) :
    ((l.zipIdx n).map fun x => Param.mk x.1 (ValueId.param x.2).sourceName).map
      (fun p => { p with name := "" }) = l.map (Param.mk · "") := by
  induction l generalizing n <;> simp_all [List.zipIdx_cons]

theorem params_erase (ps : List Param) :
    (((ps.map (·.ty)).zipIdx.map fun x => Param.mk x.1 (ValueId.param x.2).sourceName).map
      fun p => { p with name := "" }) = ps.map fun p => { p with name := "" } := by
  rw [params_erase_aux, List.map_map]; rfl

theorem resolvesList_eq_map {g : α → β} (h : ResolvesList (fun x y => y = g x) xs ys) : ys = xs.map g := by
  induction h <;> simp_all

theorem map_val_lowerType (ps : List Param) :
    (ps.map fun p => lowerType p.ty).map Subtype.val = ps.map fun p => (lowerType p.ty).val := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg (List.cons _) ih

theorem mapM_reverseIntType (ps : List Param) :
    (ps.map fun p => (lowerType p.ty).val).mapM reverseIntType = .ok (ps.map (·.ty)) := by
  induction ps <;> simp_all [reverseIntType_lowerType, List.mapM_cons]

theorem reverseFunction_of_lowers (h : LowersFunction ctx f op) :
    ∃ f', reverseFunction ctx.raw op = .ok f' ∧ f'.Equiv f := by
  obtain ⟨region, body, entry, values, hm, hchain, hS⟩ := LowersFunction.shape h
  obtain ⟨DEC, hdok, hlen, hdec⟩ := decoded_ok hS hS.decodeCtx
  obtain ⟨RB, hrok, hrlen, hreq⟩ := rebuilt_ok hS hlen hdec
  obtain ⟨rest, hbody⟩ : ∃ rest, body.toList = entry :: rest := by
    have := hS.entryEq
    rw [← Array.getElem?_toList] at this
    cases hl : body.toList with
    | nil => simp [hl] at this
    | cons e rest => simp only [hl, List.getElem?_cons_zero, Option.some.injEq] at this; exact ⟨rest, this ▸ rfl⟩
  have hT : op.getOpType! ctx.raw = .llvm .func := congrArg Prod.fst hm.2.2
  have hR := reverseRegion_eq hm.regions_eq hchain
  have hE : (entry.getArgumentTypes! ctx.raw).toList.map Subtype.val =
      f.header.params.map fun p => (lowerType p.ty).val := by
    simp only [hS.entryTypes, Array.toList_map, map_val_lowerType]
  have hpar : (f.header.params.map fun p => (lowerType p.ty).val).mapM reverseIntType =
      .ok (f.header.params.map (·.ty)) := mapM_reverseIntType _
  have hB : body.toList.mapM (fun block => Prod.mk block <$> reverseBlockOps ctx.raw block) =
      .ok (body.toList.map fun b => (b, opsOf ctx b)) := by
    obtain ⟨ys, hok, rfl⟩ := mapM_ok' (xs := body.toList) (g := fun block => Prod.mk block <$> reverseBlockOps ctx.raw block)
      (Q := fun ys => ys = body.toList.map fun b => (b, opsOf ctx b)) (fun x y => y = (x, opsOf ctx x))
      (fun x hx => ⟨_, by simp [reverseBlockOps_eq (hS.chain hx)], rfl⟩) fun _ h => resolvesList_eq_map h
    exact hok
  rw [hbody] at hR hdok hrok hB
  simp only [bind_pure_comp] at hrok
  simp only [reverseFunction, hT, hm.2.1, fromUTF8?_toByteArray, reverseIntType_lowerType, hR, hE, hpar,
    String.toUTF8_eq_toByteArray, Array.toList_map, ok_bind, bind_pure_comp, beq_self_eq_true, ite_true,
    hB, hdok, hrok]
  simp only [Functor.map, Except.map]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [ResolvedFunction.normalizeLiterals, ResolvedFunction.eraseLocalNames]
    rw [params_erase]
  · simp only [ResolvedFunction.normalizeLiterals, ResolvedFunction.eraseLocalNames, Array.toList_map]
    refine resolvesList_of_lookup (by simp [hrlen]) fun i x y hx hy => ?_
    obtain ⟨rb, hrb, rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ hx)
    obtain ⟨src, hsrc, rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ hy)
    exact hreq i rb src hrb (by simpa using hsrc)

end Reverse

theorem reverseModule_lowerModule {m : ResolvedModule} (h : ValidResolvedModule m) :
    ∃ m', (lowerModule m >>= reverseModule.uncurry) = .ok m' ∧ m'.Equiv m :=
  reverseModule_lowerModule_of_reverseFunction h fun _ _ _ hf => Reverse.reverseFunction_of_lowers hf

end Veir.LLVMLowering
