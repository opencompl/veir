import Veir.Parser.LoweringSound
import Veir.Parser.LoweringUnique

/-! Two graphs meeting the lowering specification are isomorphic, so the lowering is correct. -/

namespace Veir.LLVMLowering

open LLVMParserProp NameResolutionSketch Unique



variable {α β γ δ : Type} {R : α → β → Prop}

/-! ### Lists -/

theorem resolves_split (h : ResolvesList R (a ++ b) (c ++ d)) (hl : a.length = c.length) :
    ResolvesList R a c ∧ ResolvesList R b d := by
  induction a generalizing c with
  | nil => cases c <;> simp_all [ResolvesList.nil]
  | cons x a ih =>
    cases c with
    | nil => simp at hl
    | cons y c => cases h with | cons hr ht => exact (ih ht (by simpa using hl)).imp_left (.cons hr)

theorem resolves_flatten {xs : List (List α)} {ys : List (List β)}
    (h : ResolvesList (ResolvesList R) xs ys) : ResolvesList R xs.flatten ys.flatten := by
  induction h <;> simp_all [resolves_append, ResolvesList.nil]

theorem resolves_unflatten {xs : List (List α)} {ys : List (List β)}
    (hl : xs.map List.length = ys.map List.length) (h : ResolvesList R xs.flatten ys.flatten) :
    ResolvesList (ResolvesList R) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [ResolvesList.nil]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq, List.flatten_cons] at hl h
      exact (resolves_split h hl.1).elim fun a b => .cons a (ih hl.2 b)

theorem resolves_zip3 {S : α → γ → Prop} {T U : β → γ → Prop} (h₁ : ResolvesList R xs ys)
    (h₂ : ResolvesList S xs zs) (h : ResolvesList T ys zs)
    (hU : ∀ x y z, x ∈ xs → R x y → S x z → T y z → U y z) : ResolvesList U ys zs := by
  induction h₁ generalizing zs with
  | nil => cases h₂; exact .nil
  | cons hr _ ih =>
    cases h₂ with | cons hs ht => cases h with | cons hu hv =>
      exact .cons (hU _ _ _ List.mem_cons_self hr hs hu)
        (ih ht hv fun x y z hx => hU x y z (List.mem_cons_of_mem _ hx))

theorem resolves_member3 {S : α → γ → Prop} {T : β → γ → Prop} (h₁ : ResolvesList R xs ys)
    (h₂ : ResolvesList S xs zs) (h : ResolvesList T ys zs) (hx : x ∈ xs) :
    ∃ y z, R x y ∧ S x z ∧ T y z := by
  induction h₁ generalizing zs with
  | nil => simp at hx
  | cons hr _ ih =>
    cases h₂ with | cons hs ht => cases h with | cons hu hv =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, _, hr, hs, hu⟩
      · exact ih ht hv hx

theorem resolves_zip_mem {S : α → γ → Prop} (h₁ : ResolvesList R xs ys) (h₂ : ResolvesList S xs zs)
    (h : (y, z) ∈ ys.zip zs) : ∃ x, R x y ∧ S x z := by
  induction h₁ generalizing zs with
  | nil => simp at h
  | cons hr _ ih =>
    cases h₂ with | cons hs ht =>
      rcases List.mem_cons.mp h with he | h
      · cases he; exact ⟨_, hr, hs⟩
      · exact ih ht h

theorem resolves_of_getElem {xs : List α} {ys : List β} (hl : xs.length = ys.length)
    (h : ∀ k (h₁ : k < xs.length) (h₂ : k < ys.length), R xs[k] ys[k]) : ResolvesList R xs ys :=
  resolves_of_zip hl fun p hp => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    simpa using h k (by simp at hk; omega) (by simp at hk; omega)

theorem mem_zip_of_getElem? {k : Nat} {xs : List α} {ys : List β} (h₁ : xs[k]? = some a) (h₂ : ys[k]? = some b) :
    (a, b) ∈ xs.zip ys :=
  List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨h₁, h₂⟩)

/-! ### Operations -/

variable {ctx₁ ctx₂ : WfIRContext OpCode} {φ : OperationPtr → Option OperationPtr}
  {ρ : RegionPtr → Option RegionPtr} {β : BlockPtr → Option BlockPtr}

/-- `OperationAgrees` without the parent link. -/
def Fields (ctx₁ ctx₂ : WfIRContext OpCode) (φ : OperationPtr → Option OperationPtr)
    (ρ : RegionPtr → Option RegionPtr) (β : BlockPtr → Option BlockPtr) (o o' : OperationPtr) : Prop :=
  o.InBounds ctx₁.raw ∧ o'.InBounds ctx₂.raw ∧
  (∀ code : OpCode, o.getProperties! ctx₁.raw code = o'.getProperties! ctx₂.raw code) ∧
  (o.getOpType! ctx₁.raw, o.getResultTypes! ctx₁.raw, o.getAttributes! ctx₁.raw) =
    (o'.getOpType! ctx₂.raw, o'.getResultTypes! ctx₂.raw, o'.getAttributes! ctx₂.raw) ∧
  (o.getOperands! ctx₁.raw).mapM (renameValue? φ β) = some (o'.getOperands! ctx₂.raw) ∧
  (o.getSuccessors! ctx₁.raw).mapM β = some (o'.getSuccessors! ctx₂.raw) ∧
  (o.getRegions! ctx₁.raw).mapM ρ = some (o'.getRegions! ctx₂.raw)

theorem Fields.agrees (h : Fields ctx₁ ctx₂ φ ρ β o o')
    (hp : o ≠ root → (o.getParent! ctx₁.raw).mapM β = some (o'.getParent! ctx₂.raw)) :
    OperationAgrees ctx₁ ctx₂ root φ ρ β o o' :=
  let ⟨a, b, c, d, e, f, g⟩ := h; ⟨a, b, c, d, e, f, g, hp⟩

abbrev Paired (φ : OperationPtr → Option OperationPtr) (o o' : OperationPtr) : Prop := φ o = some o'

theorem MatchesOp.fields {D : Type} [HasOpInfo D] [HasDialect OpCode D] {code : D} {props : propertiesOf code}
    (h₁ : MatchesOp ctx₁ o₁ code ts vs₁ rs₁ props attrs) (h₂ : MatchesOp ctx₂ o₂ code ts vs₂ rs₂ props attrs)
    (hv : vs₁.mapM (renameValue? φ β) = some vs₂) (hr : rs₁.mapM ρ = some rs₂) :
    Fields ctx₁ ctx₂ φ ρ β o₁ o₂ := by
  have hp := h₁.properties_eq h₂
  simp only [MatchesOp, Prod.mk.injEq] at h₁ h₂
  have hs : o₁.getSuccessors! ctx₁.raw = #[] ∧ o₂.getSuccessors! ctx₂.raw = #[] :=
    ⟨Array.eq_empty_of_size_eq_zero (by grind), Array.eq_empty_of_size_eq_zero (by grind)⟩
  refine ⟨h₁.1, h₂.1, hp, by grind, by grind, by simp [hs.1, hs.2], by grind⟩

theorem MatchesTermOp.properties_eq {code : Llvm} {props : propertiesOf code}
    (h₁ : MatchesTermOp ctx₁ o₁ code vs₁ ss₁ props) (h₂ : MatchesTermOp ctx₂ o₂ code vs₂ ss₂ props)
    (c : OpCode) : o₁.getProperties! ctx₁.raw c = o₂.getProperties! ctx₂.raw c := by
  simp only [MatchesTermOp, Prod.mk.injEq] at h₁ h₂
  unfold OperationPtr.getOpType! at h₁ h₂
  unfold OperationPtr.getProperties! at *
  grind [HasDialect.ofDialectProperties_toDialectProperties]

theorem MatchesTermOp.fields {code : Llvm} {props : propertiesOf code}
    (h₁ : MatchesTermOp ctx₁ o₁ code vs₁ ss₁ props) (h₂ : MatchesTermOp ctx₂ o₂ code vs₂ ss₂ props)
    (hv : vs₁.mapM (renameValue? φ β) = some vs₂) (hs : ss₁.mapM β = some ss₂) :
    Fields ctx₁ ctx₂ φ ρ β o₁ o₂ := by
  have hp := h₁.properties_eq h₂
  simp only [MatchesTermOp, Prod.mk.injEq] at h₁ h₂
  refine ⟨h₁.1, h₂.1, hp, by grind, by grind, by grind, by grind⟩



/-! ### Tiles -/

/-- Definitions known on both sides correspond under the renaming. -/
def ValuesAgree (φ : OperationPtr → Option OperationPtr) (β : BlockPtr → Option BlockPtr)
    (f : ResolvedFunction) (values₁ values₂ : ValueMap) : Prop :=
  ∀ id v₁ v₂, ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length (.ref id) →
    values₁ id = some v₁ → values₂ id = some v₂ → renameValue? φ β v₁ = some v₂

theorem rename_result (h : φ o = some o') :
    renameValue? φ β (.opResult (o.getResult 0)) = some (.opResult (o'.getResult 0)) := by
  simp [renameValue?, h, OperationPtr.getResult]

theorem OperandTile.agree (hV : ValuesAgree φ β f values₁ values₂)
    (hv : ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length val)
    (h₁ : OperandTile ctx₁ values₁ ty val v₁ cs₁) (h₂ : OperandTile ctx₂ values₂ ty val v₂ cs₂)
    (hp : ResolvesList (Paired φ) cs₁ cs₂) :
    renameValue? φ β v₁ = some v₂ ∧ ResolvesList (Fields ctx₁ ctx₂ φ ρ β) cs₁ cs₂ := by
  cases val with
  | ref id => obtain ⟨h₁, rfl⟩ := h₁; obtain ⟨h₂, rfl⟩ := h₂; exact ⟨hV id _ _ hv h₁ h₂, .nil⟩
  | intConst =>
    cases ty; obtain ⟨c₁, rfl, rfl, hc₁⟩ := h₁; obtain ⟨c₂, rfl, rfl, hc₂⟩ := h₂
    cases hp with | cons hc _ => exact ⟨rename_result hc, .cons (hc₁.fields hc₂ (by simp) (by simp)) .nil⟩

theorem mapM_pair {x₁ y₁ x₂ y₂ : ValuePtr} (hx : renameValue? φ β x₁ = some x₂) (hy : renameValue? φ β y₁ = some y₂) :
    #[x₁, y₁].mapM (renameValue? φ β) = some #[x₂, y₂] := by
  simp [Array.mapM_eq_mapM_toList, hx, hy]

theorem instTile_agree (hV : ValuesAgree φ β f values₁ values₂)
    (hv : ValidResolvedInst f.header.params.length (f.blocks.toList.flatMap (·.insts)).length f.blocks.size inst)
    (h₁ : LowersResolvedInstTile ctx₁ values₁ (inst, i) t₁) (h₂ : LowersResolvedInstTile ctx₂ values₂ (inst, i) t₂)
    (hp : ResolvesList (Paired φ) t₁ t₂) : ResolvesList (Fields ctx₁ ctx₂ φ ρ β) t₁ t₂ := by
  rcases inst with ⟨_, _, l, r⟩ | _
  · obtain ⟨_, _, _, _, _, rfl, hl₁, hr₁, _, hm₁⟩ := h₁
    obtain ⟨_, _, _, _, _, rfl, hl₂, hr₂, _, hm₂⟩ := h₂
    obtain ⟨hp, ho⟩ := resolves_split hp (by simp [OperandTile.length hl₁, OperandTile.length hl₂,
      OperandTile.length hr₁, OperandTile.length hr₂])
    obtain ⟨hpl, hpr⟩ := resolves_split hp (by simp [OperandTile.length hl₁, OperandTile.length hl₂])
    obtain ⟨hl, hl'⟩ := hl₁.agree (ρ := ρ) hV hv.1 hl₂ hpl
    obtain ⟨hr, hr'⟩ := hr₁.agree (ρ := ρ) hV hv.2 hr₂ hpr
    cases ho with | cons ho _ => exact resolves_append (resolves_append hl' hr') (.cons (hm₁.fields hm₂ (mapM_pair hl hr) (by simp)) .nil)
  · cases h₁; cases h₂; cases hp; exact .nil

variable {f : ResolvedFunction}

abbrev numInsts (f : ResolvedFunction) : Nat := (f.blocks.toList.flatMap (·.insts)).length

abbrev InputTiles (ctx : WfIRContext OpCode) (values : ValueMap) :
    List (LLType × ResolvedValue) → List ArgTile → Prop :=
  ResolvesList (fun (ty, input) arg => OperandTile ctx values ty input arg.1 arg.2)

theorem edge_inputs (hck : checkBlocks f = .ok ()) (hvf : ValidResolvedFunction f) {blocks₁ blocks₂ : BlockMap}
    (h₁ : LowersEdge ctx₁ f blocks₁ values₁ src dst b₁ a₁) (h₂ : LowersEdge ctx₂ f blocks₂ values₂ src dst b₂ a₂) :
    ∃ inputs, (∀ x ∈ inputs, ValidResolvedValue f.header.params.length (numInsts f) x.2) ∧
      InputTiles ctx₁ values₁ inputs a₁ ∧ InputTiles ctx₂ values₂ inputs a₂ := by
  have ha (target : ResolvedBlock) ty incoming hs hp := checkedPhiAgree hck (dst := dst) (target := target)
    (ty := ty) (incoming := incoming) hs hp
  obtain ⟨target, inputs, hs, hi, ho⟩ := phiArgs_source h₁ ha
  obtain ⟨_, _, hs', hi', ho'⟩ := phiArgs_source h₂ ha
  cases hs.symm.trans hs'; cases hi.symm.trans hi'
  refine ⟨inputs, fun ⟨ty, v⟩ hm => ?_, ho, ho'⟩
  obtain ⟨incoming, hp, he⟩ := Complete.selectPhiInputs_mem hi hm
  exact ((hvf _ (Complete.mem_of_get hs)).1 _ hp _ he).2

theorem argOps_cons : argOps (a :: as) = a.2 ++ argOps as := rfl

theorem inputTiles_length (h₁ : InputTiles ctx₁ values₁ inputs a₁) (h₂ : InputTiles ctx₂ values₂ inputs a₂) :
    (argOps a₁).length = (argOps a₂).length := by
  simpa [argOps, List.flatMap_def, Function.comp_def] using
    congrArg List.sum ((phiArgs_widths h₁).trans (phiArgs_widths h₂).symm)

theorem inputTiles_agree (hV : ValuesAgree φ β f values₁ values₂)
    (hval : ∀ x ∈ inputs, ValidResolvedValue f.header.params.length (numInsts f) x.2)
    (h₁ : InputTiles ctx₁ values₁ inputs a₁) (h₂ : InputTiles ctx₂ values₂ inputs a₂)
    (hp : ResolvesList (Paired φ) (argOps a₁) (argOps a₂)) :
    ResolvesList (renameValue? φ β · = some ·) (a₁.map Prod.fst) (a₂.map Prod.fst) ∧
      ResolvesList (Fields ctx₁ ctx₂ φ ρ β) (argOps a₁) (argOps a₂) := by
  induction h₁ generalizing a₂ with
  | nil => cases h₂; exact ⟨.nil, .nil⟩
  | @cons x _ _ _ hx _ ih =>
    cases h₂ with | cons hx' ht' =>
    rcases x with ⟨ty, v⟩
    rw [argOps_cons, argOps_cons] at hp
    obtain ⟨hp, hps⟩ := resolves_split hp (by rw [OperandTile.length hx, OperandTile.length hx'])
    obtain ⟨hr, hf⟩ := hx.agree hV (hval _ List.mem_cons_self) hx' hp
    obtain ⟨ih₁, ih₂⟩ := ih (fun y hy => hval y (List.mem_cons_of_mem _ hy)) ht' hps
    exact ⟨.cons hr ih₁, by rw [argOps_cons, argOps_cons]; exact resolves_append hf ih₂⟩

theorem edge_agree (hV : ValuesAgree φ β f values₁ values₂) (hck : checkBlocks f = .ok ())
    (hvf : ValidResolvedFunction f) {blocks₁ blocks₂ : BlockMap}
    (hβ : ∀ j b₁ b₂, blocks₁ j = some b₁ → blocks₂ j = some b₂ → β b₁ = some b₂)
    (h₁ : LowersEdge ctx₁ f blocks₁ values₁ src dst b₁ a₁) (h₂ : LowersEdge ctx₂ f blocks₂ values₂ src dst b₂ a₂) :
    a₁.length = a₂.length ∧ (argOps a₁).length = (argOps a₂).length ∧ β b₁ = some b₂ ∧
      (ResolvesList (Paired φ) (argOps a₁) (argOps a₂) →
        (argPtrs a₁).mapM (renameValue? φ β) = some (argPtrs a₂) ∧
        ResolvesList (Fields ctx₁ ctx₂ φ ρ β) (argOps a₁) (argOps a₂)) := by
  obtain ⟨inputs, hval, ht₁, ht₂⟩ := edge_inputs hck hvf h₁ h₂
  refine ⟨(resolves_length ht₁).symm.trans (resolves_length ht₂), inputTiles_length ht₁ ht₂,
    hβ dst _ _ h₁.2.1 h₂.2.1, fun hp => ?_⟩
  obtain ⟨hr, hf⟩ := inputTiles_agree hV hval ht₁ ht₂ hp
  exact ⟨resolves_mapM hr, hf⟩

theorem mapM_append_some {σ τ : Type} {g : σ → Option τ} {a b : Array σ} {c d : Array τ}
    (h₁ : a.mapM g = some c) (h₂ : b.mapM g = some d) : (a ++ b).mapM g = some (c ++ d) := by
  simp only [Array.mapM_eq_mapM_toList, Array.toList_append, List.mapM_append] at *
  cases hx : List.mapM g a.toList <;> cases hy : List.mapM g b.toList <;> simp_all <;> subst c d <;> rfl

theorem termTile_agree (hV : ValuesAgree φ β f values₁ values₂) (hck : checkBlocks f = .ok ())
    (hvf : ValidResolvedFunction f) (hs : f.blocks[src]? = some blk) {blocks₁ blocks₂ : BlockMap}
    (hβ : ∀ j b₁ b₂, blocks₁ j = some b₁ → blocks₂ j = some b₂ → β b₁ = some b₂)
    (h₁ : LowersTerminatorTile ctx₁ f blocks₁ values₁ src blk.terminator t₁)
    (h₂ : LowersTerminatorTile ctx₂ f blocks₂ values₂ src blk.terminator t₂)
    (hp : ResolvesList (Paired φ) t₁ t₂) : ResolvesList (Fields ctx₁ ctx₂ φ ρ β) t₁ t₂ := by
  have hvt := (hvf _ (Complete.mem_of_get hs)).2
  generalize blk.terminator = t at h₁ h₂ hvt
  cases t with
  | ret =>
    obtain ⟨_, _, _, hx₁, hm₁, rfl⟩ := h₁; obtain ⟨_, _, _, hx₂, hm₂, rfl⟩ := h₂
    obtain ⟨hp, ho⟩ := resolves_split hp (by rw [OperandTile.length hx₁, OperandTile.length hx₂])
    obtain ⟨hr, hf⟩ := hx₁.agree (ρ := ρ) hV hvt hx₂ hp
    cases ho with | cons ho _ =>
      exact resolves_append hf (.cons (hm₁.fields hm₂ (by simp [Array.mapM_eq_mapM_toList, hr]) (by simp)) .nil)
  | br =>
    obtain ⟨_, _, _, he₁, hm₁, rfl⟩ := h₁; obtain ⟨_, _, _, he₂, hm₂, rfl⟩ := h₂
    obtain ⟨_, hl, hb, hk⟩ := edge_agree (ρ := ρ) hV hck hvf hβ he₁ he₂
    obtain ⟨hp, ho⟩ := resolves_split hp hl
    obtain ⟨hr, hf⟩ := hk hp
    cases ho with | cons ho _ =>
      exact resolves_append hf (.cons (hm₁.fields hm₂ hr (by simp [Array.mapM_eq_mapM_toList, hb])) .nil)
  | condBr =>
    obtain ⟨_, _, _, _, _, _, _, hx₁, _, hy₁, hn₁, hm₁, rfl⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, hx₂, _, hy₂, hn₂, hm₂, rfl⟩ := h₂
    obtain ⟨hly, hy, hby, hky⟩ := edge_agree (ρ := ρ) hV hck hvf hβ hy₁ hy₂
    obtain ⟨hln, hn, hbn, hkn⟩ := edge_agree (ρ := ρ) hV hck hvf hβ hn₁ hn₂
    have hlx := (OperandTile.length hx₁).trans (OperandTile.length hx₂).symm
    obtain ⟨hp, ho⟩ := resolves_split hp (by simp [hlx, hy, hn])
    obtain ⟨hp, hpn⟩ := resolves_split hp (by simp [hlx, hy])
    obtain ⟨hpx, hpy⟩ := resolves_split hp hlx
    obtain ⟨hr, hf⟩ := hx₁.agree (ρ := ρ) hV hvt.1 hx₂ hpx
    obtain ⟨hry, hfy⟩ := hky hpy; obtain ⟨hrn, hfn⟩ := hkn hpn
    rw [← hly, ← hln] at hm₂
    cases ho with | cons ho _ =>
      exact resolves_append (resolves_append (resolves_append hf hfy) hfn) (.cons (hm₁.fields hm₂
        (mapM_append_some (mapM_append_some (by simp [Array.mapM_eq_mapM_toList, hr]) hry) hrn)
        (by simp [Array.mapM_eq_mapM_toList, hby, hbn])) .nil)

/-! ### Blocks -/

theorem mem_of_zipIdx {l : List α} (h : (a, i) ∈ l.zipIdx k) : a ∈ l :=
  List.mem_of_getElem? (List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mp h).2

def blockOffset (f : ResolvedFunction) (k : Nat) : Nat := ((f.blocks.toList.take k).map (·.insts.length)).sum

/-- The instruction and terminator tiles of block `k`, common to entry and non-entry blocks. -/
def BlockTiles (ctx : WfIRContext OpCode) (f : ResolvedFunction) (blocks : BlockMap) (values : ValueMap)
    (k : Nat) (src : ResolvedBlock) (tiles : List (List OperationPtr)) (term : List OperationPtr) : Prop :=
  f.blocks[k]? = some src ∧ ResolvesList (LowersResolvedInstTile ctx values) (src.insts.zipIdx (blockOffset f k)) tiles ∧
    LowersTerminatorTile ctx f blocks values k src.terminator term

theorem blockTiles_of {blocks : BlockMap} (hE : LowersEntry ctx f blocks values entry)
    (hB : ∀ i dst, i ≠ 0 → blocks i = some dst → LowersBlock ctx f blocks values i dst) (hk : blocks k = some dst) :
    ∃ src tiles term, BlockTiles ctx f blocks values k src tiles term ∧
      dst.OpChain ctx.raw (tiles.flatten ++ term).toArray := by
  by_cases h0 : k = 0
  · subst h0; obtain ⟨src, tiles, term, hs, he, _, _, _, hi, ht, hc⟩ := hE
    cases he.symm.trans hk; exact ⟨src, tiles, term, ⟨hs, by simpa [blockOffset] using hi, ht⟩, hc⟩
  · obtain ⟨_, _, _, hs, _, _, _, hi, ht, hc⟩ := hB k dst h0 hk; exact ⟨_, _, _, ⟨hs, hi, ht⟩, hc⟩

theorem tiles_paired {S : OperationPtr → OperationPtr → Prop} {blocks₁ blocks₂ : BlockMap}
    (h₁ : BlockTiles ctx₁ f blocks₁ values₁ k src tiles₁ term₁) (h₂ : BlockTiles ctx₂ f blocks₂ values₂ k src' tiles₂ term₂)
    (hp : ResolvesList S (tiles₁.flatten ++ term₁) (tiles₂.flatten ++ term₂)) :
    src = src' ∧ ResolvesList (ResolvesList S) tiles₁ tiles₂ ∧ ResolvesList S term₁ term₂ := by
  obtain ⟨hs, hi₁, _⟩ := h₁; obtain ⟨hs', hi₂, _⟩ := h₂; cases hs.symm.trans hs'
  have hl := (instTiles_lengths hi₁).trans (instTiles_lengths hi₂).symm
  obtain ⟨hp, hpt⟩ := resolves_split hp (by simp [List.length_flatten, hl])
  exact ⟨rfl, resolves_unflatten hl hp, hpt⟩

theorem block_agree (hV : ValuesAgree φ β f values₁ values₂) (hck : checkBlocks f = .ok ())
    (hvf : ValidResolvedFunction f) {blocks₁ blocks₂ : BlockMap}
    (hβ : ∀ j b₁ b₂, blocks₁ j = some b₁ → blocks₂ j = some b₂ → β b₁ = some b₂)
    (h₁ : BlockTiles ctx₁ f blocks₁ values₁ k src tiles₁ term₁) (h₂ : BlockTiles ctx₂ f blocks₂ values₂ k src' tiles₂ term₂)
    (hp : ResolvesList (Paired φ) (tiles₁.flatten ++ term₁) (tiles₂.flatten ++ term₂)) :
    ResolvesList (Fields ctx₁ ctx₂ φ ρ β) (tiles₁.flatten ++ term₁) (tiles₂.flatten ++ term₂) := by
  obtain ⟨rfl, ht, hpt⟩ := tiles_paired h₁ h₂ hp
  refine resolves_append (resolves_flatten (resolves_zip3 h₁.2.1 h₂.2.1 ht fun ⟨_, _⟩ _ _ hx ha hb hc =>
    instTile_agree hV ((hvf _ (Complete.mem_of_get h₁.1)).1 _ (mem_of_zipIdx hx)) ha hb hc))
    (termTile_agree hV hck hvf h₁.1 hβ h₁.2.2 h₂.2.2 hpt)

/-! ### Values -/

theorem getArguments_getElem? {i : Nat} {v : ValuePtr} {ctx : IRContext OpCode} {b : BlockPtr} (h : (b.getArguments! ctx)[i]? = some v) :
    v = .blockArgument ⟨b, i⟩ := by
  simp only [BlockPtr.getArguments!, Array.getElem?_map, Array.getElem?_range] at h
  split at h <;> simp_all [BlockPtr.getArgument]

theorem args_paired {c₁ c₂ : IRContext OpCode} (hβ : β d₁ = some d₂)
    (hl : (d₁.getArguments! c₁).toList.length = (d₂.getArguments! c₂).toList.length) :
    ResolvesList (renameValue? φ β · = some ·) (d₁.getArguments! c₁).toList (d₂.getArguments! c₂).toList :=
  resolves_of_getElem hl fun _ _ _ => by simp [BlockPtr.getArguments!, BlockPtr.getArgument, renameValue?, hβ]

theorem blockArgs_agree {insts : List (ResolvedInst × Nat)}
    (h₁ : LowersBlockArgs ctx₁.raw values₁ f k insts d₁) (h₂ : LowersBlockArgs ctx₂.raw values₂ f k insts d₂)
    (hβ : β d₁ = some d₂) (hm : (.phi ty inc, i) ∈ insts) (hv₁ : values₁ (.inst i) = some v₁)
    (hv₂ : values₂ (.inst i) = some v₂) : renameValue? φ β v₁ = some v₂ := by
  obtain ⟨phis, hf₁, hr₁⟩ := h₁; obtain ⟨_, hf₂, hr₂⟩ := h₂
  obtain rfl := (FilterRel.eq_filter hf₂).trans (FilterRel.eq_filter hf₁).symm
  obtain ⟨_, hp, rfl, _⟩ := hf₁.mem_of_matches hm ⟨_, rfl, by simp [ResolvedInst.phiType]⟩
  obtain ⟨_, _, ⟨_, _, _, _, ha₁, _⟩, ⟨_, _, _, _, ha₂, _⟩, hr⟩ :=
    resolves_member3 hr₁ hr₂ (args_paired hβ ((resolves_length hr₁).symm.trans (resolves_length hr₂))) hp
  cases hv₁.symm.trans ha₁; cases hv₂.symm.trans ha₂; exact hr

theorem binResult_agree {blocks₁ blocks₂ : BlockMap}
    (h₁ : BlockTiles ctx₁ f blocks₁ values₁ k src tiles₁ term₁) (h₂ : BlockTiles ctx₂ f blocks₂ values₂ k src tiles₂ term₂)
    (hp : ResolvesList (Paired φ) (tiles₁.flatten ++ term₁) (tiles₂.flatten ++ term₂))
    (hm : (.bin b, i) ∈ src.insts.zipIdx (blockOffset f k)) (hv₁ : values₁ (.inst i) = some v₁)
    (hv₂ : values₂ (.inst i) = some v₂) : renameValue? φ β v₁ = some v₂ := by
  obtain ⟨_, ht, _⟩ := tiles_paired h₁ h₂ hp
  rcases b with ⟨_, _, _, _⟩
  obtain ⟨_, _, ⟨_, _, _, _, _, rfl, a₁, b₁, hd₁, _⟩, ⟨_, _, _, _, _, rfl, a₂, b₂, hd₂, _⟩, hpt⟩ :=
    resolves_member3 h₁.2.1 h₂.2.1 ht hm
  cases hv₁.symm.trans hd₁; cases hv₂.symm.trans hd₂
  obtain ⟨_, ho⟩ := resolves_split hpt (by simp [OperandTile.length a₁, OperandTile.length a₂, OperandTile.length b₁, OperandTile.length b₂])
  cases ho with | cons ho _ => exact rename_result ho

theorem values_agree {blocks₁ blocks₂ : BlockMap}
    (hE₁ : LowersEntry ctx₁ f blocks₁ values₁ entry₁) (hE₂ : LowersEntry ctx₂ f blocks₂ values₂ entry₂)
    (hB₁ : ∀ i dst, i ≠ 0 → blocks₁ i = some dst → LowersBlock ctx₁ f blocks₁ values₁ i dst)
    (hB₂ : ∀ i dst, i ≠ 0 → blocks₂ i = some dst → LowersBlock ctx₂ f blocks₂ values₂ i dst)
    (hsz : ∀ k < f.blocks.size, (∃ d, blocks₁ k = some d) ∧ ∃ d, blocks₂ k = some d)
    (hβ : ∀ j b₁ b₂, blocks₁ j = some b₁ → blocks₂ j = some b₂ → β b₁ = some b₂)
    (hφ : ∀ k d₁ d₂, blocks₁ k = some d₁ → blocks₂ k = some d₂ →
      ResolvesList (Paired φ) (opsOf ctx₁ d₁) (opsOf ctx₂ d₂)) :
    ValuesAgree φ β f values₁ values₂ := by
  rintro (i | i) v₁ v₂ hv h₁ h₂
  · obtain ⟨_, _, _, _, he₁, _, hp₁, _⟩ := hE₁; obtain ⟨_, _, _, _, he₂, _, hp₂, _⟩ := hE₂
    rw [hp₁] at h₁; rw [hp₂] at h₂
    simp [getArguments_getElem? h₁, getArguments_getElem? h₂, renameValue?, hβ 0 _ _ he₁ he₂]
  obtain ⟨k, src, hs, hm⟩ := Complete.locate_inst (List.getElem?_eq_getElem hv)
  replace hs : f.blocks[k]? = some src := by simpa using hs
  obtain ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩ := hsz k (Array.getElem?_eq_some_iff.mp hs).1
  obtain ⟨_, _, _, hT₁, hc₁⟩ := blockTiles_of hE₁ hB₁ hd₁
  obtain ⟨_, _, _, hT₂, hc₂⟩ := blockTiles_of hE₂ hB₂ hd₂
  cases hs.symm.trans hT₁.1; cases hs.symm.trans hT₂.1
  have hp := hφ k _ _ hd₁ hd₂; rw [opsOf_eq hc₁, opsOf_eq hc₂] at hp
  rcases hx : (f.blocks.toList.flatMap (·.insts))[i] with b | ⟨ty, inc⟩ <;> rw [hx] at hm
  · exact binResult_agree hT₁ hT₂ (by simpa using hp) hm h₁ h₂
  have hk : k ≠ 0 := by
    rintro rfl; obtain ⟨_, _, _, hs0, _, _, _, hn, _⟩ := hE₁; cases hs.symm.trans hs0
    simpa [ResolvedInst.phiType] using hn _ (mem_of_zipIdx hm)
  obtain ⟨_, _, _, hs₁, _, _, ha₁, _⟩ := hB₁ k d₁ hk hd₁; obtain ⟨_, _, _, hs₂, _, _, ha₂, _⟩ := hB₂ k d₂ hk hd₂
  cases hs.symm.trans hs₁; cases hs.symm.trans hs₂
  exact blockArgs_agree ha₁ ha₂ (hβ k _ _ hd₁ hd₂) hm h₁ h₂

/-! ### Functions -/

def funcProps (f : ResolvedFunction) : propertiesOf Llvm.func :=
  LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
    { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
      outputs := #[(lowerType f.header.retType).val] } defaultFuncExtra

/-- `LowersFunction`, phrased with the region and blocks read back from the graph. -/
def FuncView (ctx : WfIRContext OpCode) (f : ResolvedFunction) (o : OperationPtr) (values : ValueMap) : Prop :=
  MatchesOp ctx o Llvm.func #[] #[] #[regOf ctx o] (funcProps f) ∧
  (regOf ctx o).BlockChain ctx.raw (bodyOf ctx o).toArray ∧ (bodyOf ctx o).length = f.blocks.size ∧
  (∃ entry, (bodyOf ctx o)[0]? = some entry ∧ LowersEntry ctx f ((bodyOf ctx o)[·]?) values entry) ∧
  ∀ i dst, i ≠ 0 → (bodyOf ctx o)[i]? = some dst → LowersBlock ctx f ((bodyOf ctx o)[·]?) values i dst

theorem LowersFunction.view (h : LowersFunction ctx f o) : ∃ values, FuncView ctx f o values := by
  obtain ⟨_, region, body, entry, values, hf, hc, hs, he, hE, hB⟩ := h
  have hr : regOf ctx o = region := by simp [regOf, hf.regions_eq]
  have hb : bodyOf ctx o = body.toList := by rw [bodyOf, hr, blocksOf_eq hc]
  have hl : (fun j : Nat => (bodyOf ctx o)[j]?) = (fun j : Nat => body[j]?) := by funext; simp [hb]
  exact ⟨values, by rw [hr]; exact hf, by simpa [hr, hb] using hc, by simp [hb, hs],
    ⟨entry, by simpa [hb] using he, hl ▸ hE⟩, fun i d hi hd => hl ▸ hB i d hi (by simpa [hb] using hd)⟩

theorem FuncView.tiles {k : Nat} (h : FuncView ctx f o values) (hd : (bodyOf ctx o)[k]? = some d) :
    ∃ src tiles term, BlockTiles ctx f ((bodyOf ctx o)[·]?) values k src tiles term ∧
      d.OpChain ctx.raw (opsOf ctx d).toArray ∧ opsOf ctx d = tiles.flatten ++ term := by
  obtain ⟨_, _, _, ⟨_, _, hE⟩, hB⟩ := h
  obtain ⟨src, tiles, term, hT, hc⟩ := blockTiles_of hE hB hd
  exact ⟨src, tiles, term, hT, by simpa [opsOf_eq hc] using hc, by simp [opsOf_eq hc]⟩

theorem zip_index {σ τ : Type} {a : σ} {b : τ} {xs : List σ} {ys : List τ} (h : (a, b) ∈ xs.zip ys) : ∃ k : Nat, xs[k]? = some a ∧ ys[k]? = some b := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
  exact ⟨k, (List.getElem?_zip_eq_some.mp hk)⟩

variable {o₁ o₂ : OperationPtr} {k : Nat}

theorem chains_paired (hF₁ : FuncView ctx₁ f o₁ values₁) (hF₂ : FuncView ctx₂ f o₂ values₂)
    (hck : checkBlocks f = .ok ()) (hφ : ∀ p ∈ funcOpPairs ctx₁ ctx₂ o₁ o₂, φ p.1 = some p.2)
    (hd₁ : (bodyOf ctx₁ o₁)[k]? = some d₁) (hd₂ : (bodyOf ctx₂ o₂)[k]? = some d₂) :
    ResolvesList (Paired φ) (opsOf ctx₁ d₁) (opsOf ctx₂ d₂) := by
  obtain ⟨_, _, _, ⟨hs, hi₁, ht₁⟩, _, he₁⟩ := hF₁.tiles hd₁
  obtain ⟨_, _, _, ⟨hs', hi₂, ht₂⟩, _, he₂⟩ := hF₂.tiles hd₂
  cases hs.symm.trans hs'
  refine resolves_of_zip (by rw [he₁, he₂]; exact opChains_equal_length hck hi₁ hi₂ ht₁ ht₂) fun p hp => ?_
  exact hφ p (List.mem_flatMap.mpr ⟨_, mem_zip_of_getElem? hd₁ hd₂, hp⟩)

theorem FuncView.entryTypes (h : FuncView ctx f o values) (hd : (bodyOf ctx o)[0]? = some d) :
    d.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty) := by
  obtain ⟨_, _, _, ⟨_, he, _, _, _, _, he', ht, _⟩, _⟩ := h; cases he.symm.trans hd; cases he'.symm.trans hd; exact ht

theorem FuncView.blockTypes (h : FuncView ctx f o values) (hk : k ≠ 0) (hd : (bodyOf ctx o)[k]? = some d)
    (hs : f.blocks[k]? = some src) :
    d.getArgumentTypes! ctx.raw = ((src.insts.zipIdx (blockOffset f k)).filterMap (·.1.phiType.map lowerType)).toArray := by
  obtain ⟨_, _, _, hs', _, _, ha, _⟩ := h.2.2.2.2 k d hk hd
  cases hs.symm.trans hs'; exact blockArgs_types ha

section Function

variable (hF₁ : FuncView ctx₁ f o₁ values₁) (hF₂ : FuncView ctx₂ f o₂ values₂) (hck : checkBlocks f = .ok ())
  (hβ : ∀ p ∈ (bodyOf ctx₁ o₁).zip (bodyOf ctx₂ o₂), β p.1 = some p.2)
  (hφ : ∀ p ∈ funcOpPairs ctx₁ ctx₂ o₁ o₂, φ p.1 = some p.2)
include hF₁ hF₂ hck hβ hφ

theorem FuncView.valuesAgree : ValuesAgree φ β f values₁ values₂ :=
  values_agree hF₁.2.2.2.1.choose_spec.2 hF₂.2.2.2.1.choose_spec.2 hF₁.2.2.2.2 hF₂.2.2.2.2
    (fun _ hk => ⟨⟨_, List.getElem?_eq_getElem (hF₁.2.2.1 ▸ hk)⟩, ⟨_, List.getElem?_eq_getElem (hF₂.2.2.1 ▸ hk)⟩⟩)
    (fun _ _ _ h₁ h₂ => hβ _ (mem_zip_of_getElem? h₁ h₂)) (fun _ _ _ h₁ h₂ => chains_paired hF₁ hF₂ hck hφ h₁ h₂)

theorem funcOps_agree (hvf : ValidResolvedFunction f) (hp : (x₁, x₂) ∈ funcOpPairs ctx₁ ctx₂ o₁ o₂) :
    OperationAgrees ctx₁ ctx₂ root φ ρ β x₁ x₂ := by
  obtain ⟨⟨d₁, d₂⟩, hd, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨k, hd₁, hd₂⟩ := zip_index hd
  obtain ⟨_, _, _, hT₁, hc₁, he₁⟩ := hF₁.tiles hd₁
  obtain ⟨_, _, _, hT₂, hc₂, he₂⟩ := hF₂.tiles hd₂
  have hf := block_agree (ρ := ρ) (FuncView.valuesAgree hF₁ hF₂ hck hβ hφ) hck hvf
    (fun _ _ _ h₁ h₂ => hβ _ (mem_zip_of_getElem? h₁ h₂)) hT₁ hT₂ (he₁ ▸ he₂ ▸ chains_paired hF₁ hF₂ hck hφ hd₁ hd₂)
  rw [← he₁, ← he₂] at hf
  have ⟨hm₁, hm₂⟩ := List.of_mem_zip hp
  refine (resolves_mem_zip hf hp).agrees fun _ => ?_
  rw [hc₁.opParent (by simpa using hm₁), hc₂.opParent (by simpa using hm₂)]
  simp [hβ _ hd]

omit hβ in
theorem body_agree (hρ : ρ (regOf ctx₁ o₁) = some (regOf ctx₂ o₂))
    (hd : (d₁, d₂) ∈ (bodyOf ctx₁ o₁).zip (bodyOf ctx₂ o₂)) : BlockAgrees ctx₁ ctx₂ φ ρ d₁ d₂ := by
  obtain ⟨k, hd₁, hd₂⟩ := zip_index hd
  obtain ⟨s, _, _, hT₁, hc₁, _⟩ := hF₁.tiles hd₁
  obtain ⟨_, _, _, hT₂, hc₂, _⟩ := hF₂.tiles hd₂
  have hm₁ := List.mem_of_getElem? hd₁; have hm₂ := List.mem_of_getElem? hd₂
  refine ⟨hc₁.blockInBounds, hc₂.blockInBounds, ?_, ?_, fun os hos => ?_⟩
  · by_cases hk : k = 0
    · subst k; rw [hF₁.entryTypes hd₁, hF₂.entryTypes hd₂]
    · rw [hF₁.blockTypes hk hd₁ hT₁.1, hF₂.blockTypes hk hd₂ hT₁.1]
  · rw [hF₁.2.1.opParent (by simpa using hm₁), hF₂.2.1.opParent (by simpa using hm₂)]; simp [hρ]
  · obtain rfl := BlockPtr.OpChain_unique hos hc₁
    exact ⟨_, resolves_mapM (chains_paired hF₁ hF₂ hck hφ hd₁ hd₂), hc₂⟩

omit hck hφ in
theorem funcRegion_agree (hφo : φ o₁ = some o₂) : RegionAgrees ctx₁ ctx₂ φ β (regOf ctx₁ o₁) (regOf ctx₂ o₂) := by
  have hc₁ := hF₁.2.1; have hc₂ := hF₂.2.1
  refine ⟨hc₁.inBounds, hc₂.inBounds, ?_, fun bs hbs => ?_⟩
  · rw [hF₁.1.singletonRegion_parent hc₁.inBounds, hF₂.1.singletonRegion_parent hc₂.inBounds]; simp [hφo]
  · obtain rfl := RegionPtr.BlockChain_unique hbs hc₁
    exact ⟨_, resolves_mapM (resolves_of_zip (by rw [hF₁.2.2.1, hF₂.2.2.1]) hβ), hc₂⟩

end Function

theorem func_fields (hF₁ : FuncView ctx₁ f o₁ values₁) (hF₂ : FuncView ctx₂ f o₂ values₂)
    (hρ : ρ (regOf ctx₁ o₁) = some (regOf ctx₂ o₂)) : Fields ctx₁ ctx₂ φ ρ β o₁ o₂ :=
  hF₁.1.fields hF₂.1 (by simp) (by simp [Array.mapM_eq_mapM_toList, hρ])

/-! ### Distinctness -/

/-- Operations inside function bodies are neither modules nor functions. -/
def Inner (ctx : WfIRContext OpCode) (o : OperationPtr) : Prop :=
  o.getOpType! ctx.raw ≠ ofDialect OpCode Builtin.module ∧ o.getOpType! ctx.raw ≠ ofDialect OpCode Llvm.func

theorem llvm_inner {code : Llvm} (h : o.getOpType! ctx.raw = ofDialect OpCode code) (hc : code ≠ .func) :
    Inner ctx o :=
  ⟨by simp [h, ofDialect, HasDialect.inject], fun e => hc (HasDialect.ofDialect_injective (h.symm.trans e))⟩

theorem MatchesOp.inner {code : Llvm} {props : propertiesOf code} (h : MatchesOp ctx o code ts vs rs props attrs)
    (hc : code ≠ .func) : Inner ctx o :=
  llvm_inner (by grind [MatchesOp]) hc

theorem MatchesTermOp.inner {code : Llvm} {props : propertiesOf code} (h : MatchesTermOp ctx o code vs ss props)
    (hc : code ≠ .func) : Inner ctx o :=
  llvm_inner (by grind [MatchesTermOp]) hc

theorem OperandTile.inner (h : OperandTile ctx values ty v x cs) : ∀ c ∈ cs, Inner ctx c := by
  cases v with
  | ref => obtain ⟨_, rfl⟩ := h; simp
  | intConst => cases ty; obtain ⟨c, rfl, _, hc⟩ := h; simpa using hc.inner (by decide)

theorem instTile_inner (h : LowersResolvedInstTile ctx values (inst, i) t) : ∀ o ∈ t, Inner ctx o := by
  rcases inst with ⟨opc, _, _, _⟩ | _
  · obtain ⟨_, _, _, _, _, rfl, hl, hr, _, hm⟩ := h
    simp only [List.mem_append, List.mem_singleton]
    rintro o ((ho | ho) | rfl)
    · exact hl.inner o ho
    · exact hr.inner o ho
    · exact hm.inner (by cases opc <;> decide)
  · cases h; simp

theorem argOps_inner {blocks : BlockMap} (h : LowersEdge ctx f blocks values src dst b args) :
    ∀ o ∈ argOps args, Inner ctx o := by
  obtain ⟨_, _, _, _, _, _, hr⟩ := h
  obtain ⟨_, _, ho⟩ := phiArgs_inputs hr
  intro o hm
  obtain ⟨arg, ha, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨⟨_, _⟩, hx⟩ := resolvesList_right_member ho ha
  exact hx.inner o hm

theorem termTile_inner {blocks : BlockMap} (h : LowersTerminatorTile ctx f blocks values src t tile) :
    ∀ o ∈ tile, Inner ctx o := by
  cases t with
  | ret =>
    obtain ⟨_, _, _, hx, hm, rfl⟩ := h
    simpa [or_imp, forall_and] using ⟨hx.inner, hm.inner (by decide)⟩
  | br =>
    obtain ⟨_, _, _, he, hm, rfl⟩ := h
    simpa [or_imp, forall_and] using ⟨argOps_inner he, hm.inner (by decide)⟩
  | condBr =>
    obtain ⟨_, _, _, _, _, _, _, hx, _, hy, hn, hm, rfl⟩ := h
    simp only [List.mem_append, List.mem_singleton]
    rintro o (((ho | ho) | ho) | rfl)
    · exact hx.inner o ho
    · exact argOps_inner hy o ho
    · exact argOps_inner hn o ho
    · exact hm.inner (by decide)

theorem BlockTiles.inner {blocks : BlockMap} (h : BlockTiles ctx f blocks values k src tiles term) :
    ∀ o ∈ tiles.flatten ++ term, Inner ctx o := by
  simp only [List.mem_append, List.mem_flatten]
  rintro o (⟨t, ht, ho⟩ | ho)
  · obtain ⟨⟨_, _⟩, hx⟩ := resolvesList_right_member h.2.1 ht; exact instTile_inner hx o ho
  · exact termTile_inner h.2.2 o ho

theorem blockChain_injective {c : IRContext OpCode} (h : RegionPtr.BlockChain r c bs) :
    ∀ (i j : Nat) hi hj, i ≠ j → bs[i]'hi ≠ bs[j]'hj := by
  intro i; induction i with
  | zero => grind [RegionPtr.BlockChain]
  | succ i ih => intro j; cases j <;> grind [RegionPtr.BlockChain]

theorem blockChain_nodup {c : IRContext OpCode} (h : RegionPtr.BlockChain r c bs) : bs.toList.Nodup := by
  simp only [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  grind [blockChain_injective h]

/-- The function owning an operation, through its block and region. -/
def owner (ctx : WfIRContext OpCode) (x : OperationPtr) : Option OperationPtr :=
  (x.getParent! ctx.raw).bind fun d => (d.getParent! ctx.raw).bind (·.getParent! ctx.raw)

theorem FuncView.funcOps (h : FuncView ctx f o values) :
    (funcOps ctx o).Nodup ∧ ∀ x ∈ funcOps ctx o, Inner ctx x ∧ owner ctx x = some o := by
  have hd d (hm : d ∈ bodyOf ctx o) : (opsOf ctx d).Nodup ∧ ∀ x ∈ opsOf ctx d,
      x.getParent! ctx.raw = some d ∧ Inner ctx x := by
    obtain ⟨_, hk⟩ := List.mem_iff_getElem?.mp hm; obtain ⟨_, _, _, hT, hc, he⟩ := h.tiles hk
    exact ⟨by simpa using BlockPtr.OpChain_array_toList_Nodup hc,
      fun x hx => ⟨hc.opParent (by simpa using hx), hT.inner x (he ▸ hx)⟩⟩
  refine ⟨nodup_flatMap_owner (·.getParent! ctx.raw) (by simpa using blockChain_nodup h.2.1)
    fun d hm => ⟨(hd d hm).1, fun x hx => ((hd d hm).2 x hx).1⟩, fun x hx => ?_⟩
  obtain ⟨d, hm, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨hp, hi⟩ := (hd d hm).2 x hx
  exact ⟨hi, by simp [owner, hp, h.2.1.opParent (by simpa using hm), h.1.singletonRegion_parent h.2.1.inBounds]⟩

theorem nodup_map_on {σ τ : Type} {l : List σ} {g : σ → τ} (h : ∀ x ∈ l, ∀ y ∈ l, g x = g y → x = y)
    (hn : l.Nodup) : (l.map g).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at *
    exact ⟨fun x hx he => hn.1 (h x (by simp [hx]) a (by simp) he ▸ hx),
      ih (fun x hx y hy => h x (by simp [hx]) y (by simp [hy])) hn.2⟩

theorem module_nodup (hm : MatchesOp ctx root Builtin.module #[] #[] #[r] default defaultModuleAttrs)
    (hr : r.BlockChain ctx.raw #[b]) (hb : b.OpChain ctx.raw fs.toArray) {fns : List ResolvedFunction} (hf : ResolvesList (LowersFunction ctx) fns fs) :
    (allOps ctx root fs).Nodup ∧ (allBlocks ctx b fs).Nodup ∧ (allRegions ctx r fs).Nodup := by
  have hv o (ho : o ∈ fs) : ∃ f values, FuncView ctx f o values := by
    obtain ⟨f, h⟩ := resolvesList_right_member hf ho; obtain ⟨v, hv⟩ := h.view; exact ⟨f, v, hv⟩
  have ht : root.getOpType! ctx.raw = ofDialect OpCode Builtin.module := (Prod.mk.inj hm.2.2).1
  have hfo o (ho : o ∈ fs) : o.getOpType! ctx.raw = ofDialect OpCode Llvm.func := by
    obtain ⟨_, _, h⟩ := hv o ho; exact (Prod.mk.inj h.1.2.2).1
  have hne o (ho : o ∈ fs) : o ≠ root := fun he => by
    have := hfo o ho; rw [he, ht] at this; simp [ofDialect, HasDialect.inject] at this
  have hreg o (ho : o ∈ fs) : (regOf ctx o).getParent! ctx.raw = some o := by
    obtain ⟨_, _, h⟩ := hv o ho; exact h.1.singletonRegion_parent h.2.1.inBounds
  have hrp : r.getParent! ctx.raw = some root := hm.singletonRegion_parent hr.inBounds
  have hn : fs.Nodup := by simpa using BlockPtr.OpChain_array_toList_Nodup hb
  refine ⟨List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨hn, ?_, ?_⟩⟩, List.nodup_cons.mpr ⟨?_, ?_⟩,
    List.nodup_cons.mpr ⟨?_, nodup_map_on (fun x hx y hy he =>
      Option.some.inj ((hreg x hx).symm.trans (he ▸ hreg y hy))) hn⟩⟩
  · simp only [List.mem_append, List.mem_flatMap, not_or, not_exists, not_and]
    refine ⟨fun h => hne _ h rfl, fun o ho h => ?_⟩
    obtain ⟨_, _, hF⟩ := hv o ho; exact (hF.funcOps.2 _ h).1.1 ht
  · exact nodup_flatMap_owner (owner ctx) hn fun o ho => by
      obtain ⟨_, _, hF⟩ := hv o ho; exact ⟨hF.funcOps.1, fun x hx => (hF.funcOps.2 x hx).2⟩
  · intro x hx y hy he; subst he
    obtain ⟨o, ho, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨_, _, hF⟩ := hv o ho; exact (hF.funcOps.2 _ hy).1.2 (hfo x hx)
  · simp only [List.mem_flatMap, not_exists, not_and]
    intro o ho hd
    obtain ⟨_, _, hF⟩ := hv o ho
    have := (hr.opParent (bl := b) (by simp)).symm.trans (hF.2.1.opParent (by simpa using hd))
    cases this; exact hne o ho (Option.some.inj ((hreg o ho).symm.trans hrp))
  · exact nodup_flatMap_owner (fun d => (d.getParent! ctx.raw).bind (·.getParent! ctx.raw)) hn fun o ho => by
      obtain ⟨_, _, hF⟩ := hv o ho
      exact ⟨by simpa using blockChain_nodup hF.2.1, fun d hd => by simp [hF.2.1.opParent (by simpa using hd), hreg o ho]⟩
  · simp only [List.mem_map, not_exists, not_and]
    intro o ho he; exact hne o ho (Option.some.inj ((hreg o ho).symm.trans (he ▸ hrp)))

/-! ### Modules -/

theorem func_pair {fns : List ResolvedFunction} (hf₁ : ResolvesList (LowersFunction ctx₁) fns fs₁)
    (hf₂ : ResolvesList (LowersFunction ctx₂) fns fs₂) (h : (o₁, o₂) ∈ fs₁.zip fs₂) :
    ∃ f v₁ v₂, FuncView ctx₁ f o₁ v₁ ∧ FuncView ctx₂ f o₂ v₂ ∧ checkBlocks f = .ok () ∧ ValidResolvedFunction f := by
  obtain ⟨f, h₁, h₂⟩ := resolves_zip_mem hf₁ hf₂ h
  obtain ⟨v₁, hv₁⟩ := h₁.view; obtain ⟨v₂, hv₂⟩ := h₂.view
  exact ⟨f, v₁, v₂, hv₁, hv₂, h₁.checkBlocks, h₁.1⟩

section Module

variable (hm₁ : MatchesOp ctx₁ root₁ Builtin.module #[] #[] #[r₁] default defaultModuleAttrs)
  (hm₂ : MatchesOp ctx₂ root₂ Builtin.module #[] #[] #[r₂] default defaultModuleAttrs)
  (hr₁ : r₁.BlockChain ctx₁.raw #[b₁]) (hr₂ : r₂.BlockChain ctx₂.raw #[b₂])
include hm₁ hm₂

theorem root_agree (hρ : ρ r₁ = some r₂) : OperationAgrees ctx₁ ctx₂ root₁ φ ρ β root₁ root₂ :=
  (hm₁.fields hm₂ (by simp) (by simp [Array.mapM_eq_mapM_toList, hρ])).agrees fun h => (h rfl).elim

include hr₁ hr₂

theorem moduleRegion_agree (hφ : φ root₁ = some root₂) (hβ : β b₁ = some b₂) :
    RegionAgrees ctx₁ ctx₂ φ β r₁ r₂ := by
  refine ⟨hr₁.inBounds, hr₂.inBounds, ?_, fun bs hbs => ?_⟩
  · simp [hm₁.singletonRegion_parent hr₁.inBounds, hm₂.singletonRegion_parent hr₂.inBounds, hφ]
  · obtain rfl := RegionPtr.BlockChain_unique hbs hr₁
    exact ⟨#[b₂], by simp [Array.mapM_eq_mapM_toList, hβ], hr₂⟩

omit hm₁ hm₂ in
theorem moduleBlock_agree (hb₁ : b₁.OpChain ctx₁.raw fs₁.toArray) (hb₂ : b₂.OpChain ctx₂.raw fs₂.toArray)
    (ha₁ : b₁.getArgumentTypes! ctx₁.raw = #[]) (ha₂ : b₂.getArgumentTypes! ctx₂.raw = #[])
    (hρ : ρ r₁ = some r₂) (hφ : ResolvesList (Paired φ) fs₁ fs₂) : BlockAgrees ctx₁ ctx₂ φ ρ b₁ b₂ := by
  refine ⟨hb₁.blockInBounds, hb₂.blockInBounds, ha₁.trans ha₂.symm, ?_, fun os hos => ?_⟩
  · simp [hr₁.opParent (bl := b₁) (by simp), hr₂.opParent (bl := b₂) (by simp), hρ]
  · obtain rfl := BlockPtr.OpChain_unique hos hb₁
    exact ⟨_, resolves_mapM hφ, hb₂⟩

end Module

theorem LowersModule.iso (h₁ : LowersModule ctx₁ m root₁) (h₂ : LowersModule ctx₂ m root₂) :
    RootedIso ctx₁ root₁ ctx₂ root₂ := by
  obtain ⟨r₁, b₁, fs₁, hm₁, hr₁, hb₁, ha₁, hf₁⟩ := h₁
  obtain ⟨r₂, b₂, fs₂, hm₂, hr₂, hb₂, ha₂, hf₂⟩ := h₂
  obtain ⟨no₁, nb₁, nr₁⟩ := module_nodup hm₁ hr₁ hb₁ hf₁
  obtain ⟨no₂, nb₂, nr₂⟩ := module_nodup hm₂ hr₂ hb₂ hf₂
  have hO := (opTable_fst ctx₁ ctx₂ (root₁ := root₁) (root₂ := root₂) (funcs₁ := fs₁) (funcs₂ := fs₂)).nodup no₁
  have hO' := (opTable_snd ctx₁ ctx₂ (root₁ := root₁) (root₂ := root₂) (funcs₁ := fs₁) (funcs₂ := fs₂)).nodup no₂
  have hB := (blockTable_fst ctx₁ ctx₂ (b₁ := b₁) (b₂ := b₂) (funcs₁ := fs₁) (funcs₂ := fs₂)).nodup nb₁
  have hB' := (blockTable_snd ctx₁ ctx₂ (b₁ := b₁) (b₂ := b₂) (funcs₁ := fs₁) (funcs₂ := fs₂)).nodup nb₂
  have hR := (regionTable_fst ctx₁ ctx₂ (r₁ := r₁) (r₂ := r₂) (funcs₁ := fs₁) (funcs₂ := fs₂)).nodup nr₁
  have hR' := (regionTable_snd ctx₁ ctx₂ (r₁ := r₁) (r₂ := r₂) (funcs₁ := fs₁) (funcs₂ := fs₂)).nodup nr₂
  have hl : fs₁.length = fs₂.length := (resolves_length hf₁).symm.trans (resolves_length hf₂)
  have hφf : ∀ p ∈ fs₁.zip fs₂, pairFun (opTable ctx₁ ctx₂ root₁ root₂ fs₁ fs₂) p.1 = some p.2 := fun p hp =>
    (pairFun_eq hO).mpr (by simp [opTable, hp])
  have hφi : ∀ q ∈ fs₁.zip fs₂, ∀ p ∈ funcOpPairs ctx₁ ctx₂ q.1 q.2,
      pairFun (opTable ctx₁ ctx₂ root₁ root₂ fs₁ fs₂) p.1 = some p.2 := fun q hq p hp =>
    (pairFun_eq hO).mpr (by simp only [opTable, List.mem_cons, List.mem_append, List.mem_flatMap]; exact .inr (.inr ⟨q, hq, hp⟩))
  have hβm : pairFun (blockTable ctx₁ ctx₂ b₁ b₂ fs₁ fs₂) b₁ = some b₂ := (pairFun_eq hB).mpr (by simp [blockTable])
  have hβi : ∀ q ∈ fs₁.zip fs₂, ∀ p ∈ (bodyOf ctx₁ q.1).zip (bodyOf ctx₂ q.2),
      pairFun (blockTable ctx₁ ctx₂ b₁ b₂ fs₁ fs₂) p.1 = some p.2 := fun q hq p hp =>
    (pairFun_eq hB).mpr (by simp only [blockTable, List.mem_cons, List.mem_flatMap]; exact .inr ⟨q, hq, hp⟩)
  have hρm : pairFun (regionTable ctx₁ ctx₂ r₁ r₂ fs₁ fs₂) r₁ = some r₂ := (pairFun_eq hR).mpr (by simp [regionTable])
  have hρi : ∀ q ∈ fs₁.zip fs₂, pairFun (regionTable ctx₁ ctx₂ r₁ r₂ fs₁ fs₂) (regOf ctx₁ q.1) = some (regOf ctx₂ q.2) :=
    fun q hq => (pairFun_eq hR).mpr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩))
  have hroot := (pairFun_eq hO).mpr (List.mem_cons_self (a := (root₁, root₂)))
  refine ⟨_, _, _, pairFun_injective hO hO', pairFun_injective hR hR', pairFun_injective hB hB', hroot, ?_, ?_, ?_⟩
  · intro o o' h
    rcases List.mem_cons.mp ((pairFun_eq hO).mp h) with he | h
    · cases he; exact root_agree hm₁ hm₂ hρm
    rcases List.mem_append.mp h with h | h
    · obtain ⟨_, _, _, hF₁, hF₂, _, _⟩ := func_pair hf₁ hf₂ h
      refine (func_fields hF₁ hF₂ (hρi _ h)).agrees fun _ => ?_
      have ⟨hm, hm'⟩ := List.of_mem_zip h
      simp [hb₁.opParent (by simpa using hm), hb₂.opParent (by simpa using hm'), hβm]
    · obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp h
      obtain ⟨_, _, _, hF₁, hF₂, hck, hvf⟩ := func_pair hf₁ hf₂ hq
      exact funcOps_agree hF₁ hF₂ hck (hβi q hq) (hφi q hq) hvf hp
  · intro s s' h
    rcases List.mem_cons.mp ((pairFun_eq hR).mp h) with he | h
    · cases he; exact moduleRegion_agree hm₁ hm₂ hr₁ hr₂ hroot hβm
    · obtain ⟨q, hq, he⟩ := List.mem_map.mp h; cases he
      obtain ⟨_, _, _, hF₁, hF₂, _, _⟩ := func_pair hf₁ hf₂ hq
      exact funcRegion_agree hF₁ hF₂ (hβi q hq) (hφf q hq)
  · intro z z' h
    rcases List.mem_cons.mp ((pairFun_eq hB).mp h) with he | h
    · cases he; exact moduleBlock_agree hr₁ hr₂ hb₁ hb₂ ha₁ ha₂ hρm (resolves_of_zip hl hφf)
    · obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp h
      obtain ⟨_, _, _, hF₁, hF₂, hck, _⟩ := func_pair hf₁ hf₂ hq
      exact body_agree hF₁ hF₂ hck (hφi q hq) (hρi q hq) hp

theorem lowerModule_correct : LowersModule ctx m root ↔
    ∃ ctx₂ root₂, lowerModule m = .ok (ctx₂, root₂) ∧
      equivalent_modulo_renaming ctx root ctx₂ root₂ :=
  lowerModule_correct_of_unique LowersModule.iso

end Veir.LLVMLowering
