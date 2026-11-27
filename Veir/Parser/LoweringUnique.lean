import Veir.Parser.LLVMLowering

/-! The lowering specification determines the rooted graph up to renaming. -/

namespace Veir.LLVMLowering

open LLVMParserProp NameResolutionSketch

namespace Unique

variable {α β γ δ : Type} {R : α → β → Prop}

/-! ### Lists -/

theorem resolves_length (h : ResolvesList R xs ys) : xs.length = ys.length := by
  induction h <;> simp_all

theorem resolves_getElem (h : ResolvesList R xs ys) (k : Nat) (hk : k < xs.length) :
    R xs[k] (ys[k]'(resolves_length h ▸ hk)) := by
  induction h generalizing k with
  | nil => simp at hk
  | cons _ _ ih => cases k <;> simp_all

theorem resolves_append (h : ResolvesList R a b) (h' : ResolvesList R c d) :
    ResolvesList R (a ++ c) (b ++ d) := by
  induction h <;> simp_all [ResolvesList.cons]

theorem resolves_of_zip {xs : List α} {ys : List β} (hl : xs.length = ys.length) (h : ∀ p ∈ xs.zip ys, R p.1 p.2) :
    ResolvesList R xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [ResolvesList.nil]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys => simp at hl h; exact .cons h.1 (ih hl fun p hp => h.2 _ _ hp)

theorem resolves_mem_zip {p : α × β} (h : ResolvesList R xs ys) (hp : p ∈ xs.zip ys) : R p.1 p.2 := by
  induction h <;> simp_all; grind

theorem resolves_mapM {f : α → Option β} (h : ResolvesList (fun a b => f a = some b) xs ys) :
    xs.toArray.mapM f = some ys.toArray := by
  induction h <;> simp_all

theorem nodup_keys {L : List (α × β)} (hn : (L.map Prod.fst).Nodup) (h : (a, b) ∈ L) (h' : (a, b') ∈ L) : b = b' := by
  induction L with
  | nil => simp at h
  | cons p L ih =>
    obtain ⟨hp, hn⟩ := List.nodup_cons.mp hn
    simp only [List.mem_cons] at h h'
    rcases h with rfl | h <;> rcases h' with h' | h'
    · cases h'; rfl
    all_goals grind

theorem zip_fst_sublist {xs : List α} {ys : List β} : ((xs.zip ys).map Prod.fst).Sublist xs := by
  induction xs generalizing ys <;> cases ys <;> simp_all

theorem zip_snd_sublist {xs : List α} {ys : List β} : ((xs.zip ys).map Prod.snd).Sublist ys := by
  induction xs generalizing ys <;> cases ys <;> simp_all

theorem flatMap_fst_sublist {xs : List α} {ys : List β} {f : α × β → List (γ × δ)} {g : α → List γ}
    (h : ∀ a b, ((f (a, b)).map Prod.fst).Sublist (g a)) :
    (((xs.zip ys).flatMap f).map Prod.fst).Sublist (xs.flatMap g) := by
  induction xs generalizing ys <;> cases ys <;> simp_all [List.Sublist.append]

theorem flatMap_snd_sublist {xs : List α} {ys : List β} {f : α × β → List (γ × δ)} {g : β → List δ}
    (h : ∀ a b, ((f (a, b)).map Prod.snd).Sublist (g b)) :
    (((xs.zip ys).flatMap f).map Prod.snd).Sublist (ys.flatMap g) := by
  induction xs generalizing ys <;> cases ys <;> simp_all [List.Sublist.append]

theorem nodup_flatMap_owner {xs : List α} {g : α → List β} (own : β → Option α) (hx : xs.Nodup)
    (hg : ∀ a ∈ xs, (g a).Nodup ∧ ∀ y ∈ g a, own y = some a) : (xs.flatMap g).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hx⟩ := List.nodup_cons.mp hx
    simp only [List.flatMap_cons, List.nodup_append, List.mem_flatMap]
    refine ⟨(hg a (by simp)).1, ih hx (fun b hb => hg b (by simp [hb])), ?_⟩
    rintro y hy _ ⟨b, hb, hy'⟩ rfl
    exact ha (Option.some.inj (((hg a (by simp)).2 y hy).symm.trans ((hg b (by simp [hb])).2 y hy')) ▸ hb)

/-! ### Tables -/

/-- The partial function described by a table. -/
noncomputable def pairFun (L : List (α × β)) (a : α) : Option β :=
  open Classical in if h : ∃ b, (a, b) ∈ L then some h.choose else none

theorem pairFun_eq {L : List (α × β)} (hn : (L.map Prod.fst).Nodup) : pairFun L a = some b ↔ (a, b) ∈ L := by
  unfold pairFun; split
  · rename_i h; exact ⟨fun he => Option.some.inj he ▸ h.choose_spec,
      fun hm => congrArg some (nodup_keys hn h.choose_spec hm)⟩
  · rename_i h; exact ⟨nofun, fun hm => (h ⟨b, hm⟩).elim⟩

theorem pairFun_injective {L : List (α × β)} (hn : (L.map Prod.fst).Nodup) (hn' : (L.map Prod.snd).Nodup) :
    PartialInjective (pairFun L) := fun a a' b h h' =>
  nodup_keys (L := L.map Prod.swap) (by simpa [Function.comp_def] using hn')
    (List.mem_map.mpr ⟨_, (pairFun_eq hn).mp h, rfl⟩) (List.mem_map.mpr ⟨_, (pairFun_eq hn).mp h', rfl⟩)

/-- The operations of a block, determined by its chain. -/
noncomputable def opsOf (ctx : WfIRContext OpCode) (b : BlockPtr) : List OperationPtr :=
  open Classical in if h : ∃ os, b.OpChain ctx.raw os then h.choose.toList else []

/-- The blocks of a region, determined by its chain. -/
noncomputable def blocksOf (ctx : WfIRContext OpCode) (r : RegionPtr) : List BlockPtr :=
  open Classical in if h : ∃ bs, r.BlockChain ctx.raw bs then h.choose.toList else []

theorem opsOf_eq (h : b.OpChain ctx.raw os) : opsOf ctx b = os.toList := by
  have he : ∃ os, b.OpChain ctx.raw os := ⟨os, h⟩
  simp [opsOf, he, BlockPtr.OpChain_unique he.choose_spec h]

theorem blocksOf_eq (h : r.BlockChain ctx.raw bs) : blocksOf ctx r = bs.toList := by
  have he : ∃ bs, r.BlockChain ctx.raw bs := ⟨bs, h⟩
  simp [blocksOf, he, RegionPtr.BlockChain_unique he.choose_spec h]

def regOf (ctx : WfIRContext OpCode) (o : OperationPtr) : RegionPtr := (o.getRegions! ctx.raw)[0]!

noncomputable def bodyOf (ctx : WfIRContext OpCode) (o : OperationPtr) : List BlockPtr :=
  blocksOf ctx (regOf ctx o)

noncomputable def funcOps (ctx : WfIRContext OpCode) (o : OperationPtr) : List OperationPtr :=
  (bodyOf ctx o).flatMap (opsOf ctx)

noncomputable def allOps (ctx : WfIRContext OpCode) (root : OperationPtr) (funcs : List OperationPtr) :=
  root :: (funcs ++ funcs.flatMap (funcOps ctx))

noncomputable def allBlocks (ctx : WfIRContext OpCode) (b : BlockPtr) (funcs : List OperationPtr) :=
  b :: funcs.flatMap (bodyOf ctx)

def allRegions (ctx : WfIRContext OpCode) (r : RegionPtr) (funcs : List OperationPtr) :=
  r :: funcs.map (regOf ctx)

section Table

variable (ctx₁ ctx₂ : WfIRContext OpCode)

noncomputable def funcOpPairs (o₁ o₂ : OperationPtr) : List (OperationPtr × OperationPtr) :=
  ((bodyOf ctx₁ o₁).zip (bodyOf ctx₂ o₂)).flatMap fun p => (opsOf ctx₁ p.1).zip (opsOf ctx₂ p.2)

noncomputable def opTable (root₁ root₂ : OperationPtr) (funcs₁ funcs₂ : List OperationPtr) :=
  (root₁, root₂) :: (funcs₁.zip funcs₂ ++ (funcs₁.zip funcs₂).flatMap fun p => funcOpPairs ctx₁ ctx₂ p.1 p.2)

noncomputable def blockTable (b₁ b₂ : BlockPtr) (funcs₁ funcs₂ : List OperationPtr) :=
  (b₁, b₂) :: (funcs₁.zip funcs₂).flatMap fun p => (bodyOf ctx₁ p.1).zip (bodyOf ctx₂ p.2)

def regionTable (r₁ r₂ : RegionPtr) (funcs₁ funcs₂ : List OperationPtr) :=
  (r₁, r₂) :: (funcs₁.zip funcs₂).map fun p => (regOf ctx₁ p.1, regOf ctx₂ p.2)

theorem funcOpPairs_fst : ((funcOpPairs ctx₁ ctx₂ o₁ o₂).map Prod.fst).Sublist (funcOps ctx₁ o₁) :=
  flatMap_fst_sublist fun _ _ => zip_fst_sublist

theorem funcOpPairs_snd : ((funcOpPairs ctx₁ ctx₂ o₁ o₂).map Prod.snd).Sublist (funcOps ctx₂ o₂) :=
  flatMap_snd_sublist fun _ _ => zip_snd_sublist

theorem opTable_fst : ((opTable ctx₁ ctx₂ root₁ root₂ funcs₁ funcs₂).map Prod.fst).Sublist
    (allOps ctx₁ root₁ funcs₁) := by
  simp only [opTable, allOps, List.map_cons, List.map_append]
  exact (zip_fst_sublist.append (flatMap_fst_sublist fun _ _ => funcOpPairs_fst ..)).cons_cons _

theorem opTable_snd : ((opTable ctx₁ ctx₂ root₁ root₂ funcs₁ funcs₂).map Prod.snd).Sublist
    (allOps ctx₂ root₂ funcs₂) := by
  simp only [opTable, allOps, List.map_cons, List.map_append]
  exact (zip_snd_sublist.append (flatMap_snd_sublist fun _ _ => funcOpPairs_snd ..)).cons_cons _

theorem blockTable_fst : ((blockTable ctx₁ ctx₂ b₁ b₂ funcs₁ funcs₂).map Prod.fst).Sublist
    (allBlocks ctx₁ b₁ funcs₁) :=
  (flatMap_fst_sublist fun _ _ => zip_fst_sublist).cons_cons _

theorem blockTable_snd : ((blockTable ctx₁ ctx₂ b₁ b₂ funcs₁ funcs₂).map Prod.snd).Sublist
    (allBlocks ctx₂ b₂ funcs₂) :=
  (flatMap_snd_sublist fun _ _ => zip_snd_sublist).cons_cons _

theorem regionTable_fst : ((regionTable ctx₁ ctx₂ r₁ r₂ funcs₁ funcs₂).map Prod.fst).Sublist
    (allRegions ctx₁ r₁ funcs₁) := by
  simpa [regionTable, allRegions, Function.comp_def] using
    (zip_fst_sublist (xs := funcs₁) (ys := funcs₂)).map (regOf ctx₁)

theorem regionTable_snd : ((regionTable ctx₁ ctx₂ r₁ r₂ funcs₁ funcs₂).map Prod.snd).Sublist
    (allRegions ctx₂ r₂ funcs₂) := by
  simpa [regionTable, allRegions, Function.comp_def] using
    (zip_snd_sublist (xs := funcs₁) (ys := funcs₂)).map (regOf ctx₂)

end Table

/-- Filtering with a predicate determines the retained list. -/
theorem FilterRel.eq_filter {xs ys : List α} {P : α → Prop} [DecidablePred P]
    (h : FilterRel (fun x y => x = y ∧ P x) xs ys) :
    ys = xs.filter (fun x => decide (P x)) := by
  induction h with
  | nil => rfl
  | keep hm _ ih => obtain ⟨rfl, hp⟩ := hm; simp [hp, ih]
  | @drop x xs ys hn _ ih =>
    have hp : ¬P x := fun h => hn ⟨x, rfl, h⟩
    simp [hp, ih]

/-- Source operands determine the number of operations materialised for them. -/
def operandWidth : ResolvedValue → Nat
  | .ref _ => 0
  | .intConst _ => 1

theorem OperandTile.length (h : OperandTile ctx values ty v ptr cs) : cs.length = operandWidth v := by
  cases v with
  | ref id => simp [h.2, operandWidth]
  | intConst n =>
    cases ty
    obtain ⟨_, rfl, _, _⟩ := h
    rfl

def instWidth : ResolvedInst → Nat
  | .bin (.bin _ _ l r) => operandWidth l + operandWidth r + 1
  | .phi .. => 0

theorem instTile_length (h : LowersResolvedInstTile ctx values (inst, i) tile) : tile.length = instWidth inst := by
  cases inst with
  | phi => simp [show tile = [] from h, instWidth]
  | bin b =>
    cases b
    obtain ⟨_, _, _, _, _, rfl, hl, hr, _⟩ := h
    simp [instWidth, OperandTile.length hl, OperandTile.length hr, Nat.add_assoc]

theorem instTiles_lengths {xs : List (ResolvedInst × Nat)}
    (h : ResolvesList (LowersResolvedInstTile ctx values) xs tiles) :
    tiles.map List.length = xs.map (fun x => instWidth x.1) := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp [instTile_length hr, ih]

theorem phiArgs_inputs {phis : List ResolvedInst} {args : List ArgTile}
    (h : ResolvesList (fun phi arg => PhiPassesArg ctx values src phi arg ∧
      phi.phiType.map lowerType = some (typeOf ctx.raw arg.1)) phis args) :
    ∃ inputs, ResolvesList (IncomingPhiArg src) phis inputs ∧
      ResolvesList (fun (ty, input) arg => OperandTile ctx values ty input arg.1 arg.2) inputs args := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | @cons phi arg phis args hfirst _ ih =>
    obtain ⟨inputs, hi, ho⟩ := ih
    cases phi with
    | bin => exact False.elim hfirst.1
    | phi ty incoming =>
      rcases arg with ⟨v, cs⟩
      obtain ⟨input, hmem, hl⟩ := hfirst.1
      exact ⟨(ty, input) :: inputs, .cons ⟨rfl, hmem⟩ hi, .cons hl ho⟩

theorem phiArgs_source {blocks : BlockMap}
    (h : LowersEdge ctx f blocks values src dst b args)
    (ha : ∀ target ty incoming, f.blocks[dst]? = some target → .phi ty incoming ∈ target.insts →
      PhiInputsAgree incoming) :
    ∃ target inputs, f.blocks[dst]? = some target ∧ selectPhiInputs src target.insts = some inputs ∧
      ResolvesList (fun (ty, input) arg => OperandTile ctx values ty input arg.1 arg.2) inputs args := by
  obtain ⟨_, _, target, phis, hs, hf, hr⟩ := h
  obtain ⟨inputs, hi, ho⟩ := phiArgs_inputs hr
  exact ⟨target, inputs, hs, selectPhiInputs_complete hf hi (ha target · · hs), ho⟩

theorem phiArgs_widths {inputs : List (LLType × ResolvedValue)} {args : List ArgTile}
    (h : ResolvesList (fun (ty, input) arg => OperandTile ctx values ty input arg.1 arg.2) inputs args) :
    args.map (fun x => x.2.length) = inputs.map (fun x => operandWidth x.2) := by
  induction h with
  | nil => rfl
  | @cons input arg _ _ ho _ ih =>
    rcases input with ⟨ty, v⟩
    simp [OperandTile.length ho, ih]

variable {f : ResolvedFunction}

theorem phiArgs_same_source {a₁ a₂ : List ArgTile} {blocks₁ blocks₂ : BlockMap}
    (h₁ : LowersEdge ctx₁ f blocks₁ values₁ src dst b₁ a₁)
    (h₂ : LowersEdge ctx₂ f blocks₂ values₂ src dst b₂ a₂)
    (ha : ∀ target ty incoming, f.blocks[dst]? = some target → .phi ty incoming ∈ target.insts →
      PhiInputsAgree incoming) :
    ∃ inputs,
      ResolvesList (fun (ty, input) arg => OperandTile ctx₁ values₁ ty input arg.1 arg.2) inputs a₁ ∧
      ResolvesList (fun (ty, input) arg => OperandTile ctx₂ values₂ ty input arg.1 arg.2) inputs a₂ := by
  obtain ⟨target, inputs, hs, hi, ho⟩ := phiArgs_source h₁ ha
  obtain ⟨target', inputs', hs', hi', ho'⟩ := phiArgs_source h₂ ha
  cases hs.symm.trans hs'
  cases hi.symm.trans hi'
  exact ⟨inputs, ho, ho'⟩

theorem argOps_equal_length {a₁ a₂ : List ArgTile} {blocks₁ blocks₂ : BlockMap}
    (h₁ : LowersEdge ctx₁ f blocks₁ values₁ src dst b₁ a₁)
    (h₂ : LowersEdge ctx₂ f blocks₂ values₂ src dst b₂ a₂)
    (ha : ∀ target ty incoming, f.blocks[dst]? = some target → .phi ty incoming ∈ target.insts →
      PhiInputsAgree incoming) :
    (argOps a₁).length = (argOps a₂).length := by
  obtain ⟨_, ho, ho'⟩ := phiArgs_same_source h₁ h₂ ha
  simpa [argOps, List.flatMap_def, Function.comp_def] using
    congrArg List.sum ((phiArgs_widths ho).trans (phiArgs_widths ho').symm)

/-- All phi operands on an edge are fixed by the source and edge's originating block. -/
theorem checkedPhiAgree {dst : BlockId} (h : checkBlocks f = .ok ()) {incoming : List (BlockId × ResolvedValue)}
    (hs : f.blocks[dst]? = some (target : ResolvedBlock)) (hp : .phi ty incoming ∈ target.insts) :
    PhiInputsAgree incoming :=
  ((checkBlocks_accepts_iff.mp h).2.2 target dst
    (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hs))).2 ty incoming hp |>.1

theorem termTiles_equal_length {blocks₁ blocks₂ : BlockMap} {t : ResolvedTerminator}
    (h₁ : LowersTerminatorTile ctx₁ f blocks₁ values₁ src t tile₁)
    (h₂ : LowersTerminatorTile ctx₂ f blocks₂ values₂ src t tile₂)
    (hck : checkBlocks f = .ok ()) : tile₁.length = tile₂.length := by
  have ha dst (target : ResolvedBlock) ty incoming hs hp := checkedPhiAgree hck (dst := dst) (target := target) (ty := ty) (incoming := incoming) hs hp
  cases t with
  | ret =>
    obtain ⟨_, _, _, hx, _, rfl⟩ := h₁
    obtain ⟨_, _, _, hx', _, rfl⟩ := h₂
    simp [OperandTile.length hx, OperandTile.length hx']
  | br dst =>
    obtain ⟨_, _, _, he, _, rfl⟩ := h₁
    obtain ⟨_, _, _, he', _, rfl⟩ := h₂
    simp [argOps_equal_length he he' (ha dst)]
  | condBr _ yes no =>
    obtain ⟨_, _, _, _, _, _, _, hc, _, hy, hn, _, rfl⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, hc', _, hy', hn', _, rfl⟩ := h₂
    simp [OperandTile.length hc, OperandTile.length hc', argOps_equal_length hy hy' (ha yes),
      argOps_equal_length hn hn' (ha no)]

theorem argumentTypes_from_arguments {ctx : IRContext OpCode} {b : BlockPtr} :
    b.getArgumentTypes! ctx = (b.getArguments! ctx).map (typeOf ctx) := by
  rw [BlockPtr.getArguments!, Array.map_map]
  apply Array.ext
  · simp [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!]
  · intro k hk hi
    rw [BlockPtr.getArgumentTypes!.getElem_eq_getArgument]
    · simp [typeOf]
    · simpa [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using hk

theorem phiTypes_filter {xs ys : List (ResolvedInst × Nat)}
    (h : FilterRel (fun x y => x = y ∧ x.1.phiType ≠ none) xs ys) :
    ys.filterMap (fun i => i.1.phiType.map lowerType) =
      xs.filterMap (fun i => i.1.phiType.map lowerType) := by
  induction h with
  | nil => rfl
  | keep hm _ ih => rw [← hm.1]; simp only [List.filterMap_cons, ih]
  | @drop x xs ys hn _ ih =>
    have hp : x.1.phiType = none := Classical.byContradiction (fun h => hn ⟨x, rfl, h⟩)
    simp [hp, ih]

theorem phiTypes_args {xs : List (ResolvedInst × Nat)} {args : List ValuePtr} {ctx : IRContext OpCode}
    (h : ResolvesList (fun i arg => i.1.phiType.map lowerType = some (typeOf ctx arg)) xs args) :
    args.map (typeOf ctx) = xs.filterMap (fun i => i.1.phiType.map lowerType) := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp [hr, ih]

theorem blockArgs_types {insts : List (ResolvedInst × Nat)} {ctx : IRContext OpCode}
    (h : LowersBlockArgs ctx values f dst insts b) :
    b.getArgumentTypes! ctx = (insts.filterMap (fun i => i.1.phiType.map lowerType)).toArray := by
  obtain ⟨phis, hf, hr⟩ := h
  rw [argumentTypes_from_arguments, ← Array.toList_inj]
  simp only [Array.toList_map]
  rw [← phiTypes_filter hf]
  apply phiTypes_args
  refine resolvesList_transfer hr fun ⟨inst, i⟩ arg _ h => ?_
  obtain ⟨ty, incoming, he, ht, _⟩ := h
  change inst = .phi ty incoming at he
  subst inst
  simp [ResolvedInst.phiType, ht]

theorem opChains_equal_length {blocks₁ blocks₂ : BlockMap} {b : ResolvedBlock}
    (hck : checkBlocks f = .ok ())
    (hi₁ : ResolvesList (LowersResolvedInstTile ctx₁ vals₁) (b.insts.zipIdx offset) insts₁)
    (hi₂ : ResolvesList (LowersResolvedInstTile ctx₂ vals₂) (b.insts.zipIdx offset) insts₂)
    (ht₁ : LowersTerminatorTile ctx₁ f blocks₁ vals₁ src b.terminator term₁)
    (ht₂ : LowersTerminatorTile ctx₂ f blocks₂ vals₂ src b.terminator term₂) :
    (insts₁.flatten ++ term₁).length = (insts₂.flatten ++ term₂).length := by
  simp only [List.length_append, List.length_flatten, instTiles_lengths hi₁, instTiles_lengths hi₂,
    termTiles_equal_length ht₁ ht₂ hck]

end Unique

end Veir.LLVMLowering
