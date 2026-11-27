import Veir.Parser.LoweringComplete

/-! Successful lowering satisfies the lowering specification. -/

namespace Veir.LLVMLowering

open LLVMParserProp NameResolutionSketch

namespace Sound
variable {ctx ctx' : WfIRContext OpCode} {f : ResolvedFunction}


theorem createRegion_raw (h : WfRewriter.createRegion ctx = some (ctx', region)) :
    Rewriter.createRegion ctx.raw = some (ctx'.raw, region) := by
  unfold WfRewriter.createRegion at h; split at h <;> grind (gen := 20) [OperationPtr.getProperties!]

theorem createRegion_frame (h : WfRewriter.createRegion ctx = some (ctx', region)) :
    LoweringFrame ctx ctx' [] [] [] := by
  have hr := createRegion_raw h
  have hn := WfRewriter.createRegion_new_not_inBounds h
  refine ⟨fun p hp => (WfRewriter.createRegion_genericPtr_mono (ptr := p) h).mpr (.inl hp),
    fun v hv => ?_, fun b hb => ?_, fun _ hm => ?_, fun _ hm => ?_, fun o ho _ => ?_,
    fun _ hc => BlockPtr.opChain_rewriter_createRegion hc hr, fun _ hc => ?_⟩
  · cases v <;> grind (gen := 20) [OperationPtr.getProperties!]
  · apply Array.ext <;> grind (gen := 20) [OperationPtr.getProperties!]
  · simp only [MatchesOp, Prod.mk.injEq] at hm ⊢; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind (gen := 20) [OperationPtr.getProperties!]
  · simp only [MatchesTermOp, Prod.mk.injEq] at hm ⊢; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind (gen := 20) [OperationPtr.getProperties!]
  · grind
  · apply RegionPtr.blockChain_unchanged hc <;> grind (gen := 20) [OperationPtr.getProperties!]

theorem createBlock_frame
    (h : WfRewriter.createBlock ctx ts (some (.atEnd r)) hi = some (ctx', b)) :
    LoweringFrame ctx ctx' [] [] [r] := by
  have hr := createBlock_raw h
  have hg := Complete.wfCreateBlock_spec h
  refine ⟨hg.1.bounds, fun v hv => ?_, hg.1.arguments, fun _ hm => hm.createBlock h, fun _ hm => ?_,
    fun o ho _ => ?_, fun _ hc => BlockPtr.opChain_rewriter_createBlock hc hr, fun {other bs} hn hc => ?_⟩
  all_goals unfold Rewriter.createBlock at hr
  all_goals simp only [Option.bind_eq_bind, Option.bind] at hr
  all_goals split at hr <;> try contradiction
  all_goals split at hr <;> try contradiction
  all_goals obtain ⟨rfl, rfl⟩ := (by simpa only [Option.some.injEq, Prod.mk.injEq] using hr : _ ∧ _)
  · cases v <;> grind (gen := 20) [OperationPtr.getProperties!]
  · simp only [MatchesTermOp, Prod.mk.injEq, OperationPtr.getSuccessors!_def] at hm ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals grind (gen := 20) [OperationPtr.getProperties!, OperationPtr.getSuccessor!_def]
  · grind
  · rename_i middle fresh halloc _ _ hinsert
    let before := Rewriter.initBlockArguments middle fresh ts
    have hbefore : other.BlockChain before bs := by
      dsimp [before]; apply RegionPtr.blockChain_unchanged hc <;> grind
    unfold Rewriter.insertBlock at hinsert
    change fresh.linkBetweenWithParent _ ((BlockInsertPoint.atEnd r).prev _ _) none r _ _ _ _ = _ at hinsert
    apply RegionPtr.blockChain_BlockPtr_linkBetweenWithParent_other hinsert _ (by simp) (by simpa [Ne, eq_comm] using hn) hbefore
    simp only [Option.maybe₁_def]
    intro prev hprev
    have hwf : before.WellFormed :=
      IRContext.wellFormed_Rewriter_initBlockArguments (BlockPtr.allocEmpty_wellFormed ctx.wellFormed halloc)
    exact RegionPtr.lastBlock!_parent! (reg := r) (ctx := before) (by dsimp [before]; grind) hwf
      (by rw [← BlockInsertPoint.prev!_atEnd, BlockInsertPoint.prev!_eq_prev]; exact hprev)

theorem blockChain_createBlock_atEnd
    (hc : r.BlockChain ctx.raw bs)
    (h : WfRewriter.createBlock ctx ts (some (.atEnd r)) hi = some (ctx', b)) :
    r.BlockChain ctx'.raw (bs.push b) := by
  have hr := createBlock_raw h
  unfold Rewriter.createBlock at hr
  simp only [Option.bind_eq_bind, Option.bind] at hr
  split at hr <;> try contradiction
  rename_i middle fresh halloc
  split at hr <;> try contradiction
  rename_i _ _ _ hinsert
  obtain ⟨rfl, rfl⟩ := (by simpa only [Option.some.injEq, Prod.mk.injEq] using hr : _ ∧ _)
  let before := Rewriter.initBlockArguments middle fresh ts
  have hbefore : r.BlockChain before bs := by
    dsimp [before]; apply RegionPtr.blockChain_unchanged hc <;> grind
  have hwf : before.WellFormed :=
    IRContext.wellFormed_Rewriter_initBlockArguments (BlockPtr.allocEmpty_wellFormed ctx.wellFormed halloc)
  unfold Rewriter.insertBlock at hinsert
  change fresh.linkBetweenWithParent before ((BlockInsertPoint.atEnd r).prev before _) none r _ _ _ _ = _ at hinsert
  have hchain := RegionPtr.blockChain_BlockPtr_linkBetweenWithParent_self hwf hinsert
    (.atEnd r) (by grind [RegionPtr.BlockChain.inBounds]) (by simp) (by simp) (by grind) hbefore
  have hlist := (RegionPtr.blockList_iff_RegionPtr_BlockChain (hctx := hwf) (hregion := hbefore.inBounds)).mp hbefore
  simpa only [BlockInsertPoint.idxIn_atEnd_eq, hlist, Array.insertIdx_size_self] using hchain

section Creation

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem wfCreateBlock_fresh
    (h : WfRewriter.createBlock ctx ts (some (.atEnd r)) hi = some (ctx', b)) :
    ¬b.InBounds ctx.raw := by
  have hr := createBlock_raw h
  unfold Rewriter.createBlock at hr
  simp only [Option.bind_eq_bind, Option.bind] at hr
  split at hr <;> try contradiction
  split at hr <;> try contradiction
  grind

theorem createBody_spec (h : (createBody ts).run ctx = .ok ((r, entry), ctx')) :
    LoweringFrame ctx ctx' [] [] [] ∧ r.BlockChain ctx'.raw #[entry] ∧ entry.OpChain ctx'.raw #[] ∧
      ¬r.InBounds ctx.raw ∧ ¬entry.InBounds ctx.raw := by
  simp [createBody] at h
  rcases hr : WfRewriter.createRegion ctx with _ | ⟨c, region⟩ <;> simp [hr] at h
  split at h <;> try simp at h
  rename_i hi
  rcases hb : WfRewriter.createBlock c ts (some (.atEnd region)) (by simpa using hi) with _ | ⟨d, b⟩ <;> simp [hb] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  have hraw := createRegion_raw hr
  have ⟨_, hchain, hentry, _, _⟩ := createBlock_spec hb (by grind) (by grind)
  have hn := WfRewriter.createRegion_new_not_inBounds hr
  have hf := createRegion_frame hr
  exact ⟨(hf.trans (createBlock_frame hb)).mono (by simp) (by simp) (by simpa using hn),
    hchain, hentry, hn, fun hi => wfCreateBlock_fresh hb (hf.bounds (.block _) hi)⟩

theorem createBlock_step (h : (createBlock r ts).run ctx = .ok (b, ctx'))
    (hc : r.BlockChain ctx.raw bs) :
    LoweringFrame ctx ctx' [] [] [r] ∧ r.BlockChain ctx'.raw (bs.push b) ∧ b.OpChain ctx'.raw #[] ∧ ¬b.InBounds ctx.raw := by
  simp [createBlock] at h
  split at h <;> try simp at h
  rename_i hi
  rcases hb : WfRewriter.createBlock ctx ts (some (.atEnd r)) (by simpa using hi) with _ | ⟨c, block⟩ <;> simp [hb] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨createBlock_frame hb, blockChain_createBlock_atEnd hc hb, BlockPtr.opChain_rewriter_createBlock_new (createBlock_raw hb), wfCreateBlock_fresh hb⟩

end Creation

theorem createBlocks_spec {xs : List α} (h : (xs.mapM (createBlock r ∘ types)).run ctx = .ok (blocks, ctx'))
    (hc : r.BlockChain ctx.raw bs) :
    LoweringFrame ctx ctx' [] [] [r] ∧ r.BlockChain ctx'.raw (bs ++ blocks.toArray) ∧
      ∀ block ∈ blocks, block.OpChain ctx'.raw #[] ∧ ¬block.InBounds ctx.raw := by
  induction xs generalizing blocks ctx bs with
  | nil => cases h; exact ⟨LoweringFrame.refl.mono (by simp) (by simp) (by simp), by simpa using hc, by simp⟩
  | cons x xs ih =>
    simp only [List.mapM_cons, lowerM_bind_ok, lowerM_pure_ok, Prod.mk.injEq] at h
    obtain ⟨b, c, hb, tail, d, ht, rfl, rfl⟩ := h
    obtain ⟨hf, hc, ho, hnew⟩ := createBlock_step hb hc
    obtain ⟨hg, hchain, hops⟩ := ih ht hc
    refine ⟨(hf.trans hg).mono (by simp) (by simp) (by simp), ?_,
      List.forall_mem_cons.mpr ⟨⟨hg.opChains (by simp) ho, hnew⟩,
        fun p hm => ⟨(hops p hm).1, fun hi => (hops p hm).2 (hf.bounds (.block p) hi)⟩⟩⟩
    have he : bs.push b ++ tail.toArray = bs ++ (b :: tail).toArray := by
      apply Array.toList_inj.mp
      simp only [Array.toList_append, Array.toList_push, List.append_assoc, List.singleton_append]
    exact he ▸ hchain

/-- Keep each binary instruction's original index when removing phis from a block. -/
def binaryEntries (insts : List ResolvedInst) (offset : Nat) : List (ResolvedBinary × Nat) :=
  (insts.zipIdx offset).filterMap fun (i, k) => i.binary.map (·, k)

theorem binaryEntries_insts (insts : List ResolvedInst) (offset : Nat) :
    (binaryEntries insts offset).map Prod.fst = insts.filterMap ResolvedInst.binary := by
  induction insts generalizing offset with
  | nil => rfl
  | cons i insts ih =>
    cases i with
    | bin inst =>
      change inst :: (binaryEntries insts (offset + 1)).map Prod.fst =
        inst :: insts.filterMap ResolvedInst.binary
      rw [ih]
    | phi => exact ih _

/-- Restore a tile for each source instruction, using empty tiles for the phis. -/
theorem expandInstTiles {insts : List ResolvedInst} {offset : Nat}
    (h : ResolvesList (fun (inst, i) tile => LowersInstTile ctx values (.inst i) inst tile)
      (binaryEntries insts offset) tiles) :
    ∃ allTiles, ResolvesList (LowersResolvedInstTile ctx values) (insts.zipIdx offset) allTiles ∧
      allTiles.flatten = tiles.flatten := by
  induction insts generalizing offset tiles with
  | nil => cases h; exact ⟨[], .nil, rfl⟩
  | cons i insts ih =>
    cases i with
    | bin inst =>
      change ResolvesList _ ((inst, offset) :: binaryEntries insts (offset + 1)) _ at h
      cases h with
      | cons head tail =>
        obtain ⟨all, ha, he⟩ := ih tail
        exact ⟨_ :: all, .cons head ha, by simp [he]⟩
    | phi ty incoming =>
      obtain ⟨all, ha, he⟩ := ih (offset := offset + 1) h
      exact ⟨[] :: all, .cons rfl ha, he⟩

theorem blockDefinitions_length {insts : List ResolvedInst}
    (h : ops.length = (insts.filterMap ResolvedInst.binary).length) :
    (blockDefinitions block arg insts ops).length = insts.length := by
  induction insts generalizing arg ops with
  | nil => rfl
  | cons inst insts ih =>
    cases inst with
    | phi =>
      simp only [List.filterMap_cons, ResolvedInst.binary] at h
      simp [blockDefinitions, ih h]
    | bin inst =>
      cases ops with
      | nil => simp [ResolvedInst.binary] at h
      | cons op ops =>
        simp only [List.filterMap_cons, ResolvedInst.binary, List.length_cons, Nat.add_right_cancel_iff] at h
        simp [blockDefinitions, ih h]

theorem blockDefinitions_binary {insts : List ResolvedInst} {j : Nat}
    (hlen : ops.length = (insts.filterMap ResolvedInst.binary).length)
    (h : ((binaryEntries insts offset).zip ops)[j]? = some ((inst, i), op)) :
    (blockDefinitions block arg insts ops)[i - offset]? = some (allocatedResult op) ∧ offset ≤ i := by
  induction insts generalizing offset ops arg j with
  | nil => simp [binaryEntries] at h
  | cons instr insts ih =>
    cases instr with
    | phi ty incoming =>
      change ((binaryEntries insts (offset + 1)).zip ops)[j]? = _ at h
      have ⟨hv, hi⟩ := ih (arg := arg + 1) hlen h
      have he : i - offset = (i - (offset + 1)) + 1 := by omega
      exact ⟨by simpa [blockDefinitions, he] using hv, by omega⟩
    | bin bin =>
      cases ops with
      | nil => simp at h
      | cons op' ops =>
        change (((bin, offset), op') :: (binaryEntries insts (offset + 1)).zip ops)[j]? = _ at h
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          simp [blockDefinitions, allocatedResult]
        | succ j =>
          simp only [List.getElem?_cons_succ] at h
          have ⟨hv, hi⟩ := ih (arg := arg) (by simpa [ResolvedInst.binary] using hlen) h
          have he : i - offset = (i - (offset + 1)) + 1 := by omega
          exact ⟨by simpa [blockDefinitions, he] using hv, by omega⟩

theorem framePhiPassesArg {phi : ResolvedInst} {arg : ArgTile}
    (h : PhiPassesArg ctx values src phi arg)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hw : ∀ op ∈ arg.2, op ∉ ws) :
    PhiPassesArg ctx' values src phi arg := by
  cases phi with
  | bin => exact h
  | phi =>
    obtain ⟨input, hi, ho⟩ := h
    exact ⟨input, hi, ho.frame_avoiding hf hw⟩

theorem frameEdge {blocks : BlockMap}
    (h : LowersEdge ctx f blocks values src dst b args)
    (hf : LoweringFrame ctx ctx' ws ins ex)
    (hw : ∀ op ∈ argOps args, op ∉ ws)
    (hv : ∀ v ∈ argPtrs args, v.InBounds ctx.raw) :
    LowersEdge ctx' f blocks values src dst b args := by
  obtain ⟨hn, hb, block, phis, he, hp, ha⟩ := h
  refine ⟨hn, hb, block, phis, he, hp, resolvesList_transfer ha fun phi arg hm h => ?_⟩
  have hb := hv arg.1 (by simpa [argPtrs] using List.mem_map_of_mem (f := Prod.fst) hm)
  refine ⟨framePhiPassesArg h.1 hf (fun o ho => hw _ (List.mem_flatMap.mpr ⟨arg, hm, ho⟩)), ?_⟩
  simpa [typeOf, hf.valueTypes arg.1 hb] using h.2

theorem MatchesTermOp.operands_inBounds {code : Llvm} {props : propertiesOf code}
    (h : MatchesTermOp ctx op code args bs props) : ∀ v ∈ args, v.InBounds ctx.raw := by
  have he : op.getOperands! ctx.raw = args := by grind [MatchesTermOp]
  exact he ▸ fun v hv => OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds h.1 hv

theorem frameTerminator {blocks : BlockMap} {term : ResolvedTerminator}
    (h : LowersTerminatorTile ctx f blocks values src term tile)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hw : ∀ op ∈ tile, op ∉ ws) :
    LowersTerminatorTile ctx' f blocks values src term tile := by
  cases term with
  | ret =>
    obtain ⟨v, cs, op, hv, ho, rfl⟩ := h
    exact ⟨v, cs, op, hv.frame_avoiding hf (fun _ hm => hw _ (by simp [hm])),
      hf.terminators (hw _ (by simp)) ho, rfl⟩
  | br =>
    obtain ⟨b, args, op, he, ho, rfl⟩ := h
    exact ⟨b, args, op, frameEdge he hf (fun _ hm => hw _ (by simp [hm])) (MatchesTermOp.operands_inBounds ho),
      hf.terminators (hw _ (by simp)) ho, rfl⟩
  | condBr =>
    obtain ⟨v, cs, y, n, ys, ns, op, hv, ht, hy, hn, ho, rfl⟩ := h
    have hin := MatchesTermOp.operands_inBounds ho
    exact ⟨v, cs, y, n, ys, ns, op, hv.frame_avoiding hf (fun _ hm => hw _ (by simp [hm])),
      (hf.valueTypes v (hin v (by simp))).trans ht,
      frameEdge hy hf (fun _ hm => hw _ (by simp [hm])) (fun v hm => hin v (by simp [hm])),
      frameEdge hn hf (fun _ hm => hw _ (by simp [hm])) (fun v hm => hin v (by simp [hm])),
      hf.terminators (hw _ (by simp)) ho, rfl⟩

theorem frameInstTiles {insts : List (ResolvedInst × Nat)}
    (h : ResolvesList (LowersResolvedInstTile ctx values) insts tiles)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hw : ∀ op ∈ tiles.flatten, op ∉ ws) :
    ResolvesList (LowersResolvedInstTile ctx' values) insts tiles := by
  refine resolvesList_transfer h fun ⟨inst, _⟩ tile hm h => ?_
  cases inst with
  | phi => exact h
  | bin => exact LowersInstTile.frame_avoiding h hf fun o ho => hw o (List.mem_flatten.mpr ⟨tile, hm, ho⟩)

theorem lowerM_forIn_unit {xs : List α} (act : α → LowerM Unit) :
    forIn xs () (fun x _ => act x >>= fun _ => pure (.yield ())) = xs.forM act := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, List.forM_eq_forM, List.forM_cons]
    simp only [bind_assoc, pure_bind, ih, List.forM_eq_forM]

theorem resolvesWithZip {xs : List α} {ys : List β} {R S : α → β → Prop}
    (h : ResolvesList R xs ys) (hz : ∀ x y, (x, y) ∈ xs.zip ys → S x y) :
    ResolvesList (fun x y => R x y ∧ S x y) xs ys := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih =>
    exact .cons ⟨hr, hz _ _ List.mem_cons_self⟩ (ih fun x y hm => hz x y (List.mem_cons_of_mem _ hm))

/-- The operations of a block, including the constants materialised for its terminator. -/
def LowersBlockCode (ctx : WfIRContext OpCode) (f : ResolvedFunction) (blocks : BlockMap)
    (values : ValueMap) (src offset : Nat) (b : ResolvedBlock) (block : BlockPtr) : Prop :=
  ∃ tiles term,
    ResolvesList (LowersResolvedInstTile ctx values) (b.insts.zipIdx offset) tiles ∧
    LowersTerminatorTile ctx f blocks values src b.terminator term ∧
    block.OpChain ctx.raw (tiles.flatten ++ term).toArray

theorem LowersBlockCode.frame {blocks : BlockMap}
    (h : LowersBlockCode ctx f blocks values src offset b block)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hb : block ∉ ins)
    (hd : ∀ op ∈ ws, op.getParent! ctx.raw = none) :
    LowersBlockCode ctx' f blocks values src offset b block := by
  obtain ⟨tiles, term, ht, hl, hc⟩ := h
  have ho o (hm : o ∈ tiles.flatten ++ term) : o ∉ ws :=
    fun h => not_mem_ops_of_detached hc (hd o h) (List.mem_toArray.mpr hm)
  exact ⟨tiles, term, frameInstTiles ht hf (fun o hm => ho o (List.mem_append_left _ hm)),
    frameTerminator hl hf (fun o hm => ho o (List.mem_append_right _ hm)), hf.opChains hb hc⟩

theorem wireBlock_spec {blocks : Array BlockPtr} {b : ResolvedBlock}
    (h : (do
      ((b.insts.filterMap ResolvedInst.binary).zip ops).forM (wireBinary (lookupValue values) block)
      lowerTerminator f blocks (lookupValue values) block src b.terminator : LowerM Unit).run ctx = .ok ((), ctx'))
    (ha : ResolvesList (BinaryAllocated ctx) (b.insts.filterMap ResolvedInst.binary) ops)
    (hkeys : ∀ p ∈ (binaryEntries b.insts offset).zip ops, values (.inst p.1.2) = some (allocatedResult p.2))
    (hn : ops.Nodup) (hc : block.OpChain ctx.raw #[])
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (hd : ∀ dst ∈ b.terminator.successors, dst ≠ 0) :
    LoweringFrame ctx ctx' ops [block] [] ∧
      LowersBlockCode ctx' f (fun i => blocks[i]?) values src offset b block := by
  obtain ⟨⟨⟩, c, hw, ht⟩ := lowerM_bind_ok.mp h
  rw [← binaryEntries_insts b.insts offset] at ha hw
  obtain ⟨hf, tiles, htiles, hc⟩ := wireBinaryList_spec ValueId.inst hw
    (resolvesWithZip (Complete.resolvesList_of_map ha) fun x y hm => hkeys (x, y) hm) hn hc hv
  obtain ⟨hg, term, hterm, hchain⟩ := lowerTerminator_spec ht hd hc (fun id v h => hf.bounds (.value v) (hv id v h))
  obtain ⟨all, hall, he⟩ := expandInstTiles htiles
  refine ⟨(hf.trans hg).mono (by simp; exact fun _ h => .inl h) (by simp) (by simp),
    all, term, frameInstTiles hall hg (by simp), hterm, ?_⟩
  rw [Array.empty_append] at hchain
  rw [he, ← List.append_toArray]; exact hchain

/-- A block's position and flattened instruction offset in the source function. -/
structure IndexedBlock where
  source : ResolvedBlock
  target : BlockPtr
  index : Nat
  offset : Nat

def indexBlocks : List (ResolvedBlock × BlockPtr) → Nat → Nat → List IndexedBlock
  | [], _, _ => []
  | (b, block) :: body, index, offset =>
    ⟨b, block, index, offset⟩ :: indexBlocks body (index + 1) (offset + b.insts.length)

def IndexedBlock.plan (row : IndexedBlock) : BlockLoweringPlan (BlockId × ResolvedTerminator) :=
  ⟨row.target, row.source.insts.filterMap ResolvedInst.binary, (row.index, row.source.terminator)⟩

theorem indexBlocks_plans (body : List (ResolvedBlock × BlockPtr)) (index offset : Nat) :
    (indexBlocks body index offset).map IndexedBlock.plan =
      (body.zipIdx index).map fun ((b, block), i) =>
        ⟨block, b.insts.filterMap ResolvedInst.binary, (i, b.terminator)⟩ := by
  induction body generalizing index offset with
  | nil => rfl
  | cons pair body ih => obtain ⟨b, block⟩ := pair; simp [indexBlocks, IndexedBlock.plan, List.zipIdx_cons, ih]

theorem indexBlocks_targets (body : List (ResolvedBlock × BlockPtr)) (index offset : Nat) :
    (indexBlocks body index offset).map IndexedBlock.target = body.map Prod.snd := by
  induction body generalizing index offset with
  | nil => rfl
  | cons pair body ih => obtain ⟨b, block⟩ := pair; simp [indexBlocks, ih]

def wireRow (f : ResolvedFunction) (blocks : Array BlockPtr) (values : ValueMap)
    (entry : IndexedBlock × List OperationPtr) : LowerM Unit := do
  let (row, ops) := entry
  ((row.source.insts.filterMap ResolvedInst.binary).zip ops).forM (wireBinary (lookupValue values) row.target)
  lowerTerminator f blocks (lookupValue values) row.target row.index row.source.terminator

def RowAllocated (ctx : WfIRContext OpCode) (values : ValueMap) (row : IndexedBlock)
    (ops : List OperationPtr) : Prop :=
  ResolvesList (BinaryAllocated ctx) (row.source.insts.filterMap ResolvedInst.binary) ops ∧
  ∀ p ∈ (binaryEntries row.source.insts row.offset).zip ops, values (.inst p.1.2) = some (allocatedResult p.2)

theorem allocRows_frame (h : ResolvesList (RowAllocated ctx values) rows groups)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hw : ∀ o ∈ groups.flatten, o ∉ ws) :
    ResolvesList (RowAllocated ctx' values) rows groups := by
  refine resolvesList_transfer h fun row ops hm ⟨ha, hk⟩ => ⟨?_, hk⟩
  exact resolvesList_transfer ha fun _ op ho h => h.frame hf (hw op (List.mem_flatten.mpr ⟨ops, hm, ho⟩))

theorem allocRows_detached (h : ResolvesList (RowAllocated ctx values) rows groups)
    (hm : op ∈ groups.flatten) : op.getParent! ctx.raw = none := by
  obtain ⟨ops, hm, ho⟩ := List.mem_flatten.mp hm
  obtain ⟨_, hr⟩ := resolvesList_right_member h hm
  obtain ⟨inst, hi⟩ := resolvesList_right_member hr.1 ho
  cases inst; exact hi.2

theorem wireRows_spec {blocks : Array BlockPtr} {rows : List IndexedBlock}
    (h : ((rows.zip groups).forM (wireRow f blocks values)).run ctx = .ok ((), ctx'))
    (ha : ResolvesList (RowAllocated ctx values) rows groups)
    (hop : groups.flatten.Nodup) (hblocks : (rows.map IndexedBlock.target).Nodup)
    (hempty : ∀ row ∈ rows, row.target.OpChain ctx.raw #[])
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (hd : ∀ row ∈ rows, ∀ dst ∈ row.source.terminator.successors, dst ≠ 0) :
    LoweringFrame ctx ctx' groups.flatten (rows.map IndexedBlock.target) [] ∧
      ∀ row ∈ rows, LowersBlockCode ctx' f (fun i => blocks[i]?) values
        row.index row.offset row.source row.target := by
  induction rows generalizing ctx ctx' groups with
  | nil => cases ha; cases h; exact ⟨LoweringFrame.refl, by simp⟩
  | cons row rows ih =>
    cases ha
    rename_i ops groups hr ha
    simp only [List.zip_cons_cons, List.forM_eq_forM, List.forM_cons, lowerM_bind_ok] at h
    obtain ⟨_, c, hw, ht⟩ := h
    have ⟨hn, htail, hdisj⟩ := List.nodup_append.mp (show (ops ++ groups.flatten).Nodup from hop)
    have ⟨hnew, hblocks⟩ := List.nodup_cons.mp hblocks
    obtain ⟨hf, hrow⟩ := wireBlock_spec hw hr.1 hr.2 hn (hempty _ List.mem_cons_self) hv (hd _ List.mem_cons_self)
    have ha' := allocRows_frame ha hf (fun op hm ho => hdisj op ho op hm rfl)
    have hkeep r (hm : r ∈ rows) : r.target ∉ [row.target] :=
      fun he => hnew ((List.mem_singleton.mp he) ▸ List.mem_map_of_mem hm)
    obtain ⟨hg, hrows⟩ := ih ht ha' htail hblocks (fun r hm => hf.opChains (hkeep r hm) (hempty _ (List.mem_cons_of_mem _ hm)))
      (fun i v h => hf.bounds (.value v) (hv i v h)) (fun r hm => hd _ (List.mem_cons_of_mem _ hm))
    refine ⟨(hf.trans hg).mono (fun _ h => .inl h) (fun _ h => .inl h) (by simp), ?_⟩
    exact List.forall_mem_cons.mpr ⟨hrow.frame hg hnew (fun _ => allocRows_detached ha'), hrows⟩

def instructionResults (body : List (ResolvedBlock × BlockPtr)) (groups : List (List OperationPtr)) :
    List ValuePtr :=
  (body.zip groups).flatMap fun ((b, block), ops) => blockDefinitions block 0 b.insts ops

theorem indexedBlock_results
    (hlen : ResolvesList (fun (p : ResolvedBlock × BlockPtr) (ops : List OperationPtr) =>
      ops.length = (p.1.insts.filterMap ResolvedInst.binary).length) body groups)
    (hrow : (row, ops) ∈ (indexBlocks body start offset).zip groups)
    (hvalue : (blockDefinitions row.target 0 row.source.insts ops)[i]? = some v) :
    (instructionResults body groups)[(row.offset + i) - offset]? = some v ∧ offset ≤ row.offset := by
  induction hlen generalizing start offset with
  | nil => simp [indexBlocks] at hrow
  | @cons p head body groups hhead htail ih =>
    rcases p with ⟨b, block⟩
    simp only [indexBlocks, List.zip_cons_cons, List.mem_cons] at hrow
    rcases hrow with he | hm
    · cases he
      simp only [instructionResults, List.zip_cons_cons, List.flatMap_cons, Nat.add_sub_cancel_left]
      exact ⟨(List.getElem?_append_left (List.getElem?_eq_some_iff.mp hvalue).1).trans hvalue, Nat.le_refl _⟩
    · obtain ⟨hv, ho⟩ := ih hm
      have hlen := blockDefinitions_length (block := block) (arg := 0) hhead
      change (blockDefinitions block 0 b.insts head).length = b.insts.length at hlen
      simp only [instructionResults, List.zip_cons_cons, List.flatMap_cons]
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      have he : row.offset + i - offset - b.insts.length =
          row.offset + i - (offset + b.insts.length) := by omega
      exact ⟨he.symm ▸ hv, by omega⟩

theorem indexedBlock_keys {row : IndexedBlock}
    (hlen : ResolvesList (fun (p : ResolvedBlock × BlockPtr) (ops : List OperationPtr) =>
      ops.length = (p.1.insts.filterMap ResolvedInst.binary).length) body groups)
    (hrow : (row, ops) ∈ (indexBlocks body 0 0).zip groups)
    (he : ops.length = (row.source.insts.filterMap ResolvedInst.binary).length)
    (hp : p ∈ (binaryEntries row.source.insts row.offset).zip ops) :
    functionValues f entry body groups (.inst p.1.2) = some (allocatedResult p.2) := by
  obtain ⟨k, hk, helem⟩ := List.mem_iff_getElem.mp hp
  have ⟨hv, ho⟩ := blockDefinitions_binary (block := row.target) (arg := 0) he
    (List.getElem?_eq_some_iff.mpr ⟨hk, helem⟩)
  have h := (indexedBlock_results (i := p.1.2 - row.offset) hlen hrow hv).1
  change row.offset ≤ p.1.2 at ho
  rw [Nat.sub_zero, Nat.add_sub_of_le ho] at h
  simpa [functionValues, instructionResults] using h

theorem resolveMapLeft {R : α → β → Prop} {g : γ → α}
    (h : ResolvesList (fun x y => R (g x) y) xs ys) :
    ResolvesList R (xs.map g) ys := by induction h <;> constructor <;> assumption

theorem indexBlocks_pairs (body : List (ResolvedBlock × BlockPtr)) (index offset : Nat) :
    (indexBlocks body index offset).map (fun row => (row.source, row.target)) = body := by
  induction body generalizing index offset with
  | nil => rfl
  | cons pair body ih => obtain ⟨b, block⟩ := pair; simp [indexBlocks, ih]

theorem indexBlocks_getElem? {body : List (ResolvedBlock × BlockPtr)} :
    (indexBlocks body start offset)[k]? = some row ↔
      body[k]? = some (row.source, row.target) ∧ row.index = start + k ∧
      row.offset = offset + ((body.take k).map fun p => p.1.insts.length).sum := by
  induction body generalizing start offset k with
  | nil => simp [indexBlocks]
  | cons pair body ih =>
    obtain ⟨b, block⟩ := pair
    cases k <;> simp_all [indexBlocks, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] <;> cases row <;> grind

theorem resolvePlanRows {body : List (ResolvedBlock × BlockPtr)}
    (ha : ResolvesList (fun p ops => ResolvesList (BinaryAllocated ctx) p.insts ops)
      ((indexBlocks body 0 0).map IndexedBlock.plan) groups) :
    ResolvesList (RowAllocated ctx (functionValues f entry body groups)) (indexBlocks body 0 0) groups := by
  have hrows := Complete.resolvesList_of_map ha
  have hl : ResolvesList (fun (row : IndexedBlock) ops =>
      ops.length = (row.source.insts.filterMap ResolvedInst.binary).length) (indexBlocks body 0 0) groups :=
    resolvesList_transfer hrows fun _ _ _ h => (Complete.resolvesList_lookup h).1.symm
  have hlen := resolveMapLeft (g := fun row : IndexedBlock => (row.source, row.target))
    (R := fun pair (ops : List OperationPtr) => ops.length = (pair.1.insts.filterMap ResolvedInst.binary).length) hl
  rw [indexBlocks_pairs] at hlen
  have h := resolvesWithZip hrows (S := fun row ops =>
    ∀ p ∈ (binaryEntries row.source.insts row.offset).zip ops,
      functionValues f entry body groups (.inst p.1.2) = some (allocatedResult p.2))
      (fun row ops hrow _ hm => indexedBlock_keys hlen hrow
        ((Complete.resolvesList_lookup ((Complete.resolvesList_zip hrows).1 _ hrow)).1.symm) hm)
  exact h

theorem wirePlans_eq {body : List (ResolvedBlock × BlockPtr)} {blocks : Array BlockPtr}
    {groups : List (List OperationPtr)} :
    (forIn (((indexBlocks body 0 0).map IndexedBlock.plan).zip groups) () fun x _ => do
      (x.1.insts.zip x.2).forM (wireBinary (lookupValue values) x.1.block)
      lowerTerminator f blocks (lookupValue values) x.1.block x.1.terminator.1 x.1.terminator.2
      pure (.yield ())) =
      ((indexBlocks body 0 0).zip groups).forM (wireRow f blocks values) := by
  rw [List.zip_map_left, List.forIn_map]
  let act := wireRow f blocks values
  have he : (fun (x : IndexedBlock × List OperationPtr) (_ : Unit) => do
      let p := (Prod.map IndexedBlock.plan id x).1
      let ops := (Prod.map IndexedBlock.plan id x).2
      (p.insts.zip ops).forM (wireBinary (lookupValue values) p.block)
      lowerTerminator f blocks (lookupValue values) p.block p.terminator.1 p.terminator.2
      pure (ForInStep.yield ())) = (fun x _ => act x >>= fun _ => pure (ForInStep.yield ())) := by
    funext x u; rcases x with ⟨_, _⟩; simp [act, wireRow, IndexedBlock.plan]
  rw [he, lowerM_forIn_unit]

def functionRows (f : ResolvedFunction) (blocks : Array BlockPtr) : List IndexedBlock :=
  indexBlocks (f.blocks.toList.zip blocks.toList) 0 0

theorem functionRows_targets {blocks : Array BlockPtr} (hs : blocks.size = f.blocks.size) :
    (functionRows f blocks).map IndexedBlock.target = blocks.toList := by
  simp [functionRows, indexBlocks_targets, List.map_snd_zip, hs]

theorem functionRows_get {blocks : Array BlockPtr} :
    (functionRows f blocks)[k]? = some row ↔
      f.blocks[k]? = some row.source ∧ blocks[k]? = some row.target ∧ row.index = k ∧
      row.offset = ((f.blocks.toList.take k).map (·.insts.length)).sum := by
  have hoff (h : f.blocks[k]? = some row.source) (hb : blocks[k]? = some row.target) :
      (((f.blocks.toList.zip blocks.toList).take k).map fun p => p.1.insts.length).sum =
        ((f.blocks.toList.take k).map (·.insts.length)).sum := by
    simp only [List.zip_eq_zipWith, List.take_zipWith]; rw [← List.zip_eq_zipWith]
    congr 1
    change List.map ((fun b : ResolvedBlock => b.insts.length) ∘ Prod.fst) _ = _
    rw [← List.map_map, List.map_fst_zip]
    simp [Nat.le_of_lt (Array.getElem?_eq_some_iff.mp h).1, Nat.le_of_lt (Array.getElem?_eq_some_iff.mp hb).1]
  simp only [functionRows, indexBlocks_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList, Nat.zero_add]
  exact ⟨fun ⟨⟨h, hb⟩, hi, ho⟩ => ⟨h, hb, hi, ho.trans (hoff h hb)⟩,
    fun ⟨h, hb, hi, ho⟩ => ⟨⟨h, hb⟩, hi, ho.trans (hoff h hb).symm⟩⟩

theorem lowerBlocks_body_spec {blocks : Array BlockPtr} {region : RegionPtr}
    (h : (lowerBlocks (Complete.plansOf f blocks)
      (fun groups => lookupValue (functionValues f entry (f.blocks.toList.zip blocks.toList) groups))
      fun values p => lowerTerminator f blocks values p.block p.terminator.1 p.terminator.2).run ctx = .ok ((), ctx'))
    (hc : Complete.Created ctx f entry blocks) (hck : checkBlocks f = .ok ())
    (hchain : region.BlockChain ctx.raw blocks)
    (he : ∀ b ∈ blocks, b.OpChain ctx.raw #[]) :
    LoweringFrame ctx ctx' [] blocks.toList [] ∧ ∃ groups,
      ResolvesList (fun (p : ResolvedBlock × BlockPtr) ops => ops.length =
        (p.1.insts.filterMap ResolvedInst.binary).length) (f.blocks.toList.zip blocks.toList) groups ∧
      ∀ row ∈ functionRows f blocks, LowersBlockCode ctx' f (fun i => blocks[i]?)
        (functionValues f entry (f.blocks.toList.zip blocks.toList) groups)
        row.index row.offset row.source row.target := by
  simp only [lowerBlocks, lowerM_bind_ok, lowerM_pure_ok, Prod.mk.injEq] at h
  obtain ⟨groups, c, ha, ⟨⟩, d, hw, _, rfl⟩ := h
  obtain ⟨hf, halloc, hop, hfresh⟩ := Complete.allocGroups_spec ha
  obtain ⟨hv, _⟩ := Complete.allocatedValues (hc.frame hf) hck halloc
  have hp : (functionRows f blocks).map IndexedBlock.plan = Complete.plansOf f blocks :=
    indexBlocks_plans _ _ _
  rw [← hp] at halloc hw
  unfold functionRows at hw
  rw [wirePlans_eq] at hw
  have htarget := functionRows_targets hc.size
  have hnd : blocks.toList.Nodup := List.nodup_iff_eq_of_getElem_eq.mpr fun i j hi hj h =>
    Classical.byContradiction fun hn => RegionPtr.BlockChain_array_injective hchain i j hi hj hn h
  have hnd' : ((functionRows f blocks).map IndexedBlock.target).Nodup := by rwa [htarget]
  obtain ⟨hg, hrows⟩ := wireRows_spec hw (resolvePlanRows halloc) hop hnd'
    (fun row hm => hf.opChains (by simp) (he _ (by
      exact Array.mem_toList_iff.mp (htarget ▸ List.mem_map_of_mem (f := IndexedBlock.target) hm))))
    hv (fun row hm => by
      obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hm
      have hs := (functionRows_get.mp (List.getElem?_eq_some_iff.mpr ⟨hk, hget⟩)).1
      intro dst hd
      exact ((checkBlocks_accepts_iff.mp hck).2.1 _ (Complete.mem_of_get hs) _ hd).1)
  rw [hp] at halloc
  unfold Complete.plansOf at halloc
  have hl := Complete.resolvesList_zipIdx (R := fun (p : ResolvedBlock × BlockPtr) ops =>
    ResolvesList (BinaryAllocated c) (p.1.insts.filterMap ResolvedInst.binary) ops)
    (Complete.resolvesList_of_map (g := fun x : (ResolvedBlock × BlockPtr) × Nat => match x with
      | ((b, block), id) => (⟨block, b.insts.filterMap ResolvedInst.binary, (id, b.terminator)⟩ : Complete.Plan)) halloc)
  refine ⟨(hf.trans hg).mono (fun op hm => .inr (hfresh op (by simpa using hm))) ?_ (by simp),
    groups, resolvesList_transfer hl (fun _ _ _ h => (Complete.resolvesList_lookup h).1.symm), hrows⟩
  intro block hm
  refine .inl ?_
  change block ∈ (functionRows f blocks).map IndexedBlock.target at hm
  rwa [htarget] at hm

theorem instructionResults_length
    (h : ResolvesList (fun (p : ResolvedBlock × BlockPtr) (ops : List OperationPtr) =>
      ops.length = (p.1.insts.filterMap ResolvedInst.binary).length) body groups) :
    (instructionResults body groups).length = (body.flatMap (·.1.insts)).length := by
  induction h with
  | nil => rfl
  | @cons p ops body groups h _ ih =>
    obtain ⟨b, block⟩ := p
    have hn := blockDefinitions_length (block := block) (arg := 0) h
    change (blockDefinitions block 0 b.insts ops ++ instructionResults body groups).length = _
    simpa [List.flatMap_cons, hn] using congrArg (b.insts.length + ·) ih

theorem validMappedRef {blocks : Array BlockPtr} {id : ValueId}
    (hs : blocks.size = f.blocks.size)
    (h : ResolvesList (fun (p : ResolvedBlock × BlockPtr) (ops : List OperationPtr) =>
      ops.length = (p.1.insts.filterMap ResolvedInst.binary).length) (f.blocks.toList.zip blocks.toList) groups)
    (hv : functionValues f entry (f.blocks.toList.zip blocks.toList) groups id = some v) :
    ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length (.ref id) := by
  cases id with
  | param i => simpa [ValidResolvedValue, functionValues] using (show i < f.header.params.length from by
      exact Classical.byContradiction fun h => by simp [functionValues, h] at hv)
  | inst i =>
    have he : (instructionResults (f.blocks.toList.zip blocks.toList) groups)[i]? = some v := by
      simpa [functionValues, instructionResults] using hv
    have hb := (List.getElem?_eq_some_iff.mp he).1
    have hm : (f.blocks.toList.zip blocks.toList).map Prod.fst = f.blocks.toList :=
      List.map_fst_zip (by simp [hs])
    rw [instructionResults_length h, ← List.flatMap_map, hm] at hb
    exact hb

theorem OperandTile.valid
    (h : OperandTile ctx values ty v ptr tile)
    (hvalid : ∀ id ptr, values id = some ptr →
      ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length (.ref id)) :
    ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length v := by
  cases v with
  | ref id => exact hvalid id ptr h.1
  | intConst => trivial

theorem binaryTile_valid
    (h : LowersResolvedInstTile ctx values (.bin i, key) tile)
    (hvalid : ∀ id ptr, values id = some ptr →
      ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length (.ref id)) :
    ValidResolvedInst f.header.params.length (f.blocks.toList.flatMap (·.insts)).length f.blocks.size (.bin i) := by
  cases i
  obtain ⟨_, _, _, _, _, _, hl, hr, _⟩ := h
  exact ⟨OperandTile.valid hl hvalid, OperandTile.valid hr hvalid⟩

theorem terminatorTile_valid {blocks : BlockMap} {t : ResolvedTerminator}
    (h : LowersTerminatorTile ctx f blocks values src t tile)
    (hd : ∀ dst ∈ t.successors, dst < f.blocks.size)
    (hvalid : ∀ id ptr, values id = some ptr →
      ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length (.ref id)) :
    ValidResolvedTerminator f.header.params.length (f.blocks.toList.flatMap (·.insts)).length f.blocks.size t := by
  cases t with
  | ret => obtain ⟨_, _, _, hv, _⟩ := h; exact OperandTile.valid hv hvalid
  | br dst => exact hd dst (by simp [ResolvedTerminator.successors])
  | condBr c yes no =>
    obtain ⟨_, _, _, _, _, _, _, hv, _⟩ := h
    exact ⟨OperandTile.valid hv hvalid, hd yes (by simp [ResolvedTerminator.successors]),
      hd no (by simp [ResolvedTerminator.successors])⟩

theorem phi_valid {blocks : BlockMap} {incoming : List (BlockId × ResolvedValue)}
    (ht : ∀ i b, f.blocks[i]? = some b → ∃ tile, LowersTerminatorTile ctx f blocks values i b.terminator tile)
    (hvalid : ∀ id ptr, values id = some ptr →
      ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length (.ref id))
    (hb : f.blocks[dst]? = some b) (hm : .phi ty incoming ∈ b.insts)
    (ha : PhiInputsAgree incoming) (hp : HasPredEdges f dst (incoming.map Prod.fst)) :
    ValidResolvedInst f.header.params.length (f.blocks.toList.flatMap (·.insts)).length f.blocks.size (.phi ty incoming) := by
  intro ⟨src, value⟩ hv
  obtain ⟨b', hb', hd⟩ := Complete.HasPredEdges.src hp hv
  refine ⟨(Array.getElem?_eq_some_iff.mp hb').1, ?_⟩
  cases value with
  | intConst => trivial
  | ref id =>
    obtain ⟨_, ht⟩ := ht src b' hb'
    obtain ⟨_, _, he⟩ := Complete.term_edge ht hd
    obtain ⟨ptr, hr, _⟩ := Complete.LowersEdge.ref_typed he hb hm ha hv
    exact hvalid id ptr hr

theorem functionRows_code {blocks : Array BlockPtr}
    (h : ∀ row ∈ functionRows f blocks, LowersBlockCode ctx f (fun i => blocks[i]?) values
      row.index row.offset row.source row.target)
    (hs : f.blocks[k]? = some source) (hb : blocks[k]? = some target) :
    LowersBlockCode ctx f (fun i => blocks[i]?) values k
      ((f.blocks.toList.take k).map (·.insts.length)).sum source target := by
  let row := IndexedBlock.mk source target k ((f.blocks.toList.take k).map (·.insts.length)).sum
  exact h row (List.mem_of_getElem? (functionRows_get.mpr ⟨hs, hb, rfl, rfl⟩))

theorem loweredFunction_valid {blocks : Array BlockPtr}
    (hsize : blocks.size = f.blocks.size)
    (hck : checkBlocks f = .ok ())
    (h : ∀ row ∈ functionRows f blocks, LowersBlockCode ctx f (fun i => blocks[i]?) values
      row.index row.offset row.source row.target)
    (hvalid : ∀ id ptr, values id = some ptr →
      ValidResolvedValue f.header.params.length (f.blocks.toList.flatMap (·.insts)).length (.ref id)) :
    ValidResolvedFunction f := by
  have hcode k b (hs : f.blocks[k]? = some b) :=
    functionRows_code h hs (Array.getElem?_eq_getElem (show k < blocks.size by rw [hsize]; exact (Array.getElem?_eq_some_iff.mp hs).1))
  have ht k (b : ResolvedBlock) (hs : f.blocks[k]? = some b) :
      ∃ tile, LowersTerminatorTile ctx f (fun i => blocks[i]?) values k b.terminator tile := by
    obtain ⟨_, tile, _, ht, _⟩ := hcode k b hs
    exact ⟨tile, ht⟩
  obtain ⟨_, hd, hphi⟩ := checkBlocks_accepts_iff.mp hck
  intro b hb
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hb
  have hs : f.blocks[k]? = some b := by simpa using List.getElem?_eq_some_iff.mpr ⟨hk, hget⟩
  obtain ⟨_, _, hi, hterm, _⟩ := hcode k b hs
  refine ⟨fun i hm => ?_, terminatorTile_valid hterm (fun dst hh => (hd b hb dst hh).2) hvalid⟩
  cases i with
  | bin i =>
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hm
    have hz : (.bin i, ((f.blocks.toList.take k).map (·.insts.length)).sum + j) ∈ b.insts.zipIdx ((f.blocks.toList.take k).map (·.insts.length)).sum := by
      simp [List.mk_mem_zipIdx_iff_le_and_getElem?_sub, List.getElem?_eq_some_iff.mpr ⟨hj, hget⟩]
    obtain ⟨_, htile⟩ := resolvesList_mem_left hi hz
    exact binaryTile_valid htile hvalid
  | phi ty incoming =>
    have ⟨ha, hp⟩ := (hphi b k (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hs))).2 ty incoming hm
    exact phi_valid ht hvalid hs hm ha hp

theorem checkedPhiArgs {insts : List ResolvedInst} {block : BlockPtr} {values : ValueMap}
    (hops : ops.length = (insts.filterMap ResolvedInst.binary).length)
    (hvalues : ∀ (j : Nat) v, (blockDefinitions block arg insts ops)[j]? = some v →
      values (.inst (offset + j)) = some v)
    (htypes : ∀ (j : Nat) ty, (insts.filterMap ResolvedInst.phiType)[j]? = some ty →
      typeOf raw (block.getArgument (arg + j)) = lowerType ty)
    (hphi : ∀ ty incoming, .phi ty incoming ∈ insts →
      PhiInputsAgree incoming ∧ HasPredEdges f dst (incoming.map Prod.fst)) :
    ∃ phis, FilterRel (fun i p => i = p ∧ i.1.phiType ≠ none) (insts.zipIdx offset) phis ∧
      ResolvesList (fun (inst, i) v => ∃ ty incoming, inst = .phi ty incoming ∧
        typeOf raw v = lowerType ty ∧ values (.inst i) = some v ∧ PhiInputsAgree incoming ∧
        ∀ src, incoming.countP (fun pair => pair.1 = src) =
          ((f.blocks[src]?.map (·.terminator.successors)).getD []).count dst)
        phis ((List.range' arg (insts.filterMap ResolvedInst.phiType).length).map (fun j => ValuePtr.blockArgument (block.getArgument j))) := by
  induction insts generalizing arg offset ops with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons i insts ih =>
    have ht := fun ty incoming hm => hphi ty incoming (List.mem_cons_of_mem _ hm)
    cases i with
    | bin i =>
      cases ops with
      | nil => simp [ResolvedInst.binary] at hops
      | cons op ops =>
        obtain ⟨ps, hp, hr⟩ := ih (arg := arg) (offset := offset + 1) (by simpa [ResolvedInst.binary] using hops)
          (fun j v h => by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hvalues (j + 1) v h) htypes ht
        exact ⟨ps, .drop (by simp [ResolvedInst.phiType]) hp, hr⟩
    | phi ty incoming =>
      obtain ⟨ps, hp, hr⟩ := ih (arg := arg + 1) (offset := offset + 1) hops
        (fun j v h => by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hvalues (j + 1) v h)
        (fun j t h => by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htypes (j + 1) t h) ht
      have ⟨ha, hc⟩ := hphi ty incoming List.mem_cons_self
      have he src : incoming.countP (fun pair => pair.1 = src) =
          ((f.blocks[src]?.map (·.terminator.successors)).getD []).count dst := by
        cases hh : f.blocks[src]? <;>
          simpa [hh, List.count_eq_countP, Bool.beq_eq_decide_eq, Function.comp_def] using hc src
      exact ⟨(ResolvedInst.phi ty incoming, offset) :: ps, .keep ⟨rfl, by simp [ResolvedInst.phiType]⟩ hp,
        .cons ⟨ty, incoming, rfl, htypes 0 ty rfl, hvalues 0 _ rfl, ha, he⟩ hr⟩

theorem constructBlockArgs {blocks : Array BlockPtr} {b : ResolvedBlock}
    (hc : Complete.Created ctx f entry blocks) (hd : k ≠ 0)
    (hs : f.blocks[k]? = some b) (hb : blocks[k]? = some block)
    (hg : ResolvesList (fun (p : ResolvedBlock × BlockPtr) (ops : List OperationPtr) =>
      ops.length = (p.1.insts.filterMap ResolvedInst.binary).length) (f.blocks.toList.zip blocks.toList) groups)
    (hck : checkBlocks f = .ok ()) :
    LowersBlockArgs ctx.raw (functionValues f entry (f.blocks.toList.zip blocks.toList) groups) f k
      (b.insts.zipIdx ((f.blocks.toList.take k).map (·.insts.length)).sum) block := by
  let offset := ((f.blocks.toList.take k).map (·.insts.length)).sum
  let row := IndexedBlock.mk b block k offset
  have hrow : (functionRows f blocks)[k]? = some row := functionRows_get.mpr ⟨hs, hb, rfl, rfl⟩
  have hsrc : (f.blocks.toList.zip blocks.toList)[k]? = some (b, block) :=
    List.getElem?_zip_eq_some.mpr ⟨by simpa using hs, by simpa using hb⟩
  have hi : k < groups.length := (Complete.resolvesList_lookup hg).1 ▸ (List.getElem?_eq_some_iff.mp hsrc).1
  have hops := Complete.resolvesList_lookup hg |>.2 _ _ _ hsrc (List.getElem?_eq_getElem hi)
  have hzip : (row, groups[k]) ∈ (functionRows f blocks).zip groups :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hrow, List.getElem?_eq_getElem hi⟩)
  have hvalues j v (hv : (blockDefinitions block 0 b.insts groups[k])[j]? = some v) :
      functionValues f entry (f.blocks.toList.zip blocks.toList) groups (.inst (offset + j)) = some v := by
    have he := indexedBlock_results (offset := 0) (start := 0) hg hzip hv
    simpa [functionValues, instructionResults, row] using he.1
  have htypes j ty (ht : (b.insts.filterMap ResolvedInst.phiType)[j]? = some ty) :=
    (Complete.blockArgs_ready hc hck hs hb ht).2
  have hphi := ((checkBlocks_accepts_iff.mp hck).2.2 b k
    (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hs))).2
  obtain ⟨phis, hp, hr⟩ := checkedPhiArgs (dst := k) (arg := 0) (raw := ctx.raw) (block := block) hops hvalues
    (fun j ty ht => by simpa [BlockPtr.getArgument] using htypes j ty ht) hphi
  refine ⟨phis, hp, ?_⟩
  have hn : block.getNumArguments! ctx.raw = (b.insts.filterMap ResolvedInst.phiType).length := by
    rw [← BlockPtr.getArgumentTypes!.size_eq_getNumArguments!, hc.args k b block hd hs hb, ← List.map_filterMap]
    simp
  simpa [BlockPtr.getArguments!, hn, List.range_eq_range'] using hr

theorem frame_arguments {block : BlockPtr} (hf : LoweringFrame ctx ctx' ws ins ex) (hb : block.InBounds ctx.raw) :
    block.getArguments! ctx'.raw = block.getArguments! ctx.raw := by
  have he := congrArg Array.size (hf.arguments block hb)
  rw [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!, BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] at he
  simp [BlockPtr.getArguments!, he]

theorem frameBlockArgs {insts : List (ResolvedInst × Nat)}
    (h : LowersBlockArgs ctx.raw values f k insts block)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hb : block.InBounds ctx.raw) :
    LowersBlockArgs ctx'.raw values f k insts block := by
  obtain ⟨phis, hp, hr⟩ := h
  refine ⟨phis, hp, ?_⟩
  rw [frame_arguments hf hb]
  refine resolvesList_transfer hr fun _ arg hm ⟨ty, incoming, he, ht, hv, ha, hh⟩ => ?_
  have hi := BlockPtr.getArguments!_inBounds ctx.wellFormed.inBounds hb (Array.mem_toList_iff.mp hm)
  exact ⟨ty, incoming, he, (hf.valueTypes arg hi).trans ht, hv, ha, hh⟩

theorem frameEntry {blocks : BlockMap}
    (h : LowersEntry ctx f blocks values block)
    (hf : LoweringFrame ctx ctx' [] ins ex) (hb : block ∉ ins) :
    LowersEntry ctx' f blocks values block := by
  obtain ⟨src, tiles, term, hs, hl, hargs, hvals, hp, ht, hr, hc⟩ := h
  refine ⟨src, tiles, term, hs, hl, (hf.arguments block hc.blockInBounds).trans hargs,
    fun i => by rw [frame_arguments hf hc.blockInBounds]; exact hvals i, hp,
    frameInstTiles ht hf (by simp), frameTerminator hr hf (by simp), hf.opChains hb hc⟩

theorem frameBlock {blocks : BlockMap}
    (h : LowersBlock ctx f blocks values k block)
    (hf : LoweringFrame ctx ctx' [] ins ex) (hb : block ∉ ins) :
    LowersBlock ctx' f blocks values k block := by
  obtain ⟨src, tiles, term, hs, hl, ho, ha, ht, hr, hc⟩ := h
  exact ⟨src, tiles, term, hs, hl, ho, frameBlockArgs ha hf hc.blockInBounds,
    frameInstTiles ht hf (by simp), frameTerminator hr hf (by simp), hf.opChains hb hc⟩

theorem frameFunction (h : LowersFunction ctx f op)
    (hf : LoweringFrame ctx ctx' [] [parent] [])
    (hm : MatchesOp ctx root Builtin.module #[] #[] #[r] default defaultModuleAttrs)
    (hb : r.BlockChain ctx.raw #[parent]) :
    LowersFunction ctx' f op := by
  obtain ⟨hv, region, body, entry, values, hfun, hr, hs, he, hentry, hblocks⟩ := h
  have hne : op ≠ root := by
    have h1 : op.getOpType! ctx.raw = ofDialect OpCode Llvm.func := by grind [MatchesOp]
    have h2 : root.getOpType! ctx.raw = ofDialect OpCode Builtin.module := by grind [MatchesOp]
    intro h; subst op; exact nomatch h1.symm.trans h2
  have ha : ∀ b ∈ body, b ∉ [parent] := by
    intro b hmem hparent
    cases List.mem_singleton.mp hparent
    have eq := Option.some.inj ((hr.opParent hmem).symm.trans (hb.opParent (by simp)))
    exact hne (Option.some.inj ((hfun.singletonRegion_parent hr.inBounds).symm.trans
      (eq ▸ hm.singletonRegion_parent hb.inBounds)))
  exact ⟨hv, region, body, entry, values, hf.fields (by simp) hfun, hf.blockChains (by simp) hr, hs,
    he, frameEntry hentry hf (ha _ (Array.mem_of_getElem? he)),
    fun i b hi get => frameBlock (hblocks i b hi get) hf (ha _ (Array.mem_of_getElem? get))⟩

theorem emit_function_spec
    (h : (emit .func #[] #[] #[region]
      { sym_name := ⟨f.header.name.toUTF8⟩
        function_type := { inputs := (f.header.params.toArray.map (lowerType ·.ty)).map Subtype.val,
                           outputs := #[(lowerType f.header.retType).val] }
        extra := defaultFuncExtra } parent).run ctx = .ok (op, ctx'))
    (hp : parent.OpChain ctx.raw ops) :
    LoweringFrame ctx ctx' [] [parent] [] ∧ parent.OpChain ctx'.raw (ops.push op) ∧
      MatchesOp ctx' op Llvm.func #[] #[] #[region]
        (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
          { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
            outputs := #[(lowerType f.header.retType).val] } defaultFuncExtra) := by
  obtain ⟨hf, hm, _, _, he⟩ := emit_spec h
  have hinputs : (f.header.params.toArray.map (lowerType ·.ty)).map Subtype.val =
      f.header.params.toArray.map (fun p => (lowerType p.ty).val) := Array.map_map
  exact ⟨hf, he _ hp, by rwa [hinputs] at hm⟩

theorem assembleFunction {blocks : Array BlockPtr}
    (hc : Complete.Created ctx f entry blocks) (hregion : region.BlockChain ctx.raw blocks)
    (hcheck : checkBlocks f = .ok ())
    (hg : ResolvesList (fun (p : ResolvedBlock × BlockPtr) ops => ops.length =
      (p.1.insts.filterMap ResolvedInst.binary).length) (f.blocks.toList.zip blocks.toList) groups)
    (hcode : ∀ row ∈ functionRows f blocks, LowersBlockCode ctx f (fun i => blocks[i]?)
      (functionValues f entry (f.blocks.toList.zip blocks.toList) groups)
      row.index row.offset row.source row.target)
    (hm : MatchesOp ctx op Llvm.func #[] #[] #[region]
      (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
          { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
            outputs := #[(lowerType f.header.retType).val] } defaultFuncExtra)) :
    LowersFunction ctx f op := by
  obtain ⟨⟨src, hsrc, hnone⟩, _, hphis⟩ := checkBlocks_accepts_iff.mp hcheck
  have hv := loweredFunction_valid hc.size hcheck hcode (fun _ _ => validMappedRef hc.size hg)
  refine ⟨hv, region, blocks, entry, functionValues f entry (f.blocks.toList.zip blocks.toList) groups, hm, hregion, hc.size, hc.first, ?_, ?_⟩
  · obtain ⟨tiles, term, ht, hterm, hchain⟩ := functionRows_code hcode hsrc hc.first
    exact ⟨src, tiles, term, hsrc, hc.first, hc.entryArgs, fun _ => functionValues_param hc.entryArgs,
      hnone, by simpa using ht, hterm, hchain⟩
  · intro k block hk hb
    have hs : k < f.blocks.size := hc.size ▸ (Array.getElem?_eq_some_iff.mp hb).1
    have hsrc := Array.getElem?_eq_getElem hs
    obtain ⟨tiles, term, ht, hterm, hchain⟩ := functionRows_code hcode hsrc hb
    have hmem : (f.blocks[k], k) ∈ f.blocks.toList.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr (by
      simpa only [Array.getElem?_toList] using hsrc)
    have horder := (hphis _ k hmem).1
    exact ⟨_, tiles, term, hsrc, hb, horder, constructBlockArgs hc hk hsrc hb hg hcheck, ht, hterm, hchain⟩

theorem lowerFunction_spec (h : (lowerFunction parent f).run ctx = .ok (op, ctx'))
    (hp : parent.OpChain ctx.raw ops) :
    LoweringFrame ctx ctx' [] [parent] [] ∧ parent.OpChain ctx'.raw (ops.push op) ∧ LowersFunction ctx' f op := by
  have hck := lowerFunction_checkBlocks h
  obtain ⟨⟨src, hsrc, _⟩, _⟩ := checkBlocks_accepts_iff.mp hck
  simp only [lowerFunction, lowerM_bind_ok] at h
  obtain ⟨⟨⟩, c, hcheck, ⟨region, entry⟩, d, hbody, tail, e, htail, ⟨⟩, g, hw, hf⟩ := h
  have hce : c = ctx := by
    simpa [StateT.run, StateT.lift, hck, Functor.map, Except.map, eq_comm] using hcheck
  subst c
  obtain ⟨hbodyFrame, hentryRegion, hentry, hnewRegion, hnewEntry⟩ := createBody_spec hbody
  obtain ⟨htailFrame, hregion, hempty⟩ := createBlocks_spec htail hentryRegion
  obtain ⟨_, _, _, hent, htypes⟩ := Complete.createBody_ok hbody
  obtain ⟨hg, hts⟩ := Complete.createBlocks_ok htail
  let blocks := (entry :: tail).toArray
  have hc := Complete.created_of_tail hsrc (hg.bounds (.block entry) hent) ((hg.arguments entry hent).trans htypes) hts
  have hreg : region.BlockChain e.raw blocks := by
    change region.BlockChain e.raw (entry :: tail).toArray
    rw [List.toArray_cons]
    exact hregion
  have he : ∀ b ∈ blocks, b.OpChain e.raw #[] := by
    intro b hm
    rcases List.mem_cons.mp (List.mem_toArray.mp hm) with rfl | hm
    · exact htailFrame.opChains (by simp) hentry
    · exact (hempty b hm).1
  obtain ⟨hwf, groups, hgroups, hrows⟩ := lowerBlocks_body_spec hw hc hck hreg he
  have hnew b (hm : b ∈ blocks) : ¬b.InBounds ctx.raw := by
    rcases List.mem_cons.mp (List.mem_toArray.mp hm) with rfl | hm
    · exact hnewEntry
    · exact fun hi => (hempty b hm).2 (hbodyFrame.bounds (.block b) hi)
  have hframeBefore : LoweringFrame ctx g [] [] [] := by
    refine ((hbodyFrame.trans htailFrame).trans hwf).mono (by simp) ?_ (by simpa using hnewRegion)
    intro b hm
    exact .inr (hnew b (Array.mem_toList_iff.mp hm))
  obtain ⟨hf, hp', hmatch⟩ := emit_function_spec hf (hframeBefore.opChains (by simp) hp)
  refine ⟨hframeBefore.trans hf, hp', assembleFunction ((hc.frame hwf).frame hf)
    (hf.blockChains (by simp) (hwf.blockChains (by simp) hreg)) hck hgroups ?_ hmatch⟩
  intro row hm
  refine (hrows row hm).frame hf ?_ (by simp)
  intro heq
  have hmem : row.target ∈ blocks := by
    have hh := List.mem_map_of_mem (f := IndexedBlock.target) hm
    rw [functionRows_targets hc.size] at hh
    exact Array.mem_toList_iff.mp hh
  have he : row.target = parent := List.mem_singleton.mp heq
  subst parent
  exact hnew _ hmem hp.blockInBounds

theorem lowerFunctions_spec {fs : List ResolvedFunction}
    (h : (fs.forM fun f => do let _ ← lowerFunction parent f).run ctx = .ok ((), ctx'))
    (hm : MatchesOp ctx root Builtin.module #[] #[] #[region] default defaultModuleAttrs)
    (hr : region.BlockChain ctx.raw #[parent]) (hp : parent.OpChain ctx.raw ops) :
    LoweringFrame ctx ctx' [] [parent] [] ∧ ∃ newOps,
      ResolvesList (LowersFunction ctx') fs newOps ∧ parent.OpChain ctx'.raw (ops ++ newOps.toArray) := by
  induction fs generalizing ctx ops with
  | nil => cases h; exact ⟨LoweringFrame.refl.mono (by simp) (by simp) (by simp), [], .nil, by simpa using hp⟩
  | cons f fs ih =>
    simp only [List.forM_eq_forM, List.forM_cons, lowerM_bind_ok] at h
    obtain ⟨_, _, ⟨op, c, hf, he⟩, ht⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (lowerM_pure_ok.mp he)
    obtain ⟨hf, hc, hof⟩ := lowerFunction_spec hf hp
    have hmod := hf.fields (by simp) hm
    have hrc := hf.blockChains (by simp) hr
    obtain ⟨hg, os, hos, hchain⟩ := ih ht hmod hrc hc
    refine ⟨(hf.trans hg).mono (by simp) (by simp) (by simp), op :: os, .cons (frameFunction hof hg hmod hrc) hos, ?_⟩
    have he : ops.push op ++ os.toArray = ops ++ (op :: os).toArray := by
      apply Array.toList_inj.mp
      simp only [Array.toList_append, Array.toList_push, List.append_assoc, List.singleton_append]
    exact he ▸ hchain

end Sound

theorem lowerModule_sound (h : lowerModule m = .ok (ctx, root)) : LowersModule ctx m root := by
  rcases hc : createModule with _ | ⟨c, op⟩
  · simp [lowerModule, hc] at h
  obtain ⟨r, block, hm, hr, hp, _, hargs⟩ := createModule_sound hc
  have he : (op.getRegion! c.raw 0).getFirstBlock! c.raw = some block := by
    rw [← OperationPtr.getRegions!.getElem!_eq_getRegion!, hm.regions_eq]
    simpa using hr.first
  simp only [lowerModule, hc, he, Except.bind_eq_ok] at h
  obtain ⟨⟨⟨⟩, d⟩, hf, hon⟩ := h
  change Except.ok (d, op) = _ at hon
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hon)
  obtain ⟨hf, os, hos, hchain⟩ := Sound.lowerFunctions_spec hf hm hr hp
  exact ⟨r, block, os, hf.fields (by simp) hm, hf.blockChains (by simp) hr, by simpa using hchain,
    (hf.arguments block hp.blockInBounds).trans hargs, hos⟩

theorem lowersModule_of_lowerModule_iso
    (he : lowerModule m = .ok (ctx', root'))
    (hi : equivalent_modulo_renaming ctx root ctx' root') :
    LowersModule ctx m root :=
  (lowerModule_sound he).of_iso hi.symm

theorem lowerModule_correct_of_unique
    (unique : ∀ {ctx₁ ctx₂ root₁ root₂}, LowersModule ctx₁ m root₁ → LowersModule ctx₂ m root₂ →
      equivalent_modulo_renaming ctx₁ root₁ ctx₂ root₂) :
    LowersModule ctx m root ↔ ∃ ctx₂ root₂, lowerModule m = .ok (ctx₂, root₂) ∧
      equivalent_modulo_renaming ctx root ctx₂ root₂ := by
  constructor
  · intro h
    obtain ⟨ctx₂, root₂, he⟩ := lowerModule_total h
    exact ⟨ctx₂, root₂, he, unique h (lowerModule_sound he)⟩
  · rintro ⟨_, _, he, hi⟩
    exact lowersModule_of_lowerModule_iso he hi

end Veir.LLVMLowering
