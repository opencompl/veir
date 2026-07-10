import Veir.Passes.InstructionSelection.RewriteProofs.LowerAbs
import Veir.Passes.InstructionSelection.RewriteProofs.LowerAshr
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBexti
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBinaryReg
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBinaryW
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBinopNot
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBitcast
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBitreverse
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBswap
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBitwiseReg
import Veir.Passes.InstructionSelection.RewriteProofs.LowerByteBinaryW
import Veir.Passes.InstructionSelection.RewriteProofs.LowerConst
import Veir.Passes.InstructionSelection.RewriteProofs.LowerExt
import Veir.Passes.InstructionSelection.RewriteProofs.LowerFshlConst
import Veir.Passes.InstructionSelection.RewriteProofs.LowerFshGeneral
import Veir.Passes.InstructionSelection.RewriteProofs.LowerIcmp
import Veir.Passes.InstructionSelection.RewriteProofs.LowerFshrConst
import Veir.Passes.InstructionSelection.RewriteProofs.LowerLoad
import Veir.Passes.InstructionSelection.RewriteProofs.LowerGetelementptr
import Veir.Passes.InstructionSelection.RewriteProofs.LowerOrcb
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRoriw
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRotate
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelect
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectSingleBit
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSdivExact
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSdivPow2
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSextOne
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSignedMinMax
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSlliuw
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSlti
import Veir.Passes.InstructionSelection.RewriteProofs.LowerTrunc
import Veir.Passes.InstructionSelection.RewriteProofs.LowerUaddSat
import Veir.Passes.InstructionSelection.RewriteProofs.LowerUdivPow2
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSaddSat
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSsubSat
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSshlSat
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSignedMinMax
import Veir.Passes.InstructionSelection.RewriteProofs.LowerUnaryW
import Veir.Passes.InstructionSelection.RewriteProofs.LowerUshlSat
import Veir.Passes.InstructionSelection.RewriteProofs.LowerUsubSat
import Veir.Passes.InstructionSelection.RewriteProofs.LowerZextOne
import Veir.PatternRewriter.Soundness

namespace Veir

/-!
## Soundness of the instruction-selection pass

`ISelPass.impl` runs `RewritePattern.GreedyRewritePattern ISelPass.patterns` to fixpoint. Each element
of `ISelPass.patterns` is the standard driver (`RewritePattern.fromLocalRewrite`) of a
`LocalRewritePattern`, so `RewritePattern.isModuleRefinedBy_applyInContext_greedy_fromLocalRewrite`
reduces pass-level soundness to `LocalRewritePattern.Valid` of each of the 49 local patterns.

Two families of obligations are still open, and are admitted as axioms below:

* `LocalRewritePattern.Valid.of_preservesSemantics` — the structural fields of `Valid`
  (`Return*`, `MatchedOpHasNoRegions`, `RewritePreservesDom`, `RewritePreservesVerified`) are not yet
  proven for any pattern, so `Valid` is derived from the semantic field alone.
* `PreservesSemantics` of the 6 patterns whose bespoke correctness proof has not been written yet.
-/

/--
**Axiom (open obligation).** A local rewrite pattern whose lowering preserves semantics is `Valid`.

This discharges the structural fields of `LocalRewritePattern.Valid` — the `Return*` obligations,
`MatchedOpHasNoRegions`, `RewritePreservesDom` and `RewritePreservesVerified` — which are *not*
consequences of `PreservesSemantics` and must eventually be proven per pattern. The semantic
hypothesis is stated for arbitrary proofs of the `Return*` obligations, since `PreservesSemantics`
does not depend on them and the concrete `*_preservesSemantics` theorems leave them as free variables.
-/
axiom LocalRewritePattern.Valid.of_preservesSemantics {pattern : LocalRewritePattern OpCode}
    (h : ∀ (returnOps : pattern.ReturnOps) (returnCtxChanges : pattern.ReturnCtxChanges)
        (returnValuesInBounds : pattern.ReturnValuesInBounds) (returnValues : pattern.ReturnValues),
      pattern.PreservesSemantics returnOps returnCtxChanges returnValuesInBounds returnValues) :
    pattern.Valid

/-! ### Axiomatized `PreservesSemantics` obligations

The remaining instruction-selection patterns whose semantics preservation has not been proven yet.
Each of these should be replaced by a theorem in `Veir/Passes/InstructionSelection/RewriteProofs/`. -/

/- Store cannot be proven with our current lifting proof, as we expect the memory to be
equal, not refined. -/
axiom store_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps store_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges store_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds store_local}
    {h₄ : LocalRewritePattern.ReturnValues store_local} :
    LocalRewritePattern.PreservesSemantics store_local h h₂ h₃ h₄

/- Freeze cannot be proven with our current lifting proof, as we do not have
a non-deterministic execution model. -/
axiom freeze_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps freeze_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges freeze_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds freeze_local}
    {h₄ : LocalRewritePattern.ReturnValues freeze_local} :
    LocalRewritePattern.PreservesSemantics freeze_local h h₂ h₃ h₄

/-! ### Validity of every instruction-selection pattern -/

/-- Every pattern the instruction-selection pass runs is the driver of a `Valid` local pattern. -/
theorem ISelPass.exists_valid_local_of_mem_patterns :
    ∀ p ∈ ISelPass.patterns, ∃ q : LocalRewritePattern OpCode,
      q.Valid ∧ p = RewritePattern.fromLocalRewrite q := by
  intro p hp
  simp only [ISelPass.patterns, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact ⟨selectCzeroeqz_local, .of_preservesSemantics fun _ _ _ _ =>
      selectCzeroeqz_local_preservesSemantics, rfl⟩
  · exact ⟨selectCzeronez_local, .of_preservesSemantics fun _ _ _ _ =>
      selectCzeronez_local_preservesSemantics, rfl⟩
  · exact ⟨selectGeneral_local, .of_preservesSemantics fun _ _ _ _ =>
      selectGeneral_local_preservesSemantics, rfl⟩
  · exact ⟨ctlz_local, .of_preservesSemantics fun _ _ _ _ => ctlz_local_preservesSemantics, rfl⟩
  · exact ⟨cttz_local, .of_preservesSemantics fun _ _ _ _ => cttz_local_preservesSemantics, rfl⟩
  · exact ⟨ctpop_local, .of_preservesSemantics fun _ _ _ _ => ctpop_local_preservesSemantics, rfl⟩
  · exact ⟨bswap_local, .of_preservesSemantics fun _ _ _ _ => bswap_local_preservesSemantics, rfl⟩
  · exact ⟨bitreverse_local, .of_preservesSemantics fun _ _ _ _ =>
      bitreverse_local_preservesSemantics, rfl⟩
  · exact ⟨constant_local, .of_preservesSemantics fun _ _ _ _ =>
      constant_local_preservesSemantics, rfl⟩
  · exact ⟨add_local, .of_preservesSemantics fun _ _ _ _ => add_local_preservesSemantics, rfl⟩
  · exact ⟨and_local, .of_preservesSemantics fun _ _ _ _ => and_local_preservesSemantics, rfl⟩
  · exact ⟨ashr_local, .of_preservesSemantics fun _ _ _ _ => ashr_local_preservesSemantics, rfl⟩
  · exact ⟨icmp_local, .of_preservesSemantics fun _ _ _ _ => icmp_local_preservesSemantics, rfl⟩
  · exact ⟨or_local, .of_preservesSemantics fun _ _ _ _ => or_local_preservesSemantics, rfl⟩
  · exact ⟨xor_local, .of_preservesSemantics fun _ _ _ _ => xor_local_preservesSemantics, rfl⟩
  · exact ⟨mul_local, .of_preservesSemantics fun _ _ _ _ => mul_local_preservesSemantics, rfl⟩
  · exact ⟨sdiv_local, .of_preservesSemantics fun _ _ _ _ => sdiv_local_preservesSemantics, rfl⟩
  · exact ⟨udiv_local, .of_preservesSemantics fun _ _ _ _ => udiv_local_preservesSemantics, rfl⟩
  · exact ⟨srem_local, .of_preservesSemantics fun _ _ _ _ => srem_local_preservesSemantics, rfl⟩
  · exact ⟨urem_local, .of_preservesSemantics fun _ _ _ _ => urem_local_preservesSemantics, rfl⟩
  · exact ⟨sext_local, .of_preservesSemantics fun _ _ _ _ => sext_local_preservesSemantics, rfl⟩
  · exact ⟨zext_local, .of_preservesSemantics fun _ _ _ _ => zext_local_preservesSemantics, rfl⟩
  · exact ⟨trunc_local, .of_preservesSemantics fun _ _ _ _ => trunc_local_preservesSemantics, rfl⟩
  · exact ⟨shl_local, .of_preservesSemantics fun _ _ _ _ => shl_local_preservesSemantics, rfl⟩
  · exact ⟨lshr_local, .of_preservesSemantics fun _ _ _ _ => lshr_local_preservesSemantics, rfl⟩
  · exact ⟨sub_local, .of_preservesSemantics fun _ _ _ _ => sub_local_preservesSemantics, rfl⟩
  · exact ⟨bitcast_local, .of_preservesSemantics fun _ _ _ _ =>
      bitcast_local_preservesSemantics, rfl⟩
  · exact ⟨load_local, .of_preservesSemantics fun _ _ _ _ => load_local_preservesSemantics, rfl⟩
  · exact ⟨getelementptr_local, .of_preservesSemantics fun _ _ _ _ =>
      getelementptr_local_preservesSemantics, rfl⟩
  · exact ⟨store_local, .of_preservesSemantics fun _ _ _ _ => store_local_preservesSemantics, rfl⟩
  · exact ⟨smax_local, .of_preservesSemantics fun _ _ _ _ => smax_local_preservesSemantics, rfl⟩
  · exact ⟨smin_local, .of_preservesSemantics fun _ _ _ _ => smin_local_preservesSemantics, rfl⟩
  · exact ⟨umax_local, .of_preservesSemantics fun _ _ _ _ => umax_local_preservesSemantics, rfl⟩
  · exact ⟨umin_local, .of_preservesSemantics fun _ _ _ _ => umin_local_preservesSemantics, rfl⟩
  · exact ⟨saddSat_local, .of_preservesSemantics fun _ _ _ _ =>
      saddSat_local_preservesSemantics, rfl⟩
  · exact ⟨ssubSat_local, .of_preservesSemantics fun _ _ _ _ =>
      ssubSat_local_preservesSemantics, rfl⟩
  · exact ⟨uaddSat_local, .of_preservesSemantics fun _ _ _ _ =>
      uaddSat_local_preservesSemantics, rfl⟩
  · exact ⟨usubSat_local, .of_preservesSemantics fun _ _ _ _ =>
      usubSat_local_preservesSemantics, rfl⟩
  · exact ⟨sshlSat_local, .of_preservesSemantics fun _ _ _ _ =>
      sshlSat_local_preservesSemantics, rfl⟩
  · exact ⟨ushlSat_local, .of_preservesSemantics fun _ _ _ _ =>
      ushlSat_local_preservesSemantics, rfl⟩
  · exact ⟨abs_local, .of_preservesSemantics fun _ _ _ _ => abs_local_preservesSemantics, rfl⟩
  · exact ⟨fshlConst_local, .of_preservesSemantics fun _ _ _ _ =>
      fshlConst_local_preservesSemantics, rfl⟩
  · exact ⟨fshrConst_local, .of_preservesSemantics fun _ _ _ _ =>
      fshrConst_local_preservesSemantics, rfl⟩
  · exact ⟨fshl_local, .of_preservesSemantics fun _ _ _ _ => fshl_local_preservesSemantics, rfl⟩
  · exact ⟨fshr_local, .of_preservesSemantics fun _ _ _ _ => fshr_local_preservesSemantics, rfl⟩
  · exact ⟨fshlGeneral_local, .of_preservesSemantics fun _ _ _ _ =>
      fshlGeneral_local_preservesSemantics, rfl⟩
  · exact ⟨fshrGeneral_local, .of_preservesSemantics fun _ _ _ _ =>
      fshrGeneral_local_preservesSemantics, rfl⟩
  · exact ⟨poisonConst_local, .of_preservesSemantics fun _ _ _ _ =>
      poisonConst_local_preservesSemantics, rfl⟩
  · exact ⟨freeze_local, .of_preservesSemantics fun _ _ _ _ => freeze_local_preservesSemantics, rfl⟩

/-! ### Soundness of the pass -/

/-- A successful `ISelPass.impl` run is exactly a successful fixpoint iteration of the greedy
composition of `ISelPass.patterns`: the pass throws on the failing branch. -/
theorem ISelPass.applyInContext_of_impl {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (himpl : ISelPass.impl ctx op opInBounds = pure ctx') :
    RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern ISelPass.patterns) ctx
      = some ctx' := by
  -- `impl` is a `match` on the fixpoint iteration; only the `some` branch can return `pure ctx'`.
  -- Both branches are `EStateM` actions, so apply them to a (classically chosen) world state.
  have hworld : Void IO.RealWorld := Classical.choice Void.instNonempty
  rw [ISelPass.impl] at himpl
  split at himpl
  · exact absurd (congrFun himpl hworld) fun h => by injection h with h _; injection h
  · rename_i c hc
    have := congrFun himpl hworld
    injection this with h _
    injection h with h
    exact h ▸ hc

/--
**The instruction-selection pass preserves module semantics.** If `ISelPass.impl` succeeds on a
dominance-wellformed, verified context, the resulting context is again dominance-wellformed and
verified, and every module of the source is refined by the same module of the result.
-/
theorem ISelPass.impl_isModuleRefinedBy {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (hDom : ctx.Dom) (hVerif : ctx.Verified)
    (himpl : ISelPass.impl ctx op opInBounds = pure ctx') :
    ctx'.Dom ∧ ctx'.Verified ∧
      ∀ moduleOp : OperationPtr, moduleOp.isModuleRefinedBy ctx moduleOp ctx' :=
  RewritePattern.isModuleRefinedBy_applyInContext_greedy_fromLocalRewrite
    ISelPass.exists_valid_local_of_mem_patterns hDom hVerif
    (ISelPass.applyInContext_of_impl himpl)

/-!
## Soundness of the SelectionDAG instruction-selection pass

`IselSDAG.impl` has the same shape as `ISelPass.impl`: it runs
`RewritePattern.GreedyRewritePattern IselSDAG.patterns` to fixpoint, and every element of
`IselSDAG.patterns` is `RewritePattern.fromLocalRewrite` of a local pattern whose
`PreservesSemantics` is proven. The only open obligation is the shared
`LocalRewritePattern.Valid.of_preservesSemantics` axiom above.
-/

/-- Every pattern the SelectionDAG pass runs is the driver of a `Valid` local pattern. -/
theorem IselSDAG.exists_valid_local_of_mem_patterns :
    ∀ p ∈ IselSDAG.patterns, ∃ q : LocalRewritePattern OpCode,
      q.Valid ∧ p = RewritePattern.fromLocalRewrite q := by
  intro p hp
  simp only [IselSDAG.patterns, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact ⟨andn_local, .of_preservesSemantics fun _ _ _ _ => andn_local_preservesSemantics, rfl⟩
  · exact ⟨orn_local, .of_preservesSemantics fun _ _ _ _ => orn_local_preservesSemantics, rfl⟩
  · exact ⟨xnor_local, .of_preservesSemantics fun _ _ _ _ => xnor_local_preservesSemantics, rfl⟩
  · exact ⟨orcb_local, .of_preservesSemantics fun _ _ _ _ => orcb_local_preservesSemantics, rfl⟩
  · exact ⟨bexti_local, .of_preservesSemantics fun _ _ _ _ => bexti_local_preservesSemantics, rfl⟩
  · exact ⟨selectSingleBitLocal matchOr .bseti rfl false,
      .of_preservesSemantics fun _ _ _ _ => Example.bseti_local_preservesSemantics, rfl⟩
  · exact ⟨selectSingleBitLocal matchAnd .bclri rfl true,
      .of_preservesSemantics fun _ _ _ _ => Example.bclri_local_preservesSemantics, rfl⟩
  · exact ⟨selectSingleBitLocal matchXor .binvi rfl false,
      .of_preservesSemantics fun _ _ _ _ => Example.binvi_local_preservesSemantics, rfl⟩
  · exact ⟨slliuw_local, .of_preservesSemantics fun _ _ _ _ => slliuw_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchAdd .addi rfl 64 (-2048) 2047,
      .of_preservesSemantics fun _ _ _ _ => addi_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchOr .ori rfl 64 (-2048) 2047,
      .of_preservesSemantics fun _ _ _ _ => ori_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchAnd .andi rfl 64 (-2048) 2047,
      .of_preservesSemantics fun _ _ _ _ => andi_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchXor .xori rfl 64 (-2048) 2047,
      .of_preservesSemantics fun _ _ _ _ => xori_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchShl .slli rfl 64 0 63,
      .of_preservesSemantics fun _ _ _ _ => slli_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchLshr .srli rfl 64 0 63,
      .of_preservesSemantics fun _ _ _ _ => srli_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchAshr .srai rfl 64 0 63,
      .of_preservesSemantics fun _ _ _ _ => srai_local_preservesSemantics, rfl⟩
  · exact ⟨slti_local, .of_preservesSemantics fun _ _ _ _ => slti_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchAdd .addiw rfl 32 (-2048) 2047,
      .of_preservesSemantics fun _ _ _ _ => addiw_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchShl .slliw rfl 32 0 31,
      .of_preservesSemantics fun _ _ _ _ => slliw_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchLshr .srliw rfl 32 0 31,
      .of_preservesSemantics fun _ _ _ _ => srliw_local_preservesSemantics, rfl⟩
  · exact ⟨selectBinopImmLocal matchAshr .sraiw rfl 32 0 31,
      .of_preservesSemantics fun _ _ _ _ => sraiw_local_preservesSemantics, rfl⟩
  · exact ⟨roriw_local, .of_preservesSemantics fun _ _ _ _ => roriw_local_preservesSemantics, rfl⟩
  · exact ⟨roliw_local, .of_preservesSemantics fun _ _ _ _ => roliw_local_preservesSemantics, rfl⟩
  · exact ⟨zext_1_local, .of_preservesSemantics fun _ _ _ _ => zext_1_local_preservesSemantics, rfl⟩
  · exact ⟨sext_1_local, .of_preservesSemantics fun _ _ _ _ => sext_1_local_preservesSemantics, rfl⟩
  · exact ⟨udivPow2GenLocal .srli rfl 64,
      .of_preservesSemantics fun _ _ _ _ => Example.udivPow2_local_preservesSemantics, rfl⟩
  · exact ⟨udivPow2GenLocal .srliw rfl 32,
      .of_preservesSemantics fun _ _ _ _ => Example.udivwPow2_local_preservesSemantics, rfl⟩
  · exact ⟨sdivPow2ExactGenLocal .srai rfl .sub rfl 64,
      .of_preservesSemantics fun _ _ _ _ => Example.sdivPow2Exact_local_preservesSemantics, rfl⟩
  · exact ⟨sdivPow2ExactGenLocal .sraiw rfl .subw rfl 32,
      .of_preservesSemantics fun _ _ _ _ => Example.sdivwPow2Exact_local_preservesSemantics, rfl⟩
  · exact ⟨sdivPow2GenLocal .srai rfl .srli rfl .add rfl .sub rfl 64,
      .of_preservesSemantics fun _ _ _ _ => Example.sdivPow2_local_preservesSemantics, rfl⟩
  · exact ⟨sdivPow2GenLocal .sraiw rfl .srliw rfl .addw rfl .subw rfl 32,
      .of_preservesSemantics fun _ _ _ _ => Example.sdivwPow2_local_preservesSemantics, rfl⟩

/-- A successful `IselSDAG.impl` run is exactly a successful fixpoint iteration of the greedy
composition of `IselSDAG.patterns`: the pass throws on the failing branch. -/
theorem IselSDAG.applyInContext_of_impl {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (himpl : IselSDAG.impl ctx op opInBounds = pure ctx') :
    RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern IselSDAG.patterns) ctx
      = some ctx' := by
  have hworld : Void IO.RealWorld := Classical.choice Void.instNonempty
  rw [IselSDAG.impl] at himpl
  split at himpl
  · exact absurd (congrFun himpl hworld) fun h => by injection h with h _; injection h
  · rename_i c hc
    have := congrFun himpl hworld
    injection this with h _
    injection h with h
    exact h ▸ hc

/--
**The SelectionDAG instruction-selection pass preserves module semantics.** If `IselSDAG.impl`
succeeds on a dominance-wellformed, verified context, the resulting context is again
dominance-wellformed and verified, and every module of the source is refined by the same module of
the result.
-/
theorem IselSDAG.impl_isModuleRefinedBy {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (hDom : ctx.Dom) (hVerif : ctx.Verified)
    (himpl : IselSDAG.impl ctx op opInBounds = pure ctx') :
    ctx'.Dom ∧ ctx'.Verified ∧
      ∀ moduleOp : OperationPtr, moduleOp.isModuleRefinedBy ctx moduleOp ctx' :=
  RewritePattern.isModuleRefinedBy_applyInContext_greedy_fromLocalRewrite
    IselSDAG.exists_valid_local_of_mem_patterns hDom hVerif
    (IselSDAG.applyInContext_of_impl himpl)

end Veir
