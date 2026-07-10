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

/--
info: 'Veir.ISelPass.impl_isModuleRefinedBy' depends on axioms: [propext,
 ByteArray.toBitVecLE_eight,
 ByteArray.toBitVecLE_one,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 freeze_local_preservesSemantics,
 interpretOp'_branch_dest_mem,
 interpretOp'_monotone,
 interpretOp'_results_conform,
 store_local_preservesSemantics,
 BlockPtr.dominates,
 BlockPtr.dominates_antisymm,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominatesIp_iff,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 RewrittenAt.op_dominatesIp_before_transport,
 RewrittenAt.value_dominatesIp_before_transport,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 LocalRewritePattern.Valid.of_preservesSemantics,
 WfIRContext.Dom.blockArgument_not_dominatesIp_before_of_dominatesIp_firstOp,
 WfIRContext.Dom.block_dominates_of_arg_dominatesIp_afterLast,
 WfIRContext.Dom.block_dominates_of_opResult_dominatesIp_atStart!,
 WfIRContext.Dom.not_opResult_dominatesIp_before_cycle,
 WfIRContext.Dom.opResult_not_dominatesIp_atStart!,
 WfIRContext.Dom.opResult_not_dominatesIp_before_self,
 WfIRContext.Dom.op_dominatesIp_successor_entry,
 WfIRContext.Dom.value_dominatesIp_after_iff,
 WfIRContext.Dom.value_dominatesIp_successor_entry,
 WfIRContext.Verified.entry_definesDominating,
 WfIRContext.Verified.entry_equationLemmaAt_atStart,
 WfIRContext.Verified.operationList_split,
 WfIRContext.WithCreatedOps.op_dominatesIp_before_reflect,
 WfIRContext.WithCreatedOps.value_dominatesIp_before_reflect,
 abs_isRefinedBy_toInt_max_neg._native.bv_decide.ax_1_11,
 ashr_isRefinedBy_toInt_sra._native.bv_decide.ax_1_5,
 ashr_isRefinedBy_toInt_sra_sextb._native.bv_decide.ax_1_5,
 ashr_isRefinedBy_toInt_sraw._native.bv_decide.ax_1_5,
 bitcast_isRefinedBy_addrToByte._native.bv_decide.ax_1_8,
 bitcast_isRefinedBy_byteToInt._native.bv_decide.ax_1_14,
 bitcast_isRefinedBy_byteToInt._native.bv_decide.ax_1_19,
 bitcast_isRefinedBy_byteToInt._native.bv_decide.ax_1_24,
 bitcast_isRefinedBy_byteToInt._native.bv_decide.ax_1_29,
 bitcast_isRefinedBy_intToByte._native.bv_decide.ax_1_21,
 bitcast_isRefinedBy_intToByte._native.bv_decide.ax_1_26,
 bitcast_isRefinedBy_intToByte._native.bv_decide.ax_1_31,
 bitcast_isRefinedBy_intToByte._native.bv_decide.ax_1_36,
 bitcast_isRefinedBy_toByte._native.bv_decide.ax_1_14,
 bitcast_isRefinedBy_toByte._native.bv_decide.ax_1_19,
 bitcast_isRefinedBy_toByte._native.bv_decide.ax_1_24,
 bitcast_isRefinedBy_toByte._native.bv_decide.ax_1_9,
 bitreverse_isRefinedBy_toInt_rev8_swar._native.bv_decide.ax_1_6,
 bitreverse_isRefinedBy_toInt_srli_rev8_swar._native.bv_decide.ax_1_6,
 fshlGeneral_isRefinedBy_toInt_32._native.bv_decide.ax_1_5,
 fshlGeneral_isRefinedBy_toInt_64._native.bv_decide.ax_1_5,
 fshl_isRefinedBy_toInt_rol._native.bv_decide.ax_1_5,
 fshl_isRefinedBy_toInt_rolw._native.bv_decide.ax_1_5,
 fshl_rori_const_isRefinedBy_toInt._native.bv_decide.ax_1_7,
 fshl_roriw_const_isRefinedBy_toInt._native.bv_decide.ax_1_6,
 fshrGeneral_isRefinedBy_toInt_32._native.bv_decide.ax_1_5,
 fshrGeneral_isRefinedBy_toInt_64._native.bv_decide.ax_1_5,
 fshr_isRefinedBy_toInt_ror._native.bv_decide.ax_1_5,
 fshr_isRefinedBy_toInt_rorw._native.bv_decide.ax_1_5,
 fshr_rori_const_isRefinedBy_toInt._native.bv_decide.ax_1_7,
 fshr_roriw_const_isRefinedBy_toInt._native.bv_decide.ax_1_6,
 icmp_refinement_eq_32._native.bv_decide.ax_1_6,
 icmp_refinement_eq_8._native.bv_decide.ax_1_6,
 icmp_refinement_eq_zero_rhs_32._native.bv_decide.ax_1_6,
 icmp_refinement_eq_zero_rhs_8._native.bv_decide.ax_1_6,
 icmp_refinement_ne_32._native.bv_decide.ax_1_6,
 icmp_refinement_ne_8._native.bv_decide.ax_1_6,
 icmp_refinement_ne_zero_rhs_32._native.bv_decide.ax_1_6,
 icmp_refinement_ne_zero_rhs_8._native.bv_decide.ax_1_6,
 icmp_refinement_sge_32._native.bv_decide.ax_1_6,
 icmp_refinement_sge_8._native.bv_decide.ax_1_6,
 icmp_refinement_sgt_32._native.bv_decide.ax_1_6,
 icmp_refinement_sgt_8._native.bv_decide.ax_1_6,
 icmp_refinement_sle_32._native.bv_decide.ax_1_6,
 icmp_refinement_sle_8._native.bv_decide.ax_1_6,
 icmp_refinement_slt_32._native.bv_decide.ax_1_6,
 icmp_refinement_slt_8._native.bv_decide.ax_1_6,
 icmp_refinement_uge_32._native.bv_decide.ax_1_6,
 icmp_refinement_uge_8._native.bv_decide.ax_1_6,
 icmp_refinement_ugt_32._native.bv_decide.ax_1_6,
 icmp_refinement_ugt_8._native.bv_decide.ax_1_6,
 icmp_refinement_ule_32._native.bv_decide.ax_1_6,
 icmp_refinement_ule_8._native.bv_decide.ax_1_6,
 icmp_refinement_ult_32._native.bv_decide.ax_1_6,
 icmp_refinement_ult_8._native.bv_decide.ax_1_6,
 lshr_isRefinedBy_toByte_srl._native.bv_decide.ax_1_5,
 lshr_isRefinedBy_toByte_srlw._native.bv_decide.ax_1_5,
 lshr_isRefinedBy_toInt_srl._native.bv_decide.ax_1_5,
 lshr_isRefinedBy_toInt_srlw._native.bv_decide.ax_1_5,
 saddSat_isRefinedBy_toInt._native.bv_decide.ax_1_5,
 select_czeroeqz_isRefinedBy_toInt_32._native.bv_decide.ax_1_5,
 select_czeroeqz_isRefinedBy_toInt_64._native.bv_decide.ax_1_5,
 select_czeronez_isRefinedBy_toInt_32._native.bv_decide.ax_1_5,
 select_czeronez_isRefinedBy_toInt_64._native.bv_decide.ax_1_5,
 select_general_isRefinedBy_toInt_1._native.bv_decide.ax_1_5,
 select_general_isRefinedBy_toInt_32._native.bv_decide.ax_1_5,
 select_general_isRefinedBy_toInt_64._native.bv_decide.ax_1_5,
 shl_isRefinedBy_toByte_sll._native.bv_decide.ax_1_5,
 shl_isRefinedBy_toByte_sllw._native.bv_decide.ax_1_5,
 shl_isRefinedBy_toInt_sll._native.bv_decide.ax_1_5,
 shl_isRefinedBy_toInt_sllw._native.bv_decide.ax_1_5,
 smax_isRefinedBy_toInt_max._native.bv_decide.ax_1_15,
 smax_isRefinedBy_toInt_max_32._native.bv_decide.ax_1_17,
 smin_isRefinedBy_toInt_min._native.bv_decide.ax_1_15,
 smin_isRefinedBy_toInt_min_32._native.bv_decide.ax_1_17,
 sshlSat_isRefinedBy_toInt._native.bv_decide.ax_1_5,
 ssubSat_isRefinedBy_toInt._native.bv_decide.ax_1_5,
 sub_isRefinedBy_toInt_subw._native.bv_decide.ax_1_5,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_14,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_19,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_24,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_29,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_34,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_39,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_44,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_49,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_54,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_59,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_64,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_69,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_74,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_79,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_84,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_9,
 uaddSat_isRefinedBy_toInt_add_minu._native.bv_decide.ax_1_5,
 umax_isRefinedBy_toInt_maxu_32._native.bv_decide.ax_1_5,
 umin_isRefinedBy_toInt_minu._native.bv_decide.ax_1_5,
 umin_isRefinedBy_toInt_minu_32._native.bv_decide.ax_1_5,
 ushlSat_isRefinedBy_toInt._native.bv_decide.ax_1_5,
 usubSat_isRefinedBy_toInt_sub_maxu._native.bv_decide.ax_1_16,
 zextb_val._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8,
 Data.RISCV.icmp_refinement_sge._native.bv_decide.ax_1_5,
 Data.RISCV.icmp_refinement_sle._native.bv_decide.ax_1_5,
 Data.RISCV.icmp_refinement_uge._native.bv_decide.ax_1_5,
 Data.RISCV.icmp_refinement_ule._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms ISelPass.impl_isModuleRefinedBy

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

/--
info: 'Veir.IselSDAG.impl_isModuleRefinedBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 interpretOp'_branch_dest_mem,
 interpretOp'_monotone,
 interpretOp'_results_conform,
 BlockPtr.dominates,
 BlockPtr.dominates_antisymm,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominatesIp_iff,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 OperationPtr.strictlyDominates_trans,
 RewrittenAt.op_dominatesIp_before_transport,
 RewrittenAt.value_dominatesIp_before_transport,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 ValuePtr.dominatesIp_before_of_strictlyDominates,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 LocalRewritePattern.Valid.of_preservesSemantics,
 WfIRContext.Dom.blockArgument_not_dominatesIp_before_of_dominatesIp_firstOp,
 WfIRContext.Dom.block_dominates_of_arg_dominatesIp_afterLast,
 WfIRContext.Dom.block_dominates_of_opResult_dominatesIp_atStart!,
 WfIRContext.Dom.not_opResult_dominatesIp_before_cycle,
 WfIRContext.Dom.opResult_not_dominatesIp_atStart!,
 WfIRContext.Dom.opResult_not_dominatesIp_before_self,
 WfIRContext.Dom.op_dominatesIp_successor_entry,
 WfIRContext.Dom.value_dominatesIp_after_iff,
 WfIRContext.Dom.value_dominatesIp_successor_entry,
 WfIRContext.Verified.entry_definesDominating,
 WfIRContext.Verified.entry_equationLemmaAt_atStart,
 WfIRContext.Verified.operationList_split,
 WfIRContext.WithCreatedOps.op_dominatesIp_before_reflect,
 WfIRContext.WithCreatedOps.value_dominatesIp_before_reflect,
 and_not_isRefinedBy_toInt_andn._native.bv_decide.ax_1_5,
 andi_one_val._native.bv_decide.ax_1_5,
 bexti_isRefinedBy._native.bv_decide.ax_1_6,
 not_and_isRefinedBy_toInt_andn._native.bv_decide.ax_1_5,
 not_or_isRefinedBy_toInt_orn._native.bv_decide.ax_1_5,
 not_xor_isRefinedBy_toInt_xnor._native.bv_decide.ax_1_5,
 or_not_isRefinedBy_toInt_orn._native.bv_decide.ax_1_5,
 orcb_isRefinedBy._native.bv_decide.ax_1_11,
 orcb_isRefinedBy._native.bv_decide.ax_1_16,
 orcb_isRefinedBy._native.bv_decide.ax_1_21,
 orcb_isRefinedBy._native.bv_decide.ax_1_26,
 orcb_isRefinedBy._native.bv_decide.ax_1_31,
 orcb_isRefinedBy._native.bv_decide.ax_1_36,
 orcb_isRefinedBy._native.bv_decide.ax_1_41,
 orcb_isRefinedBy._native.bv_decide.ax_1_6,
 roliw_isRefinedBy._native.bv_decide.ax_1_7,
 roriw_isRefinedBy._native.bv_decide.ax_1_7,
 sdivPow2_neg_isRefinedBy._native.bv_decide.ax_1_5,
 sdivPow2_pos_isRefinedBy._native.bv_decide.ax_1_5,
 sdivwPow2_neg_isRefinedBy._native.bv_decide.ax_1_5,
 sdivwPow2_pos_isRefinedBy._native.bv_decide.ax_1_5,
 slli_isRefinedBy._native.bv_decide.ax_1_7,
 slliuw_isRefinedBy._native.bv_decide.ax_1_6,
 slliw_isRefinedBy._native.bv_decide.ax_1_7,
 srai_isRefinedBy._native.bv_decide.ax_1_7,
 srai_slli_63_val._native.bv_decide.ax_1_5,
 sraiw_isRefinedBy._native.bv_decide.ax_1_7,
 srli_isRefinedBy._native.bv_decide.ax_1_7,
 srliw_isRefinedBy._native.bv_decide.ax_1_7,
 xor_not_isRefinedBy_toInt_xnor._native.bv_decide.ax_1_5,
 Example.and_isRefinedBy_toInt_bclri._native.bv_decide.ax_1_12,
 Example.or_isRefinedBy_toInt_bseti._native.bv_decide.ax_1_13,
 Example.xor_isRefinedBy_toInt_binvi._native.bv_decide.ax_1_12,
 MemoryState.llvmLoad._native.bv_decide.ax_8,
 Data.RISCV.icmp_refinement_sge_imm._native.bv_decide.ax_1_5,
 Data.RISCV.icmp_refinement_sle_imm._native.bv_decide.ax_1_5,
 Data.RISCV.icmp_refinement_uge_imm._native.bv_decide.ax_1_5,
 Data.RISCV.icmp_refinement_ule_imm._native.bv_decide.ax_1_5,
 Data.RISCV.sdivPow2Exact_neg_refinement._native.bv_decide.ax_1_5,
 Data.RISCV.sdivPow2Exact_pos_refinement._native.bv_decide.ax_1_5,
 Data.RISCV.sdivwPow2Exact_neg_refinement._native.bv_decide.ax_1_5,
 Data.RISCV.sdivwPow2Exact_pos_refinement._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms IselSDAG.impl_isModuleRefinedBy

end Veir
