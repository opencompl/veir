import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBinaryW

namespace Veir

/-!
## Correctness of `ushlSat_local`

`llvm.intr.ushl.sat` on a 64-bit integer is lowered to LLVM's RV64 unsigned saturating-shl idiom
(`expandShlSat`): shift, then detect the lost high bits and OR in an all-ones mask on overflow.

`unrealized_conversion_cast` (each operand to a register) →
`riscv.sll`  (`shifted = lhs << rhs`) →
`riscv.srl`  (`unshifted = shifted >>u rhs`) →
`riscv.xor`  (`lostBits = lhs ^ unshifted`) →
`riscv.sltiu 1` (`noOverflow = (lostBits == 0)`) →
`riscv.addi -1` (`overflowMask = noOverflow - 1`, i.e. `0` or all-ones) →
`riscv.or`   (`overflowMask | shifted`) →
`unrealized_conversion_cast` (back to the integer type).

Like the sibling `uaddSat_local`/`usubSat_local`, it fits no combinator, so it is proven bespoke: the
two-operand `castToRegLocal` prefix followed by a straight-line register chain, here of six RISC-V
ops (two of them the immediate `sltiu`/`addi`). It is `i64`-only, so there is no bitwidth branch.

Soundness of the RISC-V shift-amount masking: `ushlSat x y` is *poison* whenever the shift amount
`y ≥ 64`, so the two-argument shifts (which mask the amount to 6 bits) only need to agree with LLVM
for `y < 64`, where masking is the identity.
-/

/-- Forward-interpretation lemma for the immediate `riscv.sltiu` (mirrors
    `interpretOp_riscv_xori_forward`). The emitted register is `Data.RISCV.sltiu k r` for the op's
    stored immediate `k`. -/
theorem interpretOp_riscv_sltiu_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {r : Data.RISCV.Reg} {k : BitVec 12}
    (hType : theOp.getOpType! ctx.raw = .riscv .sltiu)
    (hImm : BitVec.ofInt 12 (theOp.getProperties! ctx.raw (.riscv .sltiu)).value.value = k)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (Data.RISCV.sltiu k r)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.reg (Data.RISCV.sltiu k r)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [interpretOp', Riscv.interpretOp', Interp, hImm, pure])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Forward-interpretation lemma for the immediate `riscv.addi` (mirrors
    `interpretOp_riscv_xori_forward`). The emitted register is `Data.RISCV.addi k r` for the op's
    stored immediate `k`. -/
theorem interpretOp_riscv_addi_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {r : Data.RISCV.Reg} {k : BitVec 12}
    (hType : theOp.getOpType! ctx.raw = .riscv .addi)
    (hImm : BitVec.ofInt 12 (theOp.getProperties! ctx.raw (.riscv .addi)).value.value = k)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (Data.RISCV.addi k r)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.reg (Data.RISCV.addi k r)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [interpretOp', Riscv.interpretOp', Interp, hImm, pure])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Correctness of the RV64 unsigned saturating-shl lowering of a 64-bit `llvm.intr.ushl.sat`: the
    register chain `or (sll ·) (addi -1 (sltiu 1 (xor (srl ·) ·)))` refines `ushlSat`. (`xt`/`yt`
    are the possibly-more-defined target-side values of the operands.) The interpreter applies each
    binary data-level op as `RISCV.op op2 op1`, which fixes the operand order in each subterm. -/
theorem ushlSat_isRefinedBy_toInt {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.ushlSat x y ⊒
      RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))
          (Data.RISCV.addi (BitVec.ofInt 12 (-1))
            (Data.RISCV.sltiu (BitVec.ofInt 12 1)
              (Data.RISCV.xor
                (Data.RISCV.srl (LLVM.Int.toReg yt)
                  (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
                (LLVM.Int.toReg xt))))) 64 := by
  revert h₁ h₂
  veir_bv_decide

set_option maxHeartbeats 2000000 in
/-- Correctness of the `ushlSat_local` lowering: the
    `castToReg → castToReg → sll → srl → xor → sltiu 1 → addi -1 → or → castBack` round trip refines
    `llvm.intr.ushl.sat`. -/
theorem ushlSat_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics ushlSat_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, ushlSat_local, createRISCVUnitLocal,
    createRISCVImmLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchUshlSat op ctx.raw).isSome := by
    cases hM : matchUshlSat op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchUshlSat_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_intr__ushl__sat opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- Both operand types and the result type are the integer type `intType`.
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  -- Resolve the result-type-destructuring match on `intType`.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand values and their `ushlSat`.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold
      (srcFn := fun {_} x y _ => Data.LLVM.Int.ushlSat x y)
      (props := op.getProperties! ctx.raw (.llvm .intr__ushl__sat))
      opInBounds hOpType hNumResults hOperands rfl
      (fun bw x y props rt bo mem res h => by
        have hEq : Llvm.interpretOp' .intr__ushl__sat props rt #[.int bw x, .int bw y] bo mem
            = some (.ok (#[.int bw (Data.LLVM.Int.ushlSat x y)], mem, none)) := by
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]
        rw [hEq] at h; injection h with h; injection h with h; exact h.symm)
      hinterp hLhsType hRhsType
  subst hCf
  -- The matched operands dominate the rewrite point in the source context.
  have hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  peelSplittableCondition' [hBw] hpattern
  -- Source value: `op`'s single result is `ushlSat` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `lhs`/`rhs` are not among `op`'s results.
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the two `castToRegLocal` creations, transporting both operand dominance facts through.
  peelCastToRegLocal₂ hpattern ctx₁ lcastOp hLCast hDomCtxL hDomL₁ hDomCtxR hDomR₁
  peelCastToRegLocal₂ hpattern ctx₂ rcastOp hRCast hDomL₁ hDomL₂ hDomR₁ hDomR₂
  -- Freshness facts, used to keep `rhs` alive across the first cast.
  have hLCastFresh : ¬ lcastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds lcastOp hLCast
  have hLhsIn : lhs.InBounds ctx.raw := by clear hpattern; grind
  have hRhsIn : rhs.InBounds ctx.raw := by clear hpattern; grind
  have hRhsNeLCastRes : ∀ i, rhs ≠ ValuePtr.opResult (lcastOp.getResult i) := by
    intro i heq
    rw [heq] at hRhsIn
    rw [ValuePtr.inBounds_opResult] at hRhsIn
    obtain ⟨hIn, -⟩ := hRhsIn
    exact hLCastFresh hIn
  -- Peel the first three RISC-V ops with the macro (their dominance transports chain `op.InBounds`
  -- across ≤ 4 createOps, which grind handles on its own).
  peelOpCreation!₂ hpattern ctx₃ sllOp hSll hDomL₂ hDomL₃ hDomR₂ hDomR₃
  peelOpCreation!₂ hpattern ctx₄ srlOp hSrl hDomL₃ hDomL₄ hDomR₃ hDomR₄
  peelOpCreation!₂ hpattern ctx₅ xorOp hXor hDomL₄ hDomL₅ hDomR₄ hDomR₅
  -- The remaining peels reach `op.InBounds` five or more creations deep, which grind cannot chain,
  -- and any `InBounds` hypothesis in context perturbs the macro's `grind` dischargers (their
  -- non-monotonicity). So peel `sltiu`/`addi`/`or`/cast-back manually: discharge each operand's
  -- in-bounds inline (seeding the op-in-bounds and result-count facts directly) and build every
  -- `op.InBounds` witness inline, clearing it before continuing.
  -- `sltiu 1`
  have ⟨⟨ctx₆, sltiuOp⟩, hSltiu, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  replace hSltiu := WfRewriter.createOp!_none_some hSltiu
  obtain ⟨_, _, _, hSltiu⟩ := hSltiu
  have hOpIn₅ : op.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hXor
      (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSrl
        (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSll
          (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRCast
            (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLCast opInBounds))))
  have hOpNeSltiu : op ≠ sltiuOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds sltiuOp hSltiu (heq ▸ hOpIn₅)
  have hDomL₆ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hSltiu hOpIn₅ hOpNeSltiu).mpr hDomL₅
  have hDomR₆ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hSltiu hOpIn₅ hOpNeSltiu).mpr hDomR₅
  have hOpIn₆ : op.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSltiu hOpIn₅
  clear hOpNeSltiu hOpIn₅
  -- `addi -1`
  have ⟨⟨ctx₇, addiOp⟩, hAddi, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  replace hAddi := WfRewriter.createOp!_none_some hAddi
  obtain ⟨_, _, _, hAddi⟩ := hAddi
  have hOpNeAddi : op ≠ addiOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds addiOp hAddi (heq ▸ hOpIn₆)
  have hDomL₇ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hAddi hOpIn₆ hOpNeAddi).mpr hDomL₆
  have hDomR₇ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hAddi hOpIn₆ hOpNeAddi).mpr hDomR₆
  have hOpIn₇ : op.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hAddi hOpIn₆
  clear hOpNeAddi hOpIn₆
  -- `or`
  have ⟨⟨ctx₈, orOp⟩, hOr, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  replace hOr := WfRewriter.createOp!_none_some hOr
  obtain ⟨_, _, _, hOr⟩ := hOr
  have hOpNeOr : op ≠ orOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds orOp hOr (heq ▸ hOpIn₇)
  have hDomL₈ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hOr hOpIn₇ hOpNeOr).mpr hDomL₇
  have hDomR₈ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hOr hOpIn₇ hOpNeOr).mpr hDomR₇
  have hOpIn₈ : op.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOr hOpIn₇
  clear hOpNeOr hOpIn₇
  -- cast-back
  have ⟨⟨ctx₉, castBackOp⟩, hCastBack, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  simp only [replaceWithRegLocal] at hCastBack
  replace hCastBack := WfRewriter.createOp!_none_some hCastBack
  obtain ⟨_, _, _, hCastBack⟩ := hCastBack
  have hOpNeCB : op ≠ castBackOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds castBackOp hCastBack (heq ▸ hOpIn₈)
  have hDomL₉ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack hOpIn₈ hOpNeCB).mpr hDomL₈
  have hDomR₉ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack hOpIn₈ hOpNeCB).mpr hDomR₈
  clear hOpNeCB hOpIn₈
  cleanupHpattern hpattern
  -- Read the refined values `xt`/`yt` of `lhs`/`rhs` in the target state `state'`.
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hxVal
      hDomCtxL hDomL₉ lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRhsIn hyVal
      hDomCtxR hDomR₉ rNotOp
  -- The refinement obligations are discharged; drop `valueRefinement`/`state'Wf`/`state'Dom` and the
  -- intermediate dominance facts, which otherwise bloat every downstream `grind`.
  clear valueRefinement state'Wf state'Dom hDomL₉ hDomR₉ hDomL₈ hDomR₈ hDomL₇ hDomR₇
    hDomL₆ hDomR₆ hDomL₅ hDomR₅ hDomL₄ hDomR₄ hDomL₃ hDomR₃ hDomL₂ hDomR₂ hDomL₁ hDomR₁
  obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
  -- Each created op stays in bounds in every later context, and each is fresh in its own creation
  -- context. Together these give (to `grind`) the pairwise distinctness of all nine ops, which the
  -- property transports below need but `grind` cannot chain nine creations deep on its own; the
  -- `…ctx₉` facts also discharge the forward-interpretation `inBounds` obligations.
  have iOp1 : op.InBounds ctx₁.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLCast opInBounds
  have iOp2 : op.InBounds ctx₂.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRCast iOp1
  have iOp3 : op.InBounds ctx₃.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSll iOp2
  have iOp4 : op.InBounds ctx₄.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSrl iOp3
  have iOp5 : op.InBounds ctx₅.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation op) hXor iOp4
  have iOp6 : op.InBounds ctx₆.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSltiu iOp5
  have iOp7 : op.InBounds ctx₇.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation op) hAddi iOp6
  have iOp8 : op.InBounds ctx₈.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOr iOp7
  have iL1 : lcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds lcastOp hLCast
  have iL2 : lcastOp.InBounds ctx₂.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRCast iL1
  have iL3 : lcastOp.InBounds ctx₃.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hSll iL2
  have iL4 : lcastOp.InBounds ctx₄.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hSrl iL3
  have iL5 : lcastOp.InBounds ctx₅.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hXor iL4
  have iL6 : lcastOp.InBounds ctx₆.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hSltiu iL5
  have iL7 : lcastOp.InBounds ctx₇.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hAddi iL6
  have iL8 : lcastOp.InBounds ctx₈.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hOr iL7
  have iL9 : lcastOp.InBounds ctx₉.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hCastBack iL8
  have iR2 : rcastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds rcastOp hRCast
  have iR3 : rcastOp.InBounds ctx₃.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hSll iR2
  have iR4 : rcastOp.InBounds ctx₄.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hSrl iR3
  have iR5 : rcastOp.InBounds ctx₅.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hXor iR4
  have iR6 : rcastOp.InBounds ctx₆.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hSltiu iR5
  have iR7 : rcastOp.InBounds ctx₇.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hAddi iR6
  have iR8 : rcastOp.InBounds ctx₈.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hOr iR7
  have iR9 : rcastOp.InBounds ctx₉.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hCastBack iR8
  have iS3 : sllOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds sllOp hSll
  have iS4 : sllOp.InBounds ctx₄.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation sllOp) hSrl iS3
  have iS5 : sllOp.InBounds ctx₅.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation sllOp) hXor iS4
  have iS6 : sllOp.InBounds ctx₆.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation sllOp) hSltiu iS5
  have iS7 : sllOp.InBounds ctx₇.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation sllOp) hAddi iS6
  have iS8 : sllOp.InBounds ctx₈.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation sllOp) hOr iS7
  have iS9 : sllOp.InBounds ctx₉.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation sllOp) hCastBack iS8
  have iT4 : srlOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds srlOp hSrl
  have iT5 : srlOp.InBounds ctx₅.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation srlOp) hXor iT4
  have iT6 : srlOp.InBounds ctx₆.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation srlOp) hSltiu iT5
  have iT7 : srlOp.InBounds ctx₇.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation srlOp) hAddi iT6
  have iT8 : srlOp.InBounds ctx₈.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation srlOp) hOr iT7
  have iT9 : srlOp.InBounds ctx₉.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation srlOp) hCastBack iT8
  have iX5 : xorOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds xorOp hXor
  have iX6 : xorOp.InBounds ctx₆.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation xorOp) hSltiu iX5
  have iX7 : xorOp.InBounds ctx₇.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation xorOp) hAddi iX6
  have iX8 : xorOp.InBounds ctx₈.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation xorOp) hOr iX7
  have iX9 : xorOp.InBounds ctx₉.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation xorOp) hCastBack iX8
  have iU6 : sltiuOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds sltiuOp hSltiu
  have iU7 : sltiuOp.InBounds ctx₇.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation sltiuOp) hAddi iU6
  have iU8 : sltiuOp.InBounds ctx₈.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation sltiuOp) hOr iU7
  have iU9 : sltiuOp.InBounds ctx₉.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation sltiuOp) hCastBack iU8
  have iA7 : addiOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds addiOp hAddi
  have iA8 : addiOp.InBounds ctx₈.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation addiOp) hOr iA7
  have iA9 : addiOp.InBounds ctx₉.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation addiOp) hCastBack iA8
  have iO8 : orOp.InBounds ctx₈.raw := WfRewriter.createOp_new_inBounds orOp hOr
  have iO9 : orOp.InBounds ctx₉.raw := WfRewriter.createOp_inBounds_mono (ptr := .operation orOp) hCastBack iO8
  have iC9 : castBackOp.InBounds ctx₉.raw := WfRewriter.createOp_new_inBounds castBackOp hCastBack
  have fRc : ¬ rcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_not_inBounds rcastOp hRCast
  have fSll : ¬ sllOp.InBounds ctx₂.raw := WfRewriter.createOp_new_not_inBounds sllOp hSll
  have fSrl : ¬ srlOp.InBounds ctx₃.raw := WfRewriter.createOp_new_not_inBounds srlOp hSrl
  have fXor : ¬ xorOp.InBounds ctx₄.raw := WfRewriter.createOp_new_not_inBounds xorOp hXor
  have fSltiu : ¬ sltiuOp.InBounds ctx₅.raw := WfRewriter.createOp_new_not_inBounds sltiuOp hSltiu
  have fAddi : ¬ addiOp.InBounds ctx₆.raw := WfRewriter.createOp_new_not_inBounds addiOp hAddi
  have fOr : ¬ orOp.InBounds ctx₇.raw := WfRewriter.createOp_new_not_inBounds orOp hOr
  have fCb : ¬ castBackOp.InBounds ctx₈.raw := WfRewriter.createOp_new_not_inBounds castBackOp hCastBack
  -- Structural facts about the nine created ops (opcode/operand/result-type transports seeded
  -- explicitly through each op created afterwards).
  have hLCastType : lcastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSll (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSrl (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSltiu (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddi (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
  have hRCastType : rcastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSll (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSrl (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSltiu (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddi (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
  have hSllType : sllOp.getOpType! ctx₉.raw = .riscv .sll := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSll (operation := sllOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSrl (operation := sllOp),
      OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := sllOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSltiu (operation := sllOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddi (operation := sllOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := sllOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := sllOp)]
  have hSrlType : srlOp.getOpType! ctx₉.raw = .riscv .srl := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSrl (operation := srlOp),
      OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := srlOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSltiu (operation := srlOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddi (operation := srlOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := srlOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := srlOp)]
  have hXorType : xorOp.getOpType! ctx₉.raw = .riscv .xor := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := xorOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSltiu (operation := xorOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddi (operation := xorOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := xorOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := xorOp)]
  have hSltiuType : sltiuOp.getOpType! ctx₉.raw = .riscv .sltiu := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSltiu (operation := sltiuOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddi (operation := sltiuOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := sltiuOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := sltiuOp)]
  have hAddiType : addiOp.getOpType! ctx₉.raw = .riscv .addi := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAddi (operation := addiOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := addiOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := addiOp)]
  have hOrType : orOp.getOpType! ctx₉.raw = .riscv .or := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := orOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := orOp)]
  have hCastBackType : castBackOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hLCastOperands : lcastOp.getOperands! ctx₉.raw = #[lhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSll (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSrl (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSltiu (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddi (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
  have hRCastOperands : rcastOp.getOperands! ctx₉.raw = #[rhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSll (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSrl (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSltiu (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddi (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rcastOp)]
  have hSllOperands : sllOp.getOperands! ctx₉.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSll (operation := sllOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSrl (operation := sllOp),
      OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := sllOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSltiu (operation := sllOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddi (operation := sllOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := sllOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := sllOp)]
  have hSrlOperands : srlOp.getOperands! ctx₉.raw
      = #[ValuePtr.opResult (sllOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSrl (operation := srlOp),
      OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := srlOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSltiu (operation := srlOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddi (operation := srlOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := srlOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := srlOp)]
  have hXorOperands : xorOp.getOperands! ctx₉.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (srlOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := xorOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSltiu (operation := xorOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddi (operation := xorOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := xorOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xorOp)]
  have hSltiuOperands : sltiuOp.getOperands! ctx₉.raw
      = #[ValuePtr.opResult (xorOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSltiu (operation := sltiuOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddi (operation := sltiuOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := sltiuOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := sltiuOp)]
  have hAddiOperands : addiOp.getOperands! ctx₉.raw
      = #[ValuePtr.opResult (sltiuOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAddi (operation := addiOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := addiOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := addiOp)]
  have hOrOperands : orOp.getOperands! ctx₉.raw
      = #[ValuePtr.opResult (addiOp.getResult 0), ValuePtr.opResult (sllOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := orOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := orOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₉.raw = #[ValuePtr.opResult (orOp.getResult 0)] := by grind
  -- The `sltiu` immediate is `1`, the `addi` immediate is `-1`.
  have hSltiuProps : sltiuOp.getProperties! ctx₉.raw (.riscv .sltiu) = mkRISCVImm 1 := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hOr (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hAddi (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp hSltiu (operation := sltiuOp)]
    rw [if_pos rfl]; rfl
  have hSltiuImm : BitVec.ofInt 12 (sltiuOp.getProperties! ctx₉.raw (.riscv .sltiu)).value.value
      = BitVec.ofInt 12 1 := by rw [hSltiuProps]; simp [mkRISCVImm]
  have hAddiProps : addiOp.getProperties! ctx₉.raw (.riscv .addi) = mkRISCVImm (-1) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hOr (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp hAddi (operation := addiOp)]
    rw [if_pos rfl]; rfl
  have hAddiImm : BitVec.ofInt 12 (addiOp.getProperties! ctx₉.raw (.riscv .addi)).value.value
      = BitVec.ofInt 12 (-1) := by rw [hAddiProps]; simp [mkRISCVImm]
  -- The cast-back op's result type is the integer type `i64`.
  have hCBType : ((op.getResult 0).get! ctx₈.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₈.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hOr
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hAddi
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hSltiu
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hXor
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hSrl
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hSll
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hRCast
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hLCast
          (value := ValuePtr.opResult (op.getResult 0))]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hLCastResTypes : lcastOp.getResultTypes! ctx₉.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLCast (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSll (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSrl (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSltiu (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAddi (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lcastOp)]
  have hRCastResTypes : rcastOp.getResultTypes! ctx₉.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSll (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSrl (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSltiu (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAddi (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rcastOp)]
  have hSllResTypes : sllOp.getResultTypes! ctx₉.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSll (operation := sllOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSrl (operation := sllOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := sllOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSltiu (operation := sllOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAddi (operation := sllOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := sllOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := sllOp)]
  have hSrlResTypes : srlOp.getResultTypes! ctx₉.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSrl (operation := srlOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := srlOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSltiu (operation := srlOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAddi (operation := srlOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := srlOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := srlOp)]
  have hXorResTypes : xorOp.getResultTypes! ctx₉.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := xorOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSltiu (operation := xorOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAddi (operation := xorOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := xorOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xorOp)]
  have hSltiuResTypes : sltiuOp.getResultTypes! ctx₉.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSltiu (operation := sltiuOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAddi (operation := sltiuOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := sltiuOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := sltiuOp)]
  have hAddiResTypes : addiOp.getResultTypes! ctx₉.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hAddi (operation := addiOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := addiOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := addiOp)]
  have hOrResTypes : orOp.getResultTypes! ctx₉.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := orOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := orOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₉.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
  -- Interpretation tail: execute the nine-op list in `state'`. The frame clauses carry earlier
  -- register bindings across later steps, notably `lReg` (to `xor`) and `shifted` (to `or`).
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hLCastType hLCastOperands hLCastResTypes hLVal'
  have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₉.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₉.raw rhs lcastOp
      with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (hRhsNeLCastRes i)
  have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 64 yt) := by
    rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
      hRCastType hRCastOperands hRCastResTypes hRVal₁
  -- `sll` reads `lReg` (through the `rcast` step) and `rReg`.
  have hLCastNotRCastRes :
      ValuePtr.opResult (lcastOp.getResult 0) ∉ rcastOp.getResults! ctx₉.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₉.raw
        (ValuePtr.opResult (lcastOp.getResult 0)) rcastOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hLRes₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.sll r₂ r₁) (fun _ _ _ _ => rfl) hSllType hSllOperands
      hSllResTypes hLRes₂ hRes₂
  -- `srl` reads `shifted` and `rReg` (through the `sll` step).
  have hRCastNotSllRes :
      ValuePtr.opResult (rcastOp.getResult 0) ∉ sllOp.getResults! ctx₉.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₉.raw
        (ValuePtr.opResult (rcastOp.getResult 0)) sllOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hRRes₃ : s₃.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₃ _ hRCastNotSllRes]; exact hRes₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.srl r₂ r₁) (fun _ _ _ _ => rfl) hSrlType hSrlOperands
      hSrlResTypes hRes₃ hRRes₃
  -- `xor` reads `unshifted` and `lReg` (through the `sll` and `srl` steps).
  have hLCastNotSllRes :
      ValuePtr.opResult (lcastOp.getResult 0) ∉ sllOp.getResults! ctx₉.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₉.raw
        (ValuePtr.opResult (lcastOp.getResult 0)) sllOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hLCastNotSrlRes :
      ValuePtr.opResult (lcastOp.getResult 0) ∉ srlOp.getResults! ctx₉.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₉.raw
        (ValuePtr.opResult (lcastOp.getResult 0)) srlOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hLRes₄ : s₄.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₄ _ hLCastNotSrlRes, hFrame₃ _ hLCastNotSllRes]; exact hLRes₂
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₄) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.xor r₂ r₁) (fun _ _ _ _ => rfl) hXorType hXorOperands
      hXorResTypes hLRes₄ hRes₄
  -- `sltiu 1` reads `lostBits`.
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
    interpretOp_riscv_sltiu_forward (state := s₅) (inBounds := by grind)
      (k := BitVec.ofInt 12 1) hSltiuType hSltiuImm hSltiuOperands hSltiuResTypes hRes₅
  -- `addi -1` reads `noOverflow`.
  obtain ⟨s₇, hI₇, hMem₇, hRes₇, hFrame₇⟩ :=
    interpretOp_riscv_addi_forward (state := s₆) (inBounds := by grind)
      (k := BitVec.ofInt 12 (-1)) hAddiType hAddiImm hAddiOperands hAddiResTypes hRes₆
  -- `or` reads `overflowMask` and `shifted` (carried through the `srl`/`xor`/`sltiu`/`addi` steps).
  have hSllNotSrlRes :
      ValuePtr.opResult (sllOp.getResult 0) ∉ srlOp.getResults! ctx₉.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₉.raw
        (ValuePtr.opResult (sllOp.getResult 0)) srlOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hSllNotXorRes :
      ValuePtr.opResult (sllOp.getResult 0) ∉ xorOp.getResults! ctx₉.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₉.raw
        (ValuePtr.opResult (sllOp.getResult 0)) xorOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hSllNotSltiuRes :
      ValuePtr.opResult (sllOp.getResult 0) ∉ sltiuOp.getResults! ctx₉.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₉.raw
        (ValuePtr.opResult (sllOp.getResult 0)) sltiuOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hSllNotAddiRes :
      ValuePtr.opResult (sllOp.getResult 0) ∉ addiOp.getResults! ctx₉.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₉.raw
        (ValuePtr.opResult (sllOp.getResult 0)) addiOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hShifted₇ : s₇.variables.getVar? (ValuePtr.opResult (sllOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₇ _ hSllNotAddiRes, hFrame₆ _ hSllNotSltiuRes, hFrame₅ _ hSllNotXorRes,
      hFrame₄ _ hSllNotSrlRes]
    exact hRes₃
  obtain ⟨s₈, hI₈, hMem₈, hRes₈, hFrame₈⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₇) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl) hOrType hOrOperands
      hOrResTypes hRes₇ hShifted₇
  obtain ⟨s₉, hI₉, hMem₉, hRes₉, -⟩ :=
    interpretOp_castBack_forward (state := s₈) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₈
  refine ⟨s₉, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, hI₈, hI₉, liftM, monadLift,
      MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
        (Data.RISCV.or (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))
          (Data.RISCV.addi (BitVec.ofInt 12 (-1))
            (Data.RISCV.sltiu (BitVec.ofInt 12 1)
              (Data.RISCV.xor
                (Data.RISCV.srl (LLVM.Int.toReg yt)
                  (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
                (LLVM.Int.toReg xt))))) 64)], ?_, ?_⟩
    · simp [hRes₉, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using ushlSat_isRefinedBy_toInt hxtRef hytRef⟩

end Veir
