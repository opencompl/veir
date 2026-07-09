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
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBswap
import Veir.Passes.InstructionSelection.RewriteProofs.LowerConst

namespace Veir

/-!
## Correctness of `saddSat_local`

`llvm.intr.sadd.sat` on a 64-bit integer is lowered to LLVM's RV64+Zicond signed saturating-add
sequence.  Casting both operands to registers `X = toReg xt`, `Y = toReg yt`, it emits:
`sum = add X Y`, `rhsSign = srli 63 Y`, `carryLike = slt sum X` (i.e. `sum <s X`),
`sumSign = srai 63 sum`, `intMin = slli 63 (li -1)`, `overflow = xor rhsSign carryLike`,
`sat = xor sumSign intMin`, then the branchless select
`or (czeronez sum overflow) (czeroeqz sat overflow)` (`overflow ≠ 0 ? sat : sum`), cast back to the
integer type.

It is proven bespoke in the same shape as the sibling `uaddSat_local`/`usubSat_local` proofs, only
much longer: a two-operand `castToRegLocal`/`castToRegLocal` prefix followed by a twelve-op
straight-line register chain (`li`/`add`/`srli`/`slt`/`srai`/`slli`/`xor`/`xor`/`czeronez`/
`czeroeqz`/`or`) and the cast-back.  It is `i64`-only, so there is no bitwidth branch.
-/

/-- Forward-interpretation lemma for the immediate `riscv.srai`, mirroring
    `interpretOp_riscv_srli_forward`: the emitted register is `Data.RISCV.srai k r`, where `k` is the
    op's shift immediate (a `BitVec 6`). -/
theorem interpretOp_riscv_srai_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {r : Data.RISCV.Reg} {k : BitVec 6}
    (hType : theOp.getOpType! ctx.raw = .riscv .srai)
    (hImm : BitVec.ofInt 6 (theOp.getProperties! ctx.raw (.riscv .srai)).value.value = k)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (Data.RISCV.srai k r)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.reg (Data.RISCV.srai k r)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [interpretOp', Riscv.interpretOp', Interp, hImm, pure])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Forward-interpretation lemma for the immediate `riscv.slli`, mirroring
    `interpretOp_riscv_srli_forward`: the emitted register is `Data.RISCV.slli k r`. -/
theorem interpretOp_riscv_slli_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {r : Data.RISCV.Reg} {k : BitVec 6}
    (hType : theOp.getOpType! ctx.raw = .riscv .slli)
    (hImm : BitVec.ofInt 6 (theOp.getProperties! ctx.raw (.riscv .slli)).value.value = k)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (Data.RISCV.slli k r)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.reg (Data.RISCV.slli k r)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [interpretOp', Riscv.interpretOp', Interp, hImm, pure])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Correctness of the branchless signed saturating-add chain: the round trip
    `int × int → reg × reg → li/add/srli/slt/srai/slli/xor/xor/czeronez/czeroeqz/or → int` refines
    `sadd.sat`.  (`xt`/`yt` are the possibly-more-defined target-side values of the operands.) -/
theorem saddSat_isRefinedBy_toInt {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.saddSat x y ⊒
      RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.czeronez
            (Data.RISCV.xor
              (Data.RISCV.slt (LLVM.Int.toReg xt)
                (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt)))
            (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.czeroeqz
            (Data.RISCV.xor
              (Data.RISCV.slt (LLVM.Int.toReg xt)
                (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt)))
            (Data.RISCV.xor
              (Data.RISCV.slli (BitVec.ofInt 6 63) (Data.RISCV.li (BitVec.ofInt 64 (-1))))
              (Data.RISCV.srai (BitVec.ofInt 6 63)
                (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))))))
        64 := by
  revert h₁ h₂
  veir_bv_decide

set_option maxHeartbeats 4000000 in
/-- Correctness of the `saddSat_local` lowering: the twelve-op RV64+Zicond signed saturating-add
    chain refines `llvm.intr.sadd.sat`. -/
theorem saddSat_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics saddSat_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, saddSat_local, createRISCVUnitLocal,
    createRISCVImmLocal, signedSatSelectLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchSaddSat op ctx.raw).isSome := by
    cases hM : matchSaddSat op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSaddSat_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_intr__sadd__sat opVerif hOpType
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
  -- Unfold the interpretation of the matched op: exposes the operand values and their `saddSat`.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold
      (srcFn := fun {_} x y _ => Data.LLVM.Int.saddSat x y)
      (props := op.getProperties! ctx.raw (.llvm .intr__sadd__sat))
      opInBounds hOpType hNumResults hOperands rfl
      (fun bw x y props rt bo mem res h => by
        have hEq : Llvm.interpretOp' .intr__sadd__sat props rt #[.int bw x, .int bw y] bo mem
            = some (.ok (#[.int bw (Data.LLVM.Int.saddSat x y)], mem, none)) := by
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
  -- Source value: `op`'s single result is `saddSat` of its operands.
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
  -- Freshness facts, used to keep `lhs`/`rhs` alive across the casts.
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
  -- Peel the first three RISC-V ops (`li`/`add`/`srli`) with the macro (≤ 5 createOps deep).
  peelOpCreation!₂ hpattern ctx₃ oneOp hOne hDomL₂ hDomL₃ hDomR₂ hDomR₃
  peelOpCreation!₂ hpattern ctx₄ sumOp hSum hDomL₃ hDomL₄ hDomR₃ hDomR₄
  peelOpCreation!₂ hpattern ctx₅ rsOp hRs hDomL₄ hDomL₅ hDomR₄ hDomR₅
  -- From here on, `op.InBounds` reaches five-plus creations deep, so peel manually.
  have hOpIn₅ : op.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRs
      (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSum
        (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOne
          (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRCast
            (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLCast opInBounds))))
  -- `slt sum lReg`
  have ⟨⟨ctx₆, clOp⟩, hCl, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  dsimp only [] at hpattern hCl
  replace hCl := WfRewriter.createOp!_none_some hCl
  obtain ⟨_, _, _, hCl⟩ := hCl
  have hOpNeCl : op ≠ clOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds clOp hCl (heq ▸ hOpIn₅)
  have hDomL₆ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCl hOpIn₅ hOpNeCl).mpr hDomL₅
  have hDomR₆ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCl hOpIn₅ hOpNeCl).mpr hDomR₅
  have hOpIn₆ : op.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hCl hOpIn₅
  clear hOpNeCl hOpIn₅
  -- `srai 63 sum`
  have ⟨⟨ctx₇, ssOp⟩, hSs, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  dsimp only [] at hpattern hSs
  replace hSs := WfRewriter.createOp!_none_some hSs
  obtain ⟨_, _, _, hSs⟩ := hSs
  have hOpNeSs : op ≠ ssOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds ssOp hSs (heq ▸ hOpIn₆)
  have hDomL₇ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hSs hOpIn₆ hOpNeSs).mpr hDomL₆
  have hDomR₇ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hSs hOpIn₆ hOpNeSs).mpr hDomR₆
  have hOpIn₇ : op.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSs hOpIn₆
  clear hOpNeSs hOpIn₆
  -- `slli 63 one`
  have ⟨⟨ctx₈, imOp⟩, hIm, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  dsimp only [] at hpattern hIm
  replace hIm := WfRewriter.createOp!_none_some hIm
  obtain ⟨_, _, _, hIm⟩ := hIm
  have hOpNeIm : op ≠ imOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds imOp hIm (heq ▸ hOpIn₇)
  have hDomL₈ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hIm hOpIn₇ hOpNeIm).mpr hDomL₇
  have hDomR₈ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hIm hOpIn₇ hOpNeIm).mpr hDomR₇
  have hOpIn₈ : op.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hIm hOpIn₇
  clear hOpNeIm hOpIn₇
  -- `xor rs cl`
  have ⟨⟨ctx₉, ovOp⟩, hOv, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  dsimp only [] at hpattern hOv
  replace hOv := WfRewriter.createOp!_none_some hOv
  obtain ⟨_, _, _, hOv⟩ := hOv
  have hOpNeOv : op ≠ ovOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds ovOp hOv (heq ▸ hOpIn₈)
  have hDomL₉ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hOv hOpIn₈ hOpNeOv).mpr hDomL₈
  have hDomR₉ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hOv hOpIn₈ hOpNeOv).mpr hDomR₈
  have hOpIn₉ : op.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOv hOpIn₈
  clear hOpNeOv hOpIn₈
  -- `xor ss im`
  have ⟨⟨ctx₁₀, satOp⟩, hSat, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  dsimp only [] at hpattern hSat
  replace hSat := WfRewriter.createOp!_none_some hSat
  obtain ⟨_, _, _, hSat⟩ := hSat
  have hOpNeSat : op ≠ satOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds satOp hSat (heq ▸ hOpIn₉)
  have hDomL₁₀ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hSat hOpIn₉ hOpNeSat).mpr hDomL₉
  have hDomR₁₀ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hSat hOpIn₉ hOpNeSat).mpr hDomR₉
  have hOpIn₁₀ : op.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSat hOpIn₉
  clear hOpNeSat hOpIn₉
  -- `signedSatSelectLocal` is a *nested* `do` block returning `(ctx, ops, values)`, so its four
  -- creations sit under one extra existential. Open that first; `hFinal` records how the block's
  -- result feeds the pattern's return value, and is discharged after the inner peels.
  have ⟨⟨ctxSel, selOps, selVals⟩, hSelInner, hFinal⟩ := hpattern
  clear hpattern; have hpattern := hSelInner; clear hSelInner
  -- `czeronez sum ov`
  have ⟨⟨ctx₁₁, wozOp⟩, hWoz, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  dsimp only [] at hpattern hWoz
  replace hWoz := WfRewriter.createOp!_none_some hWoz
  obtain ⟨_, _, _, hWoz⟩ := hWoz
  have hOpNeWoz : op ≠ wozOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds wozOp hWoz (heq ▸ hOpIn₁₀)
  have hDomL₁₁ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hWoz hOpIn₁₀ hOpNeWoz).mpr hDomL₁₀
  have hDomR₁₁ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hWoz hOpIn₁₀ hOpNeWoz).mpr hDomR₁₀
  have hOpIn₁₁ : op.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hWoz hOpIn₁₀
  clear hOpNeWoz hOpIn₁₀
  -- `czeroeqz sat ov`
  have ⟨⟨ctx₁₂, sozOp⟩, hSoz, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  dsimp only [] at hpattern hSoz
  replace hSoz := WfRewriter.createOp!_none_some hSoz
  obtain ⟨_, _, _, hSoz⟩ := hSoz
  have hOpNeSoz : op ≠ sozOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds sozOp hSoz (heq ▸ hOpIn₁₁)
  have hDomL₁₂ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hSoz hOpIn₁₁ hOpNeSoz).mpr hDomL₁₁
  have hDomR₁₂ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hSoz hOpIn₁₁ hOpNeSoz).mpr hDomR₁₁
  have hOpIn₁₂ : op.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSoz hOpIn₁₁
  clear hOpNeSoz hOpIn₁₁
  -- `or soz woz`
  have ⟨⟨ctx₁₃, selOp⟩, hSel, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  dsimp only [] at hpattern hSel
  replace hSel := WfRewriter.createOp!_none_some hSel
  obtain ⟨_, _, _, hSel⟩ := hSel
  have hOpNeSel : op ≠ selOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds selOp hSel (heq ▸ hOpIn₁₂)
  have hDomL₁₃ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hSel hOpIn₁₂ hOpNeSel).mpr hDomL₁₂
  have hDomR₁₃ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hSel hOpIn₁₂ hOpNeSel).mpr hDomR₁₂
  have hOpIn₁₃ : op.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSel hOpIn₁₂
  clear hOpNeSel hOpIn₁₂
  -- cast-back (`replaceWithRegLocal op sel`)
  have ⟨⟨ctx₁₄, cbOp⟩, hCb, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  dsimp only [] at hpattern hCb
  simp only [replaceWithRegLocal] at hCb
  replace hCb := WfRewriter.createOp!_none_some hCb
  obtain ⟨_, _, _, hCb⟩ := hCb
  have hOpNeCb : op ≠ cbOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds cbOp hCb (heq ▸ hOpIn₁₃)
  have hDomL₁₄ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCb hOpIn₁₃ hOpNeCb).mpr hDomL₁₃
  have hDomR₁₄ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCb hOpIn₁₃ hOpNeCb).mpr hDomR₁₃
  clear hOpNeCb hOpIn₁₃
  -- `hpattern` now equates the select block's result with `(ctxSel, selOps, selVals)`; substituting
  -- it turns `hFinal` into the pattern's own return equation, which `cleanupHpattern` discharges.
  cleanupHpattern hpattern
  cleanupHpattern hFinal
  -- Read the refined values `xt`/`yt` of `lhs`/`rhs` in the target state `state'`.
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hxVal
      hDomCtxL hDomL₁₄ lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRhsIn hyVal
      hDomCtxR hDomR₁₄ rNotOp
  clear valueRefinement state'Wf state'Dom
    hDomL₁₄ hDomR₁₄ hDomL₁₃ hDomR₁₃ hDomL₁₂ hDomR₁₂ hDomL₁₁ hDomR₁₁ hDomL₁₀ hDomR₁₀
    hDomL₉ hDomR₉ hDomL₈ hDomR₈ hDomL₇ hDomR₇ hDomL₆ hDomR₆ hDomL₅ hDomR₅ hDomL₄ hDomR₄
    hDomL₃ hDomR₃ hDomL₂ hDomR₂ hDomL₁ hDomR₁
  obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
  -- Every created op stays in bounds in each later context, and each is fresh in its own creation
  -- context. Together these give `grind` the pairwise distinctness of all fourteen ops, which the
  -- property transports below need but `grind` cannot chain fourteen creations deep on its own;
  -- the `…ctx₁₄` facts also discharge the forward-interpretation `inBounds` obligations.
  have iOp1 : op.InBounds ctx₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLCast opInBounds
  have iOp2 : op.InBounds ctx₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRCast iOp1
  have iOp3 : op.InBounds ctx₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOne iOp2
  have iOp4 : op.InBounds ctx₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSum iOp3
  have iOp5 : op.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRs iOp4
  have iOp6 : op.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hCl iOp5
  have iOp7 : op.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSs iOp6
  have iOp8 : op.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hIm iOp7
  have iOp9 : op.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOv iOp8
  have iOp10 : op.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSat iOp9
  have iOp11 : op.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hWoz iOp10
  have iOp12 : op.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSoz iOp11
  have iOp13 : op.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSel iOp12
  have iOp14 : op.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hCb iOp13
  have i1_1 : lcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds lcastOp hLCast
  have i1_2 : lcastOp.InBounds ctx₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRCast i1_1
  have i1_3 : lcastOp.InBounds ctx₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hOne i1_2
  have i1_4 : lcastOp.InBounds ctx₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hSum i1_3
  have i1_5 : lcastOp.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRs i1_4
  have i1_6 : lcastOp.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hCl i1_5
  have i1_7 : lcastOp.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hSs i1_6
  have i1_8 : lcastOp.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hIm i1_7
  have i1_9 : lcastOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hOv i1_8
  have i1_10 : lcastOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hSat i1_9
  have i1_11 : lcastOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hWoz i1_10
  have i1_12 : lcastOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hSoz i1_11
  have i1_13 : lcastOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hSel i1_12
  have i1_14 : lcastOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hCb i1_13
  have i2_2 : rcastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds rcastOp hRCast
  have i2_3 : rcastOp.InBounds ctx₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hOne i2_2
  have i2_4 : rcastOp.InBounds ctx₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hSum i2_3
  have i2_5 : rcastOp.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hRs i2_4
  have i2_6 : rcastOp.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hCl i2_5
  have i2_7 : rcastOp.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hSs i2_6
  have i2_8 : rcastOp.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hIm i2_7
  have i2_9 : rcastOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hOv i2_8
  have i2_10 : rcastOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hSat i2_9
  have i2_11 : rcastOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hWoz i2_10
  have i2_12 : rcastOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hSoz i2_11
  have i2_13 : rcastOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hSel i2_12
  have i2_14 : rcastOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hCb i2_13
  have i3_3 : oneOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds oneOp hOne
  have i3_4 : oneOp.InBounds ctx₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hSum i3_3
  have i3_5 : oneOp.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hRs i3_4
  have i3_6 : oneOp.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hCl i3_5
  have i3_7 : oneOp.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hSs i3_6
  have i3_8 : oneOp.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hIm i3_7
  have i3_9 : oneOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hOv i3_8
  have i3_10 : oneOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hSat i3_9
  have i3_11 : oneOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hWoz i3_10
  have i3_12 : oneOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hSoz i3_11
  have i3_13 : oneOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hSel i3_12
  have i3_14 : oneOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation oneOp) hCb i3_13
  have i4_4 : sumOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds sumOp hSum
  have i4_5 : sumOp.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hRs i4_4
  have i4_6 : sumOp.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hCl i4_5
  have i4_7 : sumOp.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hSs i4_6
  have i4_8 : sumOp.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hIm i4_7
  have i4_9 : sumOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hOv i4_8
  have i4_10 : sumOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hSat i4_9
  have i4_11 : sumOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hWoz i4_10
  have i4_12 : sumOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hSoz i4_11
  have i4_13 : sumOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hSel i4_12
  have i4_14 : sumOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sumOp) hCb i4_13
  have i5_5 : rsOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds rsOp hRs
  have i5_6 : rsOp.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rsOp) hCl i5_5
  have i5_7 : rsOp.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rsOp) hSs i5_6
  have i5_8 : rsOp.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rsOp) hIm i5_7
  have i5_9 : rsOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rsOp) hOv i5_8
  have i5_10 : rsOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rsOp) hSat i5_9
  have i5_11 : rsOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rsOp) hWoz i5_10
  have i5_12 : rsOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rsOp) hSoz i5_11
  have i5_13 : rsOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rsOp) hSel i5_12
  have i5_14 : rsOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation rsOp) hCb i5_13
  have i6_6 : clOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds clOp hCl
  have i6_7 : clOp.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation clOp) hSs i6_6
  have i6_8 : clOp.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation clOp) hIm i6_7
  have i6_9 : clOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation clOp) hOv i6_8
  have i6_10 : clOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation clOp) hSat i6_9
  have i6_11 : clOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation clOp) hWoz i6_10
  have i6_12 : clOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation clOp) hSoz i6_11
  have i6_13 : clOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation clOp) hSel i6_12
  have i6_14 : clOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation clOp) hCb i6_13
  have i7_7 : ssOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds ssOp hSs
  have i7_8 : ssOp.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ssOp) hIm i7_7
  have i7_9 : ssOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ssOp) hOv i7_8
  have i7_10 : ssOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ssOp) hSat i7_9
  have i7_11 : ssOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ssOp) hWoz i7_10
  have i7_12 : ssOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ssOp) hSoz i7_11
  have i7_13 : ssOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ssOp) hSel i7_12
  have i7_14 : ssOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ssOp) hCb i7_13
  have i8_8 : imOp.InBounds ctx₈.raw := WfRewriter.createOp_new_inBounds imOp hIm
  have i8_9 : imOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation imOp) hOv i8_8
  have i8_10 : imOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation imOp) hSat i8_9
  have i8_11 : imOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation imOp) hWoz i8_10
  have i8_12 : imOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation imOp) hSoz i8_11
  have i8_13 : imOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation imOp) hSel i8_12
  have i8_14 : imOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation imOp) hCb i8_13
  have i9_9 : ovOp.InBounds ctx₉.raw := WfRewriter.createOp_new_inBounds ovOp hOv
  have i9_10 : ovOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ovOp) hSat i9_9
  have i9_11 : ovOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ovOp) hWoz i9_10
  have i9_12 : ovOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ovOp) hSoz i9_11
  have i9_13 : ovOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ovOp) hSel i9_12
  have i9_14 : ovOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation ovOp) hCb i9_13
  have i10_10 : satOp.InBounds ctx₁₀.raw := WfRewriter.createOp_new_inBounds satOp hSat
  have i10_11 : satOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation satOp) hWoz i10_10
  have i10_12 : satOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation satOp) hSoz i10_11
  have i10_13 : satOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation satOp) hSel i10_12
  have i10_14 : satOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation satOp) hCb i10_13
  have i11_11 : wozOp.InBounds ctx₁₁.raw := WfRewriter.createOp_new_inBounds wozOp hWoz
  have i11_12 : wozOp.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation wozOp) hSoz i11_11
  have i11_13 : wozOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation wozOp) hSel i11_12
  have i11_14 : wozOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation wozOp) hCb i11_13
  have i12_12 : sozOp.InBounds ctx₁₂.raw := WfRewriter.createOp_new_inBounds sozOp hSoz
  have i12_13 : sozOp.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sozOp) hSel i12_12
  have i12_14 : sozOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation sozOp) hCb i12_13
  have i13_13 : selOp.InBounds ctx₁₃.raw := WfRewriter.createOp_new_inBounds selOp hSel
  have i13_14 : selOp.InBounds ctx₁₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation selOp) hCb i13_13
  have i14_14 : cbOp.InBounds ctx₁₄.raw := WfRewriter.createOp_new_inBounds cbOp hCb
  have f2 : ¬ rcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_not_inBounds rcastOp hRCast
  have f3 : ¬ oneOp.InBounds ctx₂.raw := WfRewriter.createOp_new_not_inBounds oneOp hOne
  have f4 : ¬ sumOp.InBounds ctx₃.raw := WfRewriter.createOp_new_not_inBounds sumOp hSum
  have f5 : ¬ rsOp.InBounds ctx₄.raw := WfRewriter.createOp_new_not_inBounds rsOp hRs
  have f6 : ¬ clOp.InBounds ctx₅.raw := WfRewriter.createOp_new_not_inBounds clOp hCl
  have f7 : ¬ ssOp.InBounds ctx₆.raw := WfRewriter.createOp_new_not_inBounds ssOp hSs
  have f8 : ¬ imOp.InBounds ctx₇.raw := WfRewriter.createOp_new_not_inBounds imOp hIm
  have f9 : ¬ ovOp.InBounds ctx₈.raw := WfRewriter.createOp_new_not_inBounds ovOp hOv
  have f10 : ¬ satOp.InBounds ctx₉.raw := WfRewriter.createOp_new_not_inBounds satOp hSat
  have f11 : ¬ wozOp.InBounds ctx₁₀.raw := WfRewriter.createOp_new_not_inBounds wozOp hWoz
  have f12 : ¬ sozOp.InBounds ctx₁₁.raw := WfRewriter.createOp_new_not_inBounds sozOp hSoz
  have f13 : ¬ selOp.InBounds ctx₁₂.raw := WfRewriter.createOp_new_not_inBounds selOp hSel
  have f14 : ¬ cbOp.InBounds ctx₁₃.raw := WfRewriter.createOp_new_not_inBounds cbOp hCb
  -- Pairwise distinctness of the fourteen created ops: an earlier op is in bounds where a later
  -- op is still fresh. Stated explicitly (rather than left to `grind`) because the transports
  -- below need them as `if`-condition refutations inside `rw`.
  have hne1_2 : lcastOp ≠ rcastOp := fun hEq => f2 (hEq ▸ i1_1)
  have hne1_3 : lcastOp ≠ oneOp := fun hEq => f3 (hEq ▸ i1_2)
  have hne1_4 : lcastOp ≠ sumOp := fun hEq => f4 (hEq ▸ i1_3)
  have hne1_5 : lcastOp ≠ rsOp := fun hEq => f5 (hEq ▸ i1_4)
  have hne1_6 : lcastOp ≠ clOp := fun hEq => f6 (hEq ▸ i1_5)
  have hne1_7 : lcastOp ≠ ssOp := fun hEq => f7 (hEq ▸ i1_6)
  have hne1_8 : lcastOp ≠ imOp := fun hEq => f8 (hEq ▸ i1_7)
  have hne1_9 : lcastOp ≠ ovOp := fun hEq => f9 (hEq ▸ i1_8)
  have hne1_10 : lcastOp ≠ satOp := fun hEq => f10 (hEq ▸ i1_9)
  have hne1_11 : lcastOp ≠ wozOp := fun hEq => f11 (hEq ▸ i1_10)
  have hne1_12 : lcastOp ≠ sozOp := fun hEq => f12 (hEq ▸ i1_11)
  have hne1_13 : lcastOp ≠ selOp := fun hEq => f13 (hEq ▸ i1_12)
  have hne1_14 : lcastOp ≠ cbOp := fun hEq => f14 (hEq ▸ i1_13)
  have hne2_3 : rcastOp ≠ oneOp := fun hEq => f3 (hEq ▸ i2_2)
  have hne2_4 : rcastOp ≠ sumOp := fun hEq => f4 (hEq ▸ i2_3)
  have hne2_5 : rcastOp ≠ rsOp := fun hEq => f5 (hEq ▸ i2_4)
  have hne2_6 : rcastOp ≠ clOp := fun hEq => f6 (hEq ▸ i2_5)
  have hne2_7 : rcastOp ≠ ssOp := fun hEq => f7 (hEq ▸ i2_6)
  have hne2_8 : rcastOp ≠ imOp := fun hEq => f8 (hEq ▸ i2_7)
  have hne2_9 : rcastOp ≠ ovOp := fun hEq => f9 (hEq ▸ i2_8)
  have hne2_10 : rcastOp ≠ satOp := fun hEq => f10 (hEq ▸ i2_9)
  have hne2_11 : rcastOp ≠ wozOp := fun hEq => f11 (hEq ▸ i2_10)
  have hne2_12 : rcastOp ≠ sozOp := fun hEq => f12 (hEq ▸ i2_11)
  have hne2_13 : rcastOp ≠ selOp := fun hEq => f13 (hEq ▸ i2_12)
  have hne2_14 : rcastOp ≠ cbOp := fun hEq => f14 (hEq ▸ i2_13)
  have hne3_4 : oneOp ≠ sumOp := fun hEq => f4 (hEq ▸ i3_3)
  have hne3_5 : oneOp ≠ rsOp := fun hEq => f5 (hEq ▸ i3_4)
  have hne3_6 : oneOp ≠ clOp := fun hEq => f6 (hEq ▸ i3_5)
  have hne3_7 : oneOp ≠ ssOp := fun hEq => f7 (hEq ▸ i3_6)
  have hne3_8 : oneOp ≠ imOp := fun hEq => f8 (hEq ▸ i3_7)
  have hne3_9 : oneOp ≠ ovOp := fun hEq => f9 (hEq ▸ i3_8)
  have hne3_10 : oneOp ≠ satOp := fun hEq => f10 (hEq ▸ i3_9)
  have hne3_11 : oneOp ≠ wozOp := fun hEq => f11 (hEq ▸ i3_10)
  have hne3_12 : oneOp ≠ sozOp := fun hEq => f12 (hEq ▸ i3_11)
  have hne3_13 : oneOp ≠ selOp := fun hEq => f13 (hEq ▸ i3_12)
  have hne3_14 : oneOp ≠ cbOp := fun hEq => f14 (hEq ▸ i3_13)
  have hne4_5 : sumOp ≠ rsOp := fun hEq => f5 (hEq ▸ i4_4)
  have hne4_6 : sumOp ≠ clOp := fun hEq => f6 (hEq ▸ i4_5)
  have hne4_7 : sumOp ≠ ssOp := fun hEq => f7 (hEq ▸ i4_6)
  have hne4_8 : sumOp ≠ imOp := fun hEq => f8 (hEq ▸ i4_7)
  have hne4_9 : sumOp ≠ ovOp := fun hEq => f9 (hEq ▸ i4_8)
  have hne4_10 : sumOp ≠ satOp := fun hEq => f10 (hEq ▸ i4_9)
  have hne4_11 : sumOp ≠ wozOp := fun hEq => f11 (hEq ▸ i4_10)
  have hne4_12 : sumOp ≠ sozOp := fun hEq => f12 (hEq ▸ i4_11)
  have hne4_13 : sumOp ≠ selOp := fun hEq => f13 (hEq ▸ i4_12)
  have hne4_14 : sumOp ≠ cbOp := fun hEq => f14 (hEq ▸ i4_13)
  have hne5_6 : rsOp ≠ clOp := fun hEq => f6 (hEq ▸ i5_5)
  have hne5_7 : rsOp ≠ ssOp := fun hEq => f7 (hEq ▸ i5_6)
  have hne5_8 : rsOp ≠ imOp := fun hEq => f8 (hEq ▸ i5_7)
  have hne5_9 : rsOp ≠ ovOp := fun hEq => f9 (hEq ▸ i5_8)
  have hne5_10 : rsOp ≠ satOp := fun hEq => f10 (hEq ▸ i5_9)
  have hne5_11 : rsOp ≠ wozOp := fun hEq => f11 (hEq ▸ i5_10)
  have hne5_12 : rsOp ≠ sozOp := fun hEq => f12 (hEq ▸ i5_11)
  have hne5_13 : rsOp ≠ selOp := fun hEq => f13 (hEq ▸ i5_12)
  have hne5_14 : rsOp ≠ cbOp := fun hEq => f14 (hEq ▸ i5_13)
  have hne6_7 : clOp ≠ ssOp := fun hEq => f7 (hEq ▸ i6_6)
  have hne6_8 : clOp ≠ imOp := fun hEq => f8 (hEq ▸ i6_7)
  have hne6_9 : clOp ≠ ovOp := fun hEq => f9 (hEq ▸ i6_8)
  have hne6_10 : clOp ≠ satOp := fun hEq => f10 (hEq ▸ i6_9)
  have hne6_11 : clOp ≠ wozOp := fun hEq => f11 (hEq ▸ i6_10)
  have hne6_12 : clOp ≠ sozOp := fun hEq => f12 (hEq ▸ i6_11)
  have hne6_13 : clOp ≠ selOp := fun hEq => f13 (hEq ▸ i6_12)
  have hne6_14 : clOp ≠ cbOp := fun hEq => f14 (hEq ▸ i6_13)
  have hne7_8 : ssOp ≠ imOp := fun hEq => f8 (hEq ▸ i7_7)
  have hne7_9 : ssOp ≠ ovOp := fun hEq => f9 (hEq ▸ i7_8)
  have hne7_10 : ssOp ≠ satOp := fun hEq => f10 (hEq ▸ i7_9)
  have hne7_11 : ssOp ≠ wozOp := fun hEq => f11 (hEq ▸ i7_10)
  have hne7_12 : ssOp ≠ sozOp := fun hEq => f12 (hEq ▸ i7_11)
  have hne7_13 : ssOp ≠ selOp := fun hEq => f13 (hEq ▸ i7_12)
  have hne7_14 : ssOp ≠ cbOp := fun hEq => f14 (hEq ▸ i7_13)
  have hne8_9 : imOp ≠ ovOp := fun hEq => f9 (hEq ▸ i8_8)
  have hne8_10 : imOp ≠ satOp := fun hEq => f10 (hEq ▸ i8_9)
  have hne8_11 : imOp ≠ wozOp := fun hEq => f11 (hEq ▸ i8_10)
  have hne8_12 : imOp ≠ sozOp := fun hEq => f12 (hEq ▸ i8_11)
  have hne8_13 : imOp ≠ selOp := fun hEq => f13 (hEq ▸ i8_12)
  have hne8_14 : imOp ≠ cbOp := fun hEq => f14 (hEq ▸ i8_13)
  have hne9_10 : ovOp ≠ satOp := fun hEq => f10 (hEq ▸ i9_9)
  have hne9_11 : ovOp ≠ wozOp := fun hEq => f11 (hEq ▸ i9_10)
  have hne9_12 : ovOp ≠ sozOp := fun hEq => f12 (hEq ▸ i9_11)
  have hne9_13 : ovOp ≠ selOp := fun hEq => f13 (hEq ▸ i9_12)
  have hne9_14 : ovOp ≠ cbOp := fun hEq => f14 (hEq ▸ i9_13)
  have hne10_11 : satOp ≠ wozOp := fun hEq => f11 (hEq ▸ i10_10)
  have hne10_12 : satOp ≠ sozOp := fun hEq => f12 (hEq ▸ i10_11)
  have hne10_13 : satOp ≠ selOp := fun hEq => f13 (hEq ▸ i10_12)
  have hne10_14 : satOp ≠ cbOp := fun hEq => f14 (hEq ▸ i10_13)
  have hne11_12 : wozOp ≠ sozOp := fun hEq => f12 (hEq ▸ i11_11)
  have hne11_13 : wozOp ≠ selOp := fun hEq => f13 (hEq ▸ i11_12)
  have hne11_14 : wozOp ≠ cbOp := fun hEq => f14 (hEq ▸ i11_13)
  have hne12_13 : sozOp ≠ selOp := fun hEq => f13 (hEq ▸ i12_12)
  have hne12_14 : sozOp ≠ cbOp := fun hEq => f14 (hEq ▸ i12_13)
  have hne13_14 : selOp ≠ cbOp := fun hEq => f14 (hEq ▸ i13_13)
  -- Structural facts about the fourteen created ops. Each is transported from the op's own
  -- creation context up to `ctx₁₄` by rewriting through every later `createOp`, discharging the
  -- `operation = newOp` test with the distinctness facts above.
  have hLCastType : lcastOp.getOpType! ctx₁₄.raw = .builtin .unrealized_conversion_cast := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := lcastOp),
      if_neg hne1_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := lcastOp),
      if_neg hne1_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := lcastOp),
      if_neg hne1_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := lcastOp),
      if_neg hne1_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := lcastOp),
      if_neg hne1_10,
      OperationPtr.getOpType!_WfRewriter_createOp hOv (operation := lcastOp),
      if_neg hne1_9,
      OperationPtr.getOpType!_WfRewriter_createOp hIm (operation := lcastOp),
      if_neg hne1_8,
      OperationPtr.getOpType!_WfRewriter_createOp hSs (operation := lcastOp),
      if_neg hne1_7,
      OperationPtr.getOpType!_WfRewriter_createOp hCl (operation := lcastOp),
      if_neg hne1_6,
      OperationPtr.getOpType!_WfRewriter_createOp hRs (operation := lcastOp),
      if_neg hne1_5,
      OperationPtr.getOpType!_WfRewriter_createOp hSum (operation := lcastOp),
      if_neg hne1_4,
      OperationPtr.getOpType!_WfRewriter_createOp hOne (operation := lcastOp),
      if_neg hne1_3,
      OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
      if_neg hne1_2,
      OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp), if_pos rfl]
  have hRCastType : rcastOp.getOpType! ctx₁₄.raw = .builtin .unrealized_conversion_cast := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := rcastOp),
      if_neg hne2_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := rcastOp),
      if_neg hne2_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := rcastOp),
      if_neg hne2_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := rcastOp),
      if_neg hne2_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := rcastOp),
      if_neg hne2_10,
      OperationPtr.getOpType!_WfRewriter_createOp hOv (operation := rcastOp),
      if_neg hne2_9,
      OperationPtr.getOpType!_WfRewriter_createOp hIm (operation := rcastOp),
      if_neg hne2_8,
      OperationPtr.getOpType!_WfRewriter_createOp hSs (operation := rcastOp),
      if_neg hne2_7,
      OperationPtr.getOpType!_WfRewriter_createOp hCl (operation := rcastOp),
      if_neg hne2_6,
      OperationPtr.getOpType!_WfRewriter_createOp hRs (operation := rcastOp),
      if_neg hne2_5,
      OperationPtr.getOpType!_WfRewriter_createOp hSum (operation := rcastOp),
      if_neg hne2_4,
      OperationPtr.getOpType!_WfRewriter_createOp hOne (operation := rcastOp),
      if_neg hne2_3,
      OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp), if_pos rfl]
  have hOneType : oneOp.getOpType! ctx₁₄.raw = .riscv .li := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := oneOp),
      if_neg hne3_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := oneOp),
      if_neg hne3_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := oneOp),
      if_neg hne3_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := oneOp),
      if_neg hne3_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := oneOp),
      if_neg hne3_10,
      OperationPtr.getOpType!_WfRewriter_createOp hOv (operation := oneOp),
      if_neg hne3_9,
      OperationPtr.getOpType!_WfRewriter_createOp hIm (operation := oneOp),
      if_neg hne3_8,
      OperationPtr.getOpType!_WfRewriter_createOp hSs (operation := oneOp),
      if_neg hne3_7,
      OperationPtr.getOpType!_WfRewriter_createOp hCl (operation := oneOp),
      if_neg hne3_6,
      OperationPtr.getOpType!_WfRewriter_createOp hRs (operation := oneOp),
      if_neg hne3_5,
      OperationPtr.getOpType!_WfRewriter_createOp hSum (operation := oneOp),
      if_neg hne3_4,
      OperationPtr.getOpType!_WfRewriter_createOp hOne (operation := oneOp), if_pos rfl]
  have hSumType : sumOp.getOpType! ctx₁₄.raw = .riscv .add := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := sumOp),
      if_neg hne4_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := sumOp),
      if_neg hne4_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := sumOp),
      if_neg hne4_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := sumOp),
      if_neg hne4_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := sumOp),
      if_neg hne4_10,
      OperationPtr.getOpType!_WfRewriter_createOp hOv (operation := sumOp),
      if_neg hne4_9,
      OperationPtr.getOpType!_WfRewriter_createOp hIm (operation := sumOp),
      if_neg hne4_8,
      OperationPtr.getOpType!_WfRewriter_createOp hSs (operation := sumOp),
      if_neg hne4_7,
      OperationPtr.getOpType!_WfRewriter_createOp hCl (operation := sumOp),
      if_neg hne4_6,
      OperationPtr.getOpType!_WfRewriter_createOp hRs (operation := sumOp),
      if_neg hne4_5,
      OperationPtr.getOpType!_WfRewriter_createOp hSum (operation := sumOp), if_pos rfl]
  have hRsType : rsOp.getOpType! ctx₁₄.raw = .riscv .srli := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := rsOp),
      if_neg hne5_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := rsOp),
      if_neg hne5_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := rsOp),
      if_neg hne5_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := rsOp),
      if_neg hne5_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := rsOp),
      if_neg hne5_10,
      OperationPtr.getOpType!_WfRewriter_createOp hOv (operation := rsOp),
      if_neg hne5_9,
      OperationPtr.getOpType!_WfRewriter_createOp hIm (operation := rsOp),
      if_neg hne5_8,
      OperationPtr.getOpType!_WfRewriter_createOp hSs (operation := rsOp),
      if_neg hne5_7,
      OperationPtr.getOpType!_WfRewriter_createOp hCl (operation := rsOp),
      if_neg hne5_6,
      OperationPtr.getOpType!_WfRewriter_createOp hRs (operation := rsOp), if_pos rfl]
  have hClType : clOp.getOpType! ctx₁₄.raw = .riscv .slt := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := clOp),
      if_neg hne6_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := clOp),
      if_neg hne6_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := clOp),
      if_neg hne6_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := clOp),
      if_neg hne6_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := clOp),
      if_neg hne6_10,
      OperationPtr.getOpType!_WfRewriter_createOp hOv (operation := clOp),
      if_neg hne6_9,
      OperationPtr.getOpType!_WfRewriter_createOp hIm (operation := clOp),
      if_neg hne6_8,
      OperationPtr.getOpType!_WfRewriter_createOp hSs (operation := clOp),
      if_neg hne6_7,
      OperationPtr.getOpType!_WfRewriter_createOp hCl (operation := clOp), if_pos rfl]
  have hSsType : ssOp.getOpType! ctx₁₄.raw = .riscv .srai := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := ssOp),
      if_neg hne7_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := ssOp),
      if_neg hne7_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := ssOp),
      if_neg hne7_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := ssOp),
      if_neg hne7_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := ssOp),
      if_neg hne7_10,
      OperationPtr.getOpType!_WfRewriter_createOp hOv (operation := ssOp),
      if_neg hne7_9,
      OperationPtr.getOpType!_WfRewriter_createOp hIm (operation := ssOp),
      if_neg hne7_8,
      OperationPtr.getOpType!_WfRewriter_createOp hSs (operation := ssOp), if_pos rfl]
  have hImType : imOp.getOpType! ctx₁₄.raw = .riscv .slli := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := imOp),
      if_neg hne8_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := imOp),
      if_neg hne8_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := imOp),
      if_neg hne8_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := imOp),
      if_neg hne8_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := imOp),
      if_neg hne8_10,
      OperationPtr.getOpType!_WfRewriter_createOp hOv (operation := imOp),
      if_neg hne8_9,
      OperationPtr.getOpType!_WfRewriter_createOp hIm (operation := imOp), if_pos rfl]
  have hOvType : ovOp.getOpType! ctx₁₄.raw = .riscv .xor := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := ovOp),
      if_neg hne9_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := ovOp),
      if_neg hne9_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := ovOp),
      if_neg hne9_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := ovOp),
      if_neg hne9_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := ovOp),
      if_neg hne9_10,
      OperationPtr.getOpType!_WfRewriter_createOp hOv (operation := ovOp), if_pos rfl]
  have hSatType : satOp.getOpType! ctx₁₄.raw = .riscv .xor := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := satOp),
      if_neg hne10_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := satOp),
      if_neg hne10_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := satOp),
      if_neg hne10_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := satOp),
      if_neg hne10_11,
      OperationPtr.getOpType!_WfRewriter_createOp hSat (operation := satOp), if_pos rfl]
  have hWozType : wozOp.getOpType! ctx₁₄.raw = .riscv .czeronez := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := wozOp),
      if_neg hne11_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := wozOp),
      if_neg hne11_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := wozOp),
      if_neg hne11_12,
      OperationPtr.getOpType!_WfRewriter_createOp hWoz (operation := wozOp), if_pos rfl]
  have hSozType : sozOp.getOpType! ctx₁₄.raw = .riscv .czeroeqz := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := sozOp),
      if_neg hne12_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := sozOp),
      if_neg hne12_13,
      OperationPtr.getOpType!_WfRewriter_createOp hSoz (operation := sozOp), if_pos rfl]
  have hSelType : selOp.getOpType! ctx₁₄.raw = .riscv .or := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := selOp),
      if_neg hne13_14,
      OperationPtr.getOpType!_WfRewriter_createOp hSel (operation := selOp), if_pos rfl]
  have hCbType : cbOp.getOpType! ctx₁₄.raw = .builtin .unrealized_conversion_cast := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCb (operation := cbOp), if_pos rfl]
  have hLCastOperands : lcastOp.getOperands! ctx₁₄.raw
      = #[lhs] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := lcastOp),
      if_neg hne1_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := lcastOp),
      if_neg hne1_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := lcastOp),
      if_neg hne1_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := lcastOp),
      if_neg hne1_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := lcastOp),
      if_neg hne1_10,
      OperationPtr.getOperands!_WfRewriter_createOp hOv (operation := lcastOp),
      if_neg hne1_9,
      OperationPtr.getOperands!_WfRewriter_createOp hIm (operation := lcastOp),
      if_neg hne1_8,
      OperationPtr.getOperands!_WfRewriter_createOp hSs (operation := lcastOp),
      if_neg hne1_7,
      OperationPtr.getOperands!_WfRewriter_createOp hCl (operation := lcastOp),
      if_neg hne1_6,
      OperationPtr.getOperands!_WfRewriter_createOp hRs (operation := lcastOp),
      if_neg hne1_5,
      OperationPtr.getOperands!_WfRewriter_createOp hSum (operation := lcastOp),
      if_neg hne1_4,
      OperationPtr.getOperands!_WfRewriter_createOp hOne (operation := lcastOp),
      if_neg hne1_3,
      OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
      if_neg hne1_2,
      OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp), if_pos rfl]
  have hRCastOperands : rcastOp.getOperands! ctx₁₄.raw
      = #[rhs] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := rcastOp),
      if_neg hne2_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := rcastOp),
      if_neg hne2_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := rcastOp),
      if_neg hne2_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := rcastOp),
      if_neg hne2_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := rcastOp),
      if_neg hne2_10,
      OperationPtr.getOperands!_WfRewriter_createOp hOv (operation := rcastOp),
      if_neg hne2_9,
      OperationPtr.getOperands!_WfRewriter_createOp hIm (operation := rcastOp),
      if_neg hne2_8,
      OperationPtr.getOperands!_WfRewriter_createOp hSs (operation := rcastOp),
      if_neg hne2_7,
      OperationPtr.getOperands!_WfRewriter_createOp hCl (operation := rcastOp),
      if_neg hne2_6,
      OperationPtr.getOperands!_WfRewriter_createOp hRs (operation := rcastOp),
      if_neg hne2_5,
      OperationPtr.getOperands!_WfRewriter_createOp hSum (operation := rcastOp),
      if_neg hne2_4,
      OperationPtr.getOperands!_WfRewriter_createOp hOne (operation := rcastOp),
      if_neg hne2_3,
      OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := rcastOp), if_pos rfl]
  have hOneOperands : oneOp.getOperands! ctx₁₄.raw
      = #[] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := oneOp),
      if_neg hne3_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := oneOp),
      if_neg hne3_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := oneOp),
      if_neg hne3_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := oneOp),
      if_neg hne3_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := oneOp),
      if_neg hne3_10,
      OperationPtr.getOperands!_WfRewriter_createOp hOv (operation := oneOp),
      if_neg hne3_9,
      OperationPtr.getOperands!_WfRewriter_createOp hIm (operation := oneOp),
      if_neg hne3_8,
      OperationPtr.getOperands!_WfRewriter_createOp hSs (operation := oneOp),
      if_neg hne3_7,
      OperationPtr.getOperands!_WfRewriter_createOp hCl (operation := oneOp),
      if_neg hne3_6,
      OperationPtr.getOperands!_WfRewriter_createOp hRs (operation := oneOp),
      if_neg hne3_5,
      OperationPtr.getOperands!_WfRewriter_createOp hSum (operation := oneOp),
      if_neg hne3_4,
      OperationPtr.getOperands!_WfRewriter_createOp hOne (operation := oneOp), if_pos rfl]
  have hSumOperands : sumOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := sumOp),
      if_neg hne4_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := sumOp),
      if_neg hne4_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := sumOp),
      if_neg hne4_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := sumOp),
      if_neg hne4_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := sumOp),
      if_neg hne4_10,
      OperationPtr.getOperands!_WfRewriter_createOp hOv (operation := sumOp),
      if_neg hne4_9,
      OperationPtr.getOperands!_WfRewriter_createOp hIm (operation := sumOp),
      if_neg hne4_8,
      OperationPtr.getOperands!_WfRewriter_createOp hSs (operation := sumOp),
      if_neg hne4_7,
      OperationPtr.getOperands!_WfRewriter_createOp hCl (operation := sumOp),
      if_neg hne4_6,
      OperationPtr.getOperands!_WfRewriter_createOp hRs (operation := sumOp),
      if_neg hne4_5,
      OperationPtr.getOperands!_WfRewriter_createOp hSum (operation := sumOp), if_pos rfl]
  have hRsOperands : rsOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (rcastOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := rsOp),
      if_neg hne5_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := rsOp),
      if_neg hne5_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := rsOp),
      if_neg hne5_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := rsOp),
      if_neg hne5_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := rsOp),
      if_neg hne5_10,
      OperationPtr.getOperands!_WfRewriter_createOp hOv (operation := rsOp),
      if_neg hne5_9,
      OperationPtr.getOperands!_WfRewriter_createOp hIm (operation := rsOp),
      if_neg hne5_8,
      OperationPtr.getOperands!_WfRewriter_createOp hSs (operation := rsOp),
      if_neg hne5_7,
      OperationPtr.getOperands!_WfRewriter_createOp hCl (operation := rsOp),
      if_neg hne5_6,
      OperationPtr.getOperands!_WfRewriter_createOp hRs (operation := rsOp), if_pos rfl]
  have hClOperands : clOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (sumOp.getResult 0), ValuePtr.opResult (lcastOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := clOp),
      if_neg hne6_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := clOp),
      if_neg hne6_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := clOp),
      if_neg hne6_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := clOp),
      if_neg hne6_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := clOp),
      if_neg hne6_10,
      OperationPtr.getOperands!_WfRewriter_createOp hOv (operation := clOp),
      if_neg hne6_9,
      OperationPtr.getOperands!_WfRewriter_createOp hIm (operation := clOp),
      if_neg hne6_8,
      OperationPtr.getOperands!_WfRewriter_createOp hSs (operation := clOp),
      if_neg hne6_7,
      OperationPtr.getOperands!_WfRewriter_createOp hCl (operation := clOp), if_pos rfl]
  have hSsOperands : ssOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (sumOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := ssOp),
      if_neg hne7_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := ssOp),
      if_neg hne7_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := ssOp),
      if_neg hne7_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := ssOp),
      if_neg hne7_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := ssOp),
      if_neg hne7_10,
      OperationPtr.getOperands!_WfRewriter_createOp hOv (operation := ssOp),
      if_neg hne7_9,
      OperationPtr.getOperands!_WfRewriter_createOp hIm (operation := ssOp),
      if_neg hne7_8,
      OperationPtr.getOperands!_WfRewriter_createOp hSs (operation := ssOp), if_pos rfl]
  have hImOperands : imOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (oneOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := imOp),
      if_neg hne8_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := imOp),
      if_neg hne8_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := imOp),
      if_neg hne8_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := imOp),
      if_neg hne8_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := imOp),
      if_neg hne8_10,
      OperationPtr.getOperands!_WfRewriter_createOp hOv (operation := imOp),
      if_neg hne8_9,
      OperationPtr.getOperands!_WfRewriter_createOp hIm (operation := imOp), if_pos rfl]
  have hOvOperands : ovOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (rsOp.getResult 0), ValuePtr.opResult (clOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := ovOp),
      if_neg hne9_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := ovOp),
      if_neg hne9_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := ovOp),
      if_neg hne9_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := ovOp),
      if_neg hne9_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := ovOp),
      if_neg hne9_10,
      OperationPtr.getOperands!_WfRewriter_createOp hOv (operation := ovOp), if_pos rfl]
  have hSatOperands : satOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (ssOp.getResult 0), ValuePtr.opResult (imOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := satOp),
      if_neg hne10_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := satOp),
      if_neg hne10_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := satOp),
      if_neg hne10_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := satOp),
      if_neg hne10_11,
      OperationPtr.getOperands!_WfRewriter_createOp hSat (operation := satOp), if_pos rfl]
  have hWozOperands : wozOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (sumOp.getResult 0), ValuePtr.opResult (ovOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := wozOp),
      if_neg hne11_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := wozOp),
      if_neg hne11_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := wozOp),
      if_neg hne11_12,
      OperationPtr.getOperands!_WfRewriter_createOp hWoz (operation := wozOp), if_pos rfl]
  have hSozOperands : sozOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (satOp.getResult 0), ValuePtr.opResult (ovOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := sozOp),
      if_neg hne12_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := sozOp),
      if_neg hne12_13,
      OperationPtr.getOperands!_WfRewriter_createOp hSoz (operation := sozOp), if_pos rfl]
  have hSelOperands : selOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (sozOp.getResult 0), ValuePtr.opResult (wozOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := selOp),
      if_neg hne13_14,
      OperationPtr.getOperands!_WfRewriter_createOp hSel (operation := selOp), if_pos rfl]
  have hCbOperands : cbOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (selOp.getResult 0)] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCb (operation := cbOp), if_pos rfl]
  have hLCastResTypes : lcastOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := lcastOp),
      if_neg hne1_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := lcastOp),
      if_neg hne1_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := lcastOp),
      if_neg hne1_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := lcastOp),
      if_neg hne1_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := lcastOp),
      if_neg hne1_10,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOv (operation := lcastOp),
      if_neg hne1_9,
      OperationPtr.getResultTypes!_WfRewriter_createOp hIm (operation := lcastOp),
      if_neg hne1_8,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSs (operation := lcastOp),
      if_neg hne1_7,
      OperationPtr.getResultTypes!_WfRewriter_createOp hCl (operation := lcastOp),
      if_neg hne1_6,
      OperationPtr.getResultTypes!_WfRewriter_createOp hRs (operation := lcastOp),
      if_neg hne1_5,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSum (operation := lcastOp),
      if_neg hne1_4,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOne (operation := lcastOp),
      if_neg hne1_3,
      OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := lcastOp),
      if_neg hne1_2,
      OperationPtr.getResultTypes!_WfRewriter_createOp hLCast (operation := lcastOp), if_pos rfl]
  have hRCastResTypes : rcastOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := rcastOp),
      if_neg hne2_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := rcastOp),
      if_neg hne2_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := rcastOp),
      if_neg hne2_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := rcastOp),
      if_neg hne2_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := rcastOp),
      if_neg hne2_10,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOv (operation := rcastOp),
      if_neg hne2_9,
      OperationPtr.getResultTypes!_WfRewriter_createOp hIm (operation := rcastOp),
      if_neg hne2_8,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSs (operation := rcastOp),
      if_neg hne2_7,
      OperationPtr.getResultTypes!_WfRewriter_createOp hCl (operation := rcastOp),
      if_neg hne2_6,
      OperationPtr.getResultTypes!_WfRewriter_createOp hRs (operation := rcastOp),
      if_neg hne2_5,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSum (operation := rcastOp),
      if_neg hne2_4,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOne (operation := rcastOp),
      if_neg hne2_3,
      OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := rcastOp), if_pos rfl]
  have hOneResTypes : oneOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := oneOp),
      if_neg hne3_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := oneOp),
      if_neg hne3_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := oneOp),
      if_neg hne3_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := oneOp),
      if_neg hne3_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := oneOp),
      if_neg hne3_10,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOv (operation := oneOp),
      if_neg hne3_9,
      OperationPtr.getResultTypes!_WfRewriter_createOp hIm (operation := oneOp),
      if_neg hne3_8,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSs (operation := oneOp),
      if_neg hne3_7,
      OperationPtr.getResultTypes!_WfRewriter_createOp hCl (operation := oneOp),
      if_neg hne3_6,
      OperationPtr.getResultTypes!_WfRewriter_createOp hRs (operation := oneOp),
      if_neg hne3_5,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSum (operation := oneOp),
      if_neg hne3_4,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOne (operation := oneOp), if_pos rfl]
  have hSumResTypes : sumOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := sumOp),
      if_neg hne4_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := sumOp),
      if_neg hne4_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := sumOp),
      if_neg hne4_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := sumOp),
      if_neg hne4_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := sumOp),
      if_neg hne4_10,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOv (operation := sumOp),
      if_neg hne4_9,
      OperationPtr.getResultTypes!_WfRewriter_createOp hIm (operation := sumOp),
      if_neg hne4_8,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSs (operation := sumOp),
      if_neg hne4_7,
      OperationPtr.getResultTypes!_WfRewriter_createOp hCl (operation := sumOp),
      if_neg hne4_6,
      OperationPtr.getResultTypes!_WfRewriter_createOp hRs (operation := sumOp),
      if_neg hne4_5,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSum (operation := sumOp), if_pos rfl]
  have hRsResTypes : rsOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := rsOp),
      if_neg hne5_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := rsOp),
      if_neg hne5_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := rsOp),
      if_neg hne5_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := rsOp),
      if_neg hne5_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := rsOp),
      if_neg hne5_10,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOv (operation := rsOp),
      if_neg hne5_9,
      OperationPtr.getResultTypes!_WfRewriter_createOp hIm (operation := rsOp),
      if_neg hne5_8,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSs (operation := rsOp),
      if_neg hne5_7,
      OperationPtr.getResultTypes!_WfRewriter_createOp hCl (operation := rsOp),
      if_neg hne5_6,
      OperationPtr.getResultTypes!_WfRewriter_createOp hRs (operation := rsOp), if_pos rfl]
  have hClResTypes : clOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := clOp),
      if_neg hne6_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := clOp),
      if_neg hne6_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := clOp),
      if_neg hne6_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := clOp),
      if_neg hne6_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := clOp),
      if_neg hne6_10,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOv (operation := clOp),
      if_neg hne6_9,
      OperationPtr.getResultTypes!_WfRewriter_createOp hIm (operation := clOp),
      if_neg hne6_8,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSs (operation := clOp),
      if_neg hne6_7,
      OperationPtr.getResultTypes!_WfRewriter_createOp hCl (operation := clOp), if_pos rfl]
  have hSsResTypes : ssOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := ssOp),
      if_neg hne7_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := ssOp),
      if_neg hne7_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := ssOp),
      if_neg hne7_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := ssOp),
      if_neg hne7_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := ssOp),
      if_neg hne7_10,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOv (operation := ssOp),
      if_neg hne7_9,
      OperationPtr.getResultTypes!_WfRewriter_createOp hIm (operation := ssOp),
      if_neg hne7_8,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSs (operation := ssOp), if_pos rfl]
  have hImResTypes : imOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := imOp),
      if_neg hne8_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := imOp),
      if_neg hne8_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := imOp),
      if_neg hne8_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := imOp),
      if_neg hne8_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := imOp),
      if_neg hne8_10,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOv (operation := imOp),
      if_neg hne8_9,
      OperationPtr.getResultTypes!_WfRewriter_createOp hIm (operation := imOp), if_pos rfl]
  have hOvResTypes : ovOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := ovOp),
      if_neg hne9_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := ovOp),
      if_neg hne9_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := ovOp),
      if_neg hne9_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := ovOp),
      if_neg hne9_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := ovOp),
      if_neg hne9_10,
      OperationPtr.getResultTypes!_WfRewriter_createOp hOv (operation := ovOp), if_pos rfl]
  have hSatResTypes : satOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := satOp),
      if_neg hne10_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := satOp),
      if_neg hne10_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := satOp),
      if_neg hne10_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := satOp),
      if_neg hne10_11,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSat (operation := satOp), if_pos rfl]
  have hWozResTypes : wozOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := wozOp),
      if_neg hne11_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := wozOp),
      if_neg hne11_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := wozOp),
      if_neg hne11_12,
      OperationPtr.getResultTypes!_WfRewriter_createOp hWoz (operation := wozOp), if_pos rfl]
  have hSozResTypes : sozOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := sozOp),
      if_neg hne12_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := sozOp),
      if_neg hne12_13,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSoz (operation := sozOp), if_pos rfl]
  have hSelResTypes : selOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := selOp),
      if_neg hne13_14,
      OperationPtr.getResultTypes!_WfRewriter_createOp hSel (operation := selOp), if_pos rfl]
  -- The immediates of the four immediate-form ops (`li -1`, `srli 63`, `srai 63`, `slli 63`).
  have hOneProps : oneOp.getProperties! ctx₁₄.raw (.riscv .li) = mkRISCVImm (-1) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCb hne3_14,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSel hne3_13,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSoz hne3_12,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hWoz hne3_11,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSat hne3_10,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hOv hne3_9,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hIm hne3_8,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSs hne3_7,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hCl hne3_6,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hRs hne3_5,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSum hne3_4,
    OperationPtr.getProperties!_WfRewriter_createOp hOne (operation := oneOp)]
    rw [if_pos rfl]; rfl
  have hRsProps : rsOp.getProperties! ctx₁₄.raw (.riscv .srli) = mkRISCVImm 63 := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCb hne5_14,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSel hne5_13,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSoz hne5_12,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hWoz hne5_11,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSat hne5_10,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hOv hne5_9,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hIm hne5_8,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSs hne5_7,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hCl hne5_6,
    OperationPtr.getProperties!_WfRewriter_createOp hRs (operation := rsOp)]
    rw [if_pos rfl]; rfl
  have hRsImm : BitVec.ofInt 6 (rsOp.getProperties! ctx₁₄.raw (.riscv .srli)).value.value
      = BitVec.ofInt 6 63 := by rw [hRsProps]; simp [mkRISCVImm]
  have hSsProps : ssOp.getProperties! ctx₁₄.raw (.riscv .srai) = mkRISCVImm 63 := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCb hne7_14,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSel hne7_13,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSoz hne7_12,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hWoz hne7_11,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSat hne7_10,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hOv hne7_9,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hIm hne7_8,
    OperationPtr.getProperties!_WfRewriter_createOp hSs (operation := ssOp)]
    rw [if_pos rfl]; rfl
  have hSsImm : BitVec.ofInt 6 (ssOp.getProperties! ctx₁₄.raw (.riscv .srai)).value.value
      = BitVec.ofInt 6 63 := by rw [hSsProps]; simp [mkRISCVImm]
  have hImProps : imOp.getProperties! ctx₁₄.raw (.riscv .slli) = mkRISCVImm 63 := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCb hne8_14,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSel hne8_13,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSoz hne8_12,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hWoz hne8_11,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hSat hne8_10,
    OperationPtr.getProperties!_WfRewriter_createOp_ne hOv hne8_9,
    OperationPtr.getProperties!_WfRewriter_createOp hIm (operation := imOp)]
    rw [if_pos rfl]; rfl
  have hImImm : BitVec.ofInt 6 (imOp.getProperties! ctx₁₄.raw (.riscv .slli)).value.value
      = BitVec.ofInt 6 63 := by rw [hImProps]; simp [mkRISCVImm]
  -- `op` (the op being replaced) is distinct from every op created by the rewrite.
  have hOpNe1 : op ≠ lcastOp := fun hEq => hLCastFresh (hEq ▸ opInBounds)
  have hOpNe2 : op ≠ rcastOp := fun hEq => f2 (hEq ▸ iOp1)
  have hOpNe3 : op ≠ oneOp := fun hEq => f3 (hEq ▸ iOp2)
  have hOpNe4 : op ≠ sumOp := fun hEq => f4 (hEq ▸ iOp3)
  have hOpNe5 : op ≠ rsOp := fun hEq => f5 (hEq ▸ iOp4)
  have hOpNe6 : op ≠ clOp := fun hEq => f6 (hEq ▸ iOp5)
  have hOpNe7 : op ≠ ssOp := fun hEq => f7 (hEq ▸ iOp6)
  have hOpNe8 : op ≠ imOp := fun hEq => f8 (hEq ▸ iOp7)
  have hOpNe9 : op ≠ ovOp := fun hEq => f9 (hEq ▸ iOp8)
  have hOpNe10 : op ≠ satOp := fun hEq => f10 (hEq ▸ iOp9)
  have hOpNe11 : op ≠ wozOp := fun hEq => f11 (hEq ▸ iOp10)
  have hOpNe12 : op ≠ sozOp := fun hEq => f12 (hEq ▸ iOp11)
  have hOpNe13 : op ≠ selOp := fun hEq => f13 (hEq ▸ iOp12)
  have hOpNe14 : op ≠ cbOp := fun hEq => f14 (hEq ▸ iOp13)
  -- The cast-back op's result type is the integer type `i64`. `op`'s result type is untouched by
  -- each creation (it is never the created op's own result), so transport it back to `ctx`.
  have hCBType : ((op.getResult 0).get! ctx₁₃.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
    have g1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hLCast
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe1 hc.1)
    have g2 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hRCast
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe2 hc.1)
    have g3 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hOne
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe3 hc.1)
    have g4 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₄.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hSum
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe4 hc.1)
    have g5 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₅.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₄.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hRs
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe5 hc.1)
    have g6 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₆.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₅.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hCl
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe6 hc.1)
    have g7 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₇.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₆.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hSs
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe7 hc.1)
    have g8 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₈.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₇.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hIm
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe8 hc.1)
    have g9 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₉.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₈.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hOv
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe9 hc.1)
    have g10 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₀.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₉.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hSat
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe10 hc.1)
    have g11 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₁.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₀.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hWoz
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe11 hc.1)
    have g12 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₁.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hSoz
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe12 hc.1)
    have g13 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₂.raw := by
      rw [ValuePtr.getType!_WfRewriter_createOp hSel
        (value := ValuePtr.opResult (op.getResult 0))]
      exact dif_neg (fun hc => hOpNe13 hc.1)
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      rw [g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hCbResTypes : cbOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCb (operation := cbOp), if_pos rfl,
      hCBType]
  -- A result of `A` is never a result of a different op `B`.
  have hNotIn : ∀ (A B : OperationPtr), A ≠ B →
      ValuePtr.opResult (A.getResult 0) ∉ B.getResults! ctx₁₄.raw := by
    intro A B hne
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₁₄.raw
        (ValuePtr.opResult (A.getResult 0)) B with hres | ⟨i, hi, heq⟩
    · exact hres
    · refine absurd ?_ hne
      simp only [ValuePtr.opResult.injEq, OperationPtr.getResult_def, OpResultPtr.mk.injEq] at heq
      exact heq.1
  -- Interpretation tail: execute the fourteen-op list in `state'`. The frame clauses carry earlier
  -- register bindings across later steps; `sum` in particular must survive six intervening ops to
  -- reach the `czeronez`, and `minusOne` four to reach the `slli`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hLCastType hLCastOperands hLCastResTypes hLVal'
  have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₁₄.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₁₄.raw rhs lcastOp
      with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (hRhsNeLCastRes i)
  have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 64 yt) := by
    rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
      hRCastType hRCastOperands hRCastResTypes hRVal₁
  have hX₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₂ _ (hNotIn lcastOp rcastOp (by grind))]; exact hRes₁
  -- `li -1`
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
    interpretOp_riscv_li_forward (state := s₂) (inBounds := by grind)
      hOneType hOneProps hOneOperands hOneResTypes
  have hM₃ : s₃.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := hRes₃
  have hX₃ : s₃.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₃ _ (hNotIn lcastOp oneOp (by grind))]; exact hX₂
  have hY₃ : s₃.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₃ _ (hNotIn rcastOp oneOp (by grind))]; exact hRes₂
  -- `sum = add X Y`
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.add r₂ r₁) (fun _ _ _ _ => rfl) hSumType hSumOperands
      hSumResTypes hX₃ hY₃
  have hX₄ : s₄.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₄ _ (hNotIn lcastOp sumOp (by grind))]; exact hX₃
  have hY₄ : s₄.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₄ _ (hNotIn rcastOp sumOp (by grind))]; exact hY₃
  have hM₄ : s₄.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₄ _ (hNotIn oneOp sumOp (by grind))]; exact hM₃
  -- `rhsSign = srli 63 Y`
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
    interpretOp_riscv_srli_forward (state := s₄) (inBounds := by grind) (k := BitVec.ofInt 6 63)
      hRsType hRsImm hRsOperands hRsResTypes hY₄
  have hX₅ : s₅.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₅ _ (hNotIn lcastOp rsOp (by grind))]; exact hX₄
  have hM₅ : s₅.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₅ _ (hNotIn oneOp rsOp (by grind))]; exact hM₄
  have hSUM₅ : s₅.variables.getVar? (ValuePtr.opResult (sumOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₅ _ (hNotIn sumOp rsOp (by grind))]; exact hRes₄
  -- `carryLike = slt sum X`  (i.e. `sum <s X`)
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₅) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.slt r₂ r₁) (fun _ _ _ _ => rfl) hClType hClOperands
      hClResTypes hSUM₅ hX₅
  have hM₆ : s₆.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₆ _ (hNotIn oneOp clOp (by grind))]; exact hM₅
  have hSUM₆ : s₆.variables.getVar? (ValuePtr.opResult (sumOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₆ _ (hNotIn sumOp clOp (by grind))]; exact hSUM₅
  have hRS₆ : s₆.variables.getVar? (ValuePtr.opResult (rsOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt))) := by
    rw [hFrame₆ _ (hNotIn rsOp clOp (by grind))]; exact hRes₅
  -- `sumSign = srai 63 sum`
  obtain ⟨s₇, hI₇, hMem₇, hRes₇, hFrame₇⟩ :=
    interpretOp_riscv_srai_forward (state := s₆) (inBounds := by grind) (k := BitVec.ofInt 6 63)
      hSsType hSsImm hSsOperands hSsResTypes hSUM₆
  have hM₇ : s₇.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₇ _ (hNotIn oneOp ssOp (by grind))]; exact hM₆
  have hSUM₇ : s₇.variables.getVar? (ValuePtr.opResult (sumOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₇ _ (hNotIn sumOp ssOp (by grind))]; exact hSUM₆
  have hRS₇ : s₇.variables.getVar? (ValuePtr.opResult (rsOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt))) := by
    rw [hFrame₇ _ (hNotIn rsOp ssOp (by grind))]; exact hRS₆
  have hCL₇ : s₇.variables.getVar? (ValuePtr.opResult (clOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.slt (LLVM.Int.toReg xt)
          (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₇ _ (hNotIn clOp ssOp (by grind))]; exact hRes₆
  -- `intMin = slli 63 (li -1)`
  obtain ⟨s₈, hI₈, hMem₈, hRes₈, hFrame₈⟩ :=
    interpretOp_riscv_slli_forward (state := s₇) (inBounds := by grind) (k := BitVec.ofInt 6 63)
      hImType hImImm hImOperands hImResTypes hM₇
  have hSUM₈ : s₈.variables.getVar? (ValuePtr.opResult (sumOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₈ _ (hNotIn sumOp imOp (by grind))]; exact hSUM₇
  have hRS₈ : s₈.variables.getVar? (ValuePtr.opResult (rsOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt))) := by
    rw [hFrame₈ _ (hNotIn rsOp imOp (by grind))]; exact hRS₇
  have hCL₈ : s₈.variables.getVar? (ValuePtr.opResult (clOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.slt (LLVM.Int.toReg xt)
          (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₈ _ (hNotIn clOp imOp (by grind))]; exact hCL₇
  have hSS₈ : s₈.variables.getVar? (ValuePtr.opResult (ssOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srai (BitVec.ofInt 6 63)
          (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₈ _ (hNotIn ssOp imOp (by grind))]; exact hRes₇
  -- `overflow = xor rhsSign carryLike`
  obtain ⟨s₉, hI₉, hMem₉, hRes₉, hFrame₉⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₈) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.xor r₂ r₁) (fun _ _ _ _ => rfl) hOvType hOvOperands
      hOvResTypes hRS₈ hCL₈
  have hSUM₉ : s₉.variables.getVar? (ValuePtr.opResult (sumOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₉ _ (hNotIn sumOp ovOp (by grind))]; exact hSUM₈
  have hSS₉ : s₉.variables.getVar? (ValuePtr.opResult (ssOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srai (BitVec.ofInt 6 63)
          (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₉ _ (hNotIn ssOp ovOp (by grind))]; exact hSS₈
  have hIM₉ : s₉.variables.getVar? (ValuePtr.opResult (imOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.slli (BitVec.ofInt 6 63)
          (Data.RISCV.li (BitVec.ofInt 64 (-1))))) := by
    rw [hFrame₉ _ (hNotIn imOp ovOp (by grind))]; exact hRes₈
  -- `sat = xor sumSign intMin`
  obtain ⟨s₁₀, hI₁₀, hMem₁₀, hRes₁₀, hFrame₁₀⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₉) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.xor r₂ r₁) (fun _ _ _ _ => rfl) hSatType hSatOperands
      hSatResTypes hSS₉ hIM₉
  have hSUM₁₀ : s₁₀.variables.getVar? (ValuePtr.opResult (sumOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₁₀ _ (hNotIn sumOp satOp (by grind))]; exact hSUM₉
  have hOV₁₀ : s₁₀.variables.getVar? (ValuePtr.opResult (ovOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.xor
          (Data.RISCV.slt (LLVM.Int.toReg xt)
            (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt)))) := by
    rw [hFrame₁₀ _ (hNotIn ovOp satOp (by grind))]; exact hRes₉
  -- `wrappedOrZero = czeronez sum overflow`
  obtain ⟨s₁₁, hI₁₁, hMem₁₁, hRes₁₁, hFrame₁₁⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₁₀) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.czeronez r₂ r₁) (fun _ _ _ _ => rfl) hWozType hWozOperands
      hWozResTypes hSUM₁₀ hOV₁₀
  have hOV₁₁ : s₁₁.variables.getVar? (ValuePtr.opResult (ovOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.xor
          (Data.RISCV.slt (LLVM.Int.toReg xt)
            (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt)))) := by
    rw [hFrame₁₁ _ (hNotIn ovOp wozOp (by grind))]; exact hOV₁₀
  have hSAT₁₁ : s₁₁.variables.getVar? (ValuePtr.opResult (satOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.xor
          (Data.RISCV.slli (BitVec.ofInt 6 63) (Data.RISCV.li (BitVec.ofInt 64 (-1))))
          (Data.RISCV.srai (BitVec.ofInt 6 63)
            (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))))) := by
    rw [hFrame₁₁ _ (hNotIn satOp wozOp (by grind))]; exact hRes₁₀
  -- `satOrZero = czeroeqz sat overflow`
  obtain ⟨s₁₂, hI₁₂, hMem₁₂, hRes₁₂, hFrame₁₂⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₁₁) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.czeroeqz r₂ r₁) (fun _ _ _ _ => rfl) hSozType hSozOperands
      hSozResTypes hSAT₁₁ hOV₁₁
  have hWOZ₁₂ : s₁₂.variables.getVar? (ValuePtr.opResult (wozOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.czeronez
          (Data.RISCV.xor
            (Data.RISCV.slt (LLVM.Int.toReg xt)
              (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
            (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt)))
          (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₁₂ _ (hNotIn wozOp sozOp (by grind))]; exact hRes₁₁
  -- `select = or satOrZero wrappedOrZero`
  obtain ⟨s₁₃, hI₁₃, hMem₁₃, hRes₁₃, hFrame₁₃⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₁₂) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl) hSelType hSelOperands
      hSelResTypes hRes₁₂ hWOZ₁₂
  obtain ⟨s₁₄, hI₁₄, hMem₁₄, hRes₁₄, -⟩ :=
    interpretOp_castBack_forward (state := s₁₃) (inBounds := by grind)
      hCbType hCbOperands hCbResTypes hRes₁₃
  refine ⟨s₁₄, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, hI₈, hI₉, hI₁₀, hI₁₁, hI₁₂,
      hI₁₃, hI₁₄, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.czeronez
            (Data.RISCV.xor
              (Data.RISCV.slt (LLVM.Int.toReg xt)
                (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt)))
            (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.czeroeqz
            (Data.RISCV.xor
              (Data.RISCV.slt (LLVM.Int.toReg xt)
                (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (Data.RISCV.srli (BitVec.ofInt 6 63) (LLVM.Int.toReg yt)))
            (Data.RISCV.xor
              (Data.RISCV.slli (BitVec.ofInt 6 63) (Data.RISCV.li (BitVec.ofInt 64 (-1))))
              (Data.RISCV.srai (BitVec.ofInt 6 63)
                (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))))) 64)], ?_, ?_⟩
    · simp [hRes₁₄, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using saddSat_isRefinedBy_toInt hxtRef hytRef⟩

end Veir
