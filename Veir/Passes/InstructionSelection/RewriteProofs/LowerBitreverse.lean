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
import Veir.Passes.InstructionSelection.RewriteProofs.LowerUnaryW
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBswap
import Veir.Passes.InstructionSelection.RewriteProofs.LowerConst
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSaddSat
import Veir.Passes.InstructionSelection.RewriteProofs.LowerIcmp

namespace Veir

/-!
## Correctness of `bitreverse_local`

`llvm.intr.bitreverse` on a 64- or 32-bit integer is lowered to a cast to a register, three SWAR
bit-swap stages (`((x & mask) << k) | ((x >> k) & mask)` for `(mask, k)` = (`0x5555…`, 1),
(`0x3333…`, 2), (`0x0f0f…`, 4) — each emitted by `bitreverseStageLocal` as
`li`/`and`/`slli`/`srli`/`and`/`or`), a byte-reversing `riscv.rev8`, for `i32` an extra
`riscv.srli 32` (the 32-bit masks keep the SWAR result in the low word, which `rev8` sends to the
high word), and the cast back — 21 operations for `i64`, 22 for `i32`, the longest chain proven
so far.

A monolithic (`LowerSaddSat`-style) peel of 21 creations would need hundreds of pairwise
distinctness transports, so this proof instead factors the repeated 6-op stage the way
`LowerIcmp` factors its prologue: `bitreverseStageLocal_extends` shows one stage's creations
only extend the context (`CtxExtends`), and `bitreverseStageLocal_run` symbolically executes one
stage against an *arbitrary* final context, given the extension witness. The main proof peels the
shared prefix, applies the stage lemmas three times, and finishes with the `rev8`(/`srli`)
cast-back tail. This is also what motivates the `properties` field of `CtxExtends`: the stage's
`li`/`slli`/`srli` immediates must survive to the final context.

The data-level core (`Data.LLVM.Int.bitreverse` = `BitVec.reverse`) is outside `bv_decide`'s
vocabulary: `BitVec.reverse` is width-recursive. At the two concrete widths, unfolding `reverse`
(and `concat`) by simp produces a bitblastable append/`msb` normal form, after which
`bv_decide` closes the SWAR identity.
-/

/-- The register value computed by one SWAR stage (`bitreverseStageLocal mask shamt`) on input
    `r`: `or` of the masked-then-shifted low part and the shifted-then-masked high part, with the
    mask materialized by `li`. Data-level counterpart of the emitted
    `li`/`and`/`slli`/`srli`/`and`/`or` chain (in the interpreter's `op₂ op₁` operand order). -/
def bitreverseStageReg (mask shamt : Int) (r : Data.RISCV.Reg) : Data.RISCV.Reg :=
  Data.RISCV.or
    (Data.RISCV.and (Data.RISCV.srli (BitVec.ofInt 6 shamt) r)
      (Data.RISCV.li (BitVec.ofInt 64 mask)))
    (Data.RISCV.slli (BitVec.ofInt 6 shamt)
      (Data.RISCV.and r (Data.RISCV.li (BitVec.ofInt 64 mask))))

/-- Correctness of the three-SWAR-stage + `rev8` lowering of a 64-bit `llvm.intr.bitreverse`:
    the stages swap adjacent bits, then bit pairs, then nibbles (so every *byte* is bit-reversed
    in place), and `rev8` reverses the bytes, completing the full bit reversal. -/
theorem bitreverse_isRefinedBy_toInt_rev8_swar {x xt : Data.LLVM.Int 64} (h : x ⊒ xt) :
    Data.LLVM.Int.bitreverse x ⊒
      RISCV.Reg.toInt
        (Data.RISCV.rev8
          (bitreverseStageReg 0x0f0f0f0f0f0f0f0f 4
            (bitreverseStageReg 0x3333333333333333 2
              (bitreverseStageReg 0x5555555555555555 1 (LLVM.Int.toReg xt))))) 64 := by
  revert h
  simp only [bitreverseStageReg]
  veir_bv_normalize
  simp only [BitVec.reverse, BitVec.concat, BitVec.truncate_eq_setWidth]
  bv_decide

/-- Correctness of the `srli 32 (rev8 ·)` tail of a 32-bit `llvm.intr.bitreverse`: with the
    32-bit masks the SWAR stages stay in the low word, `rev8` sends its byte-reversal to the
    high word, and `srli 32` shifts it back down before the truncating cast reads the low
    32 bits. -/
theorem bitreverse_isRefinedBy_toInt_srli_rev8_swar {x xt : Data.LLVM.Int 32} (h : x ⊒ xt) :
    Data.LLVM.Int.bitreverse x ⊒
      RISCV.Reg.toInt
        (Data.RISCV.srli (BitVec.ofInt 6 32)
          (Data.RISCV.rev8
            (bitreverseStageReg 0x0f0f0f0f 4
              (bitreverseStageReg 0x33333333 2
                (bitreverseStageReg 0x55555555 1 (LLVM.Int.toReg xt)))))) 32 := by
  revert h
  simp only [bitreverseStageReg]
  veir_bv_normalize
  simp only [BitVec.reverse, BitVec.concat, BitVec.truncate_eq_setWidth]
  bv_decide

/-! ### The repeated 6-op SWAR stage `bitreverseStageLocal`

Following the `LowerIcmp` prologue treatment: the stage is proven once against an arbitrary final
context, and the main proof instantiates it three times. -/

/-- One SWAR stage only creates fresh operations, so it extends the context. -/
theorem bitreverseStageLocal_extends {mask shamt : Int} {ctx ctx' : WfIRContext OpCode}
    {op : OperationPtr} {input out : ValuePtr} {ops : Array OperationPtr}
    (opInBounds : op.InBounds ctx.raw)
    (hStage : bitreverseStageLocal mask shamt ctx input = some (ctx', ops, out)) :
    CtxExtends op ctx ctx' := by
  simp only [bitreverseStageLocal, bind, Option.bind_eq_some_iff] at hStage
  peelOpCreation hStage ctx₁ maskOp hMask
  replace hMask := WfRewriter.createOp!_none_some hMask
  obtain ⟨_, _, _, hMask⟩ := hMask
  peelOpCreation hStage ctx₂ lowOp hLow
  replace hLow := WfRewriter.createOp!_none_some hLow
  obtain ⟨_, _, _, hLow⟩ := hLow
  peelOpCreation hStage ctx₃ lowShiftOp hLowShift
  replace hLowShift := WfRewriter.createOp!_none_some hLowShift
  obtain ⟨_, _, _, hLowShift⟩ := hLowShift
  peelOpCreation hStage ctx₄ highShiftOp hHighShift
  replace hHighShift := WfRewriter.createOp!_none_some hHighShift
  obtain ⟨_, _, _, hHighShift⟩ := hHighShift
  peelOpCreation hStage ctx₅ highOp hHigh
  replace hHigh := WfRewriter.createOp!_none_some hHigh
  obtain ⟨_, _, _, hHigh⟩ := hHigh
  peelOpCreation hStage ctx₆ orOp hOr
  replace hOr := WfRewriter.createOp!_none_some hOr
  obtain ⟨_, _, _, hOr⟩ := hOr
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using hStage
  have E₁ := CtxExtends.of_createOp hMask opInBounds
  have hOpIn₁ := E₁.inBounds op opInBounds
  have E₂ := CtxExtends.of_createOp hLow hOpIn₁
  have hOpIn₂ := E₂.inBounds op hOpIn₁
  have E₃ := CtxExtends.of_createOp hLowShift hOpIn₂
  have hOpIn₃ := E₃.inBounds op hOpIn₂
  have E₄ := CtxExtends.of_createOp hHighShift hOpIn₃
  have hOpIn₄ := E₄.inBounds op hOpIn₃
  have E₅ := CtxExtends.of_createOp hHigh hOpIn₄
  have hOpIn₅ := E₅.inBounds op hOpIn₄
  have E₆ := CtxExtends.of_createOp hOr hOpIn₅
  exact E₁.trans (E₂.trans (E₃.trans (E₄.trans (E₅.trans E₆))))

/-- One SWAR stage's emitted ops, and its output value, are in bounds in the context it
    returns. -/
theorem bitreverseStageLocal_inBounds {mask shamt : Int} {ctx ctx' : WfIRContext OpCode}
    {input out : ValuePtr} {ops : Array OperationPtr}
    (hStage : bitreverseStageLocal mask shamt ctx input = some (ctx', ops, out)) :
    (∀ o ∈ ops.toList, o.InBounds ctx'.raw) ∧ out.InBounds ctx'.raw := by
  simp only [bitreverseStageLocal, bind, Option.bind_eq_some_iff] at hStage
  peelOpCreation hStage ctx₁ maskOp hMask
  replace hMask := WfRewriter.createOp!_none_some hMask
  obtain ⟨_, _, _, hMask⟩ := hMask
  peelOpCreation hStage ctx₂ lowOp hLow
  replace hLow := WfRewriter.createOp!_none_some hLow
  obtain ⟨_, _, _, hLow⟩ := hLow
  peelOpCreation hStage ctx₃ lowShiftOp hLowShift
  replace hLowShift := WfRewriter.createOp!_none_some hLowShift
  obtain ⟨_, _, _, hLowShift⟩ := hLowShift
  peelOpCreation hStage ctx₄ highShiftOp hHighShift
  replace hHighShift := WfRewriter.createOp!_none_some hHighShift
  obtain ⟨_, _, _, hHighShift⟩ := hHighShift
  peelOpCreation hStage ctx₅ highOp hHigh
  replace hHigh := WfRewriter.createOp!_none_some hHigh
  obtain ⟨_, _, _, hHigh⟩ := hHigh
  peelOpCreation hStage ctx₆ orOp hOr
  replace hOr := WfRewriter.createOp!_none_some hOr
  obtain ⟨_, _, _, hOr⟩ := hOr
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using hStage
  have hMaskIn₁ : maskOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds _ hMask
  have hLowIn₂ : lowOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds _ hLow
  have hLowShiftIn₃ : lowShiftOp.InBounds ctx₃.raw :=
    WfRewriter.createOp_new_inBounds _ hLowShift
  have hHighShiftIn₄ : highShiftOp.InBounds ctx₄.raw :=
    WfRewriter.createOp_new_inBounds _ hHighShift
  have hHighIn₅ : highOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds _ hHigh
  have hOrIn₆ : orOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds _ hOr
  have E₂ := CtxExtends.of_createOp (op := maskOp) hLow hMaskIn₁
  have E₃ := CtxExtends.of_createOp (op := maskOp) hLowShift (E₂.inBounds _ hMaskIn₁)
  have E₄ := CtxExtends.of_createOp (op := maskOp) hHighShift
    (E₃.inBounds _ (E₂.inBounds _ hMaskIn₁))
  have E₅ := CtxExtends.of_createOp (op := maskOp) hHigh
    (E₄.inBounds _ (E₃.inBounds _ (E₂.inBounds _ hMaskIn₁)))
  have E₆ := CtxExtends.of_createOp (op := maskOp) hOr
    (E₅.inBounds _ (E₄.inBounds _ (E₃.inBounds _ (E₂.inBounds _ hMaskIn₁))))
  have E₂₆ := E₂.trans (E₃.trans (E₄.trans (E₅.trans E₆)))
  have E₃₆ := E₃.trans (E₄.trans (E₅.trans E₆))
  have E₄₆ := E₄.trans (E₅.trans E₆)
  have E₅₆ := E₅.trans E₆
  refine ⟨?_, ?_⟩
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
    · exact E₂₆.inBounds o hMaskIn₁
    · exact E₃₆.inBounds o hLowIn₂
    · exact E₄₆.inBounds o hLowShiftIn₃
    · exact E₅₆.inBounds o hHighShiftIn₄
    · exact E₆.inBounds o hHighIn₅
    · exact hOrIn₆
  · grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]

set_option maxHeartbeats 1600000 in
/-- Symbolic execution of one SWAR stage in the main proof's final context `F`: given the
    extension of the stage's output context to `F` and the input register value `r`, the six ops
    run without touching memory and leave the stage output holding
    `bitreverseStageReg mask shamt r`. -/
theorem bitreverseStageLocal_run {mask shamt : Int} {ctx ctx' F : WfIRContext OpCode}
    {op : OperationPtr} {input out : ValuePtr} {ops : Array OperationPtr}
    {r : Data.RISCV.Reg} {state' : InterpreterState F}
    (opInBounds : op.InBounds ctx.raw)
    (hStage : bitreverseStageLocal mask shamt ctx input = some (ctx', ops, out))
    (hExt : CtxExtends op ctx' F)
    (hInputIn : input.InBounds ctx.raw)
    (hVal : state'.variables.getVar? input = some (.reg r))
    (hin : ∀ o ∈ ops.toList, o.InBounds F.raw) :
    ∃ s' : InterpreterState F,
      interpretOpList ops.toList state' hin = some (.ok (s', none)) ∧
      s'.memory = state'.memory ∧
      s'.variables.getVar? out = some (.reg (bitreverseStageReg mask shamt r)) := by
  simp only [bitreverseStageLocal, bind, Option.bind_eq_some_iff] at hStage
  peelOpCreation hStage ctx₁ maskOp hMask
  replace hMask := WfRewriter.createOp!_none_some hMask
  obtain ⟨_, _, _, hMask⟩ := hMask
  peelOpCreation hStage ctx₂ lowOp hLow
  replace hLow := WfRewriter.createOp!_none_some hLow
  obtain ⟨_, _, _, hLow⟩ := hLow
  peelOpCreation hStage ctx₃ lowShiftOp hLowShift
  replace hLowShift := WfRewriter.createOp!_none_some hLowShift
  obtain ⟨_, _, _, hLowShift⟩ := hLowShift
  peelOpCreation hStage ctx₄ highShiftOp hHighShift
  replace hHighShift := WfRewriter.createOp!_none_some hHighShift
  obtain ⟨_, _, _, hHighShift⟩ := hHighShift
  peelOpCreation hStage ctx₅ highOp hHigh
  replace hHigh := WfRewriter.createOp!_none_some hHigh
  obtain ⟨_, _, _, hHigh⟩ := hHigh
  peelOpCreation hStage ctx₆ orOp hOr
  replace hOr := WfRewriter.createOp!_none_some hOr
  obtain ⟨_, _, _, hOr⟩ := hOr
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using hStage
  -- Context extensions: one per creation, plus the suffixes reaching `F`.
  have E₁ := CtxExtends.of_createOp hMask opInBounds
  have hOpIn₁ := E₁.inBounds op opInBounds
  have E₂ := CtxExtends.of_createOp hLow hOpIn₁
  have hOpIn₂ := E₂.inBounds op hOpIn₁
  have E₃ := CtxExtends.of_createOp hLowShift hOpIn₂
  have hOpIn₃ := E₃.inBounds op hOpIn₂
  have E₄ := CtxExtends.of_createOp hHighShift hOpIn₃
  have hOpIn₄ := E₄.inBounds op hOpIn₃
  have E₅ := CtxExtends.of_createOp hHigh hOpIn₄
  have hOpIn₅ := E₅.inBounds op hOpIn₄
  have E₆ := CtxExtends.of_createOp hOr hOpIn₅
  have F₆ : CtxExtends op ctx₆ F := hExt
  have F₅ : CtxExtends op ctx₅ F := E₆.trans F₆
  have F₄ : CtxExtends op ctx₄ F := E₅.trans F₅
  have F₃ : CtxExtends op ctx₃ F := E₄.trans F₄
  have F₂ : CtxExtends op ctx₂ F := E₃.trans F₃
  have F₁ : CtxExtends op ctx₁ F := E₂.trans F₂
  -- Freshness and in-bounds bookkeeping for the frame conditions.
  have hMaskIn₁ : maskOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds _ hMask
  have hLowIn₂ : lowOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds _ hLow
  have hLowShiftIn₃ : lowShiftOp.InBounds ctx₃.raw :=
    WfRewriter.createOp_new_inBounds _ hLowShift
  have hHighShiftIn₄ : highShiftOp.InBounds ctx₄.raw :=
    WfRewriter.createOp_new_inBounds _ hHighShift
  have hHighIn₅ : highOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds _ hHigh
  have hOrIn₆ : orOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds _ hOr
  have hMaskFresh : ¬ maskOp.InBounds ctx.raw := WfRewriter.createOp_new_not_inBounds _ hMask
  have hLowFresh : ¬ lowOp.InBounds ctx₁.raw := WfRewriter.createOp_new_not_inBounds _ hLow
  have hLowShiftFresh : ¬ lowShiftOp.InBounds ctx₂.raw :=
    WfRewriter.createOp_new_not_inBounds _ hLowShift
  have hHighShiftFresh : ¬ highShiftOp.InBounds ctx₃.raw :=
    WfRewriter.createOp_new_not_inBounds _ hHighShift
  have hHighFresh : ¬ highOp.InBounds ctx₄.raw := WfRewriter.createOp_new_not_inBounds _ hHigh
  have hInputIn₁ : input.InBounds ctx₁.raw := E₁.valueInBounds input hInputIn
  have hInputIn₂ : input.InBounds ctx₂.raw := E₂.valueInBounds input hInputIn₁
  have hMaskResIn₁ : (ValuePtr.opResult (maskOp.getResult 0)).InBounds ctx₁.raw := by
    grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  have hMaskResIn₂ : (ValuePtr.opResult (maskOp.getResult 0)).InBounds ctx₂.raw :=
    E₂.valueInBounds _ hMaskResIn₁
  have hMaskResIn₃ : (ValuePtr.opResult (maskOp.getResult 0)).InBounds ctx₃.raw :=
    E₃.valueInBounds _ hMaskResIn₂
  have hLowShiftResIn₃ : (ValuePtr.opResult (lowShiftOp.getResult 0)).InBounds ctx₃.raw := by
    grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  have hLowShiftResIn₄ : (ValuePtr.opResult (lowShiftOp.getResult 0)).InBounds ctx₄.raw :=
    E₄.valueInBounds _ hLowShiftResIn₃
  -- Structural facts about the six ops, in `F`.
  have hMaskType : maskOp.getOpType! F.raw = .riscv .li := by
    rw [F₁.opType maskOp hMaskIn₁]; grind
  have hMaskOperands : maskOp.getOperands! F.raw = #[] := by
    rw [F₁.operands maskOp hMaskIn₁]; grind
  have hMaskResTypes : maskOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁.resultTypes maskOp hMaskIn₁]; grind
  have hMaskProps : maskOp.getProperties! F.raw (.riscv .li)
      = RISCVImmediateProperties.mk (IntegerAttr.mk mask (IntegerType.mk 64)) := by
    rw [F₁.properties maskOp hMaskIn₁]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hMask (operation := maskOp)]
  have hLowType : lowOp.getOpType! F.raw = .riscv .and := by
    rw [F₂.opType lowOp hLowIn₂]; grind
  have hLowOperands :
      lowOp.getOperands! F.raw = #[ValuePtr.opResult (maskOp.getResult 0), input] := by
    rw [F₂.operands lowOp hLowIn₂]; grind
  have hLowResTypes : lowOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₂.resultTypes lowOp hLowIn₂]; grind
  have hLowShiftType : lowShiftOp.getOpType! F.raw = .riscv .slli := by
    rw [F₃.opType lowShiftOp hLowShiftIn₃]; grind
  have hLowShiftOperands :
      lowShiftOp.getOperands! F.raw = #[ValuePtr.opResult (lowOp.getResult 0)] := by
    rw [F₃.operands lowShiftOp hLowShiftIn₃]; grind
  have hLowShiftResTypes :
      lowShiftOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₃.resultTypes lowShiftOp hLowShiftIn₃]; grind
  have hLowShiftProps : lowShiftOp.getProperties! F.raw (.riscv .slli)
      = RISCVImmediateProperties.mk (IntegerAttr.mk shamt (IntegerType.mk 64)) := by
    rw [F₃.properties lowShiftOp hLowShiftIn₃]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hLowShift (operation := lowShiftOp)]
  have hLowShiftImm : BitVec.ofInt 6 (lowShiftOp.getProperties! F.raw (.riscv .slli)).value.value
      = BitVec.ofInt 6 shamt := by rw [hLowShiftProps]
  have hHighShiftType : highShiftOp.getOpType! F.raw = .riscv .srli := by
    rw [F₄.opType highShiftOp hHighShiftIn₄]; grind
  have hHighShiftOperands : highShiftOp.getOperands! F.raw = #[input] := by
    rw [F₄.operands highShiftOp hHighShiftIn₄]; grind
  have hHighShiftResTypes :
      highShiftOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₄.resultTypes highShiftOp hHighShiftIn₄]; grind
  have hHighShiftProps : highShiftOp.getProperties! F.raw (.riscv .srli)
      = RISCVImmediateProperties.mk (IntegerAttr.mk shamt (IntegerType.mk 64)) := by
    rw [F₄.properties highShiftOp hHighShiftIn₄]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hHighShift (operation := highShiftOp)]
  have hHighShiftImm : BitVec.ofInt 6 (highShiftOp.getProperties! F.raw (.riscv .srli)).value.value
      = BitVec.ofInt 6 shamt := by rw [hHighShiftProps]
  have hHighType : highOp.getOpType! F.raw = .riscv .and := by
    rw [F₅.opType highOp hHighIn₅]; grind
  have hHighOperands : highOp.getOperands! F.raw
      = #[ValuePtr.opResult (maskOp.getResult 0), ValuePtr.opResult (highShiftOp.getResult 0)] := by
    rw [F₅.operands highOp hHighIn₅]; grind
  have hHighResTypes : highOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₅.resultTypes highOp hHighIn₅]; grind
  have hOrType : orOp.getOpType! F.raw = .riscv .or := by
    rw [F₆.opType orOp hOrIn₆]; grind
  have hOrOperands : orOp.getOperands! F.raw
      = #[ValuePtr.opResult (lowShiftOp.getResult 0), ValuePtr.opResult (highOp.getResult 0)] := by
    rw [F₆.operands orOp hOrIn₆]; grind
  have hOrResTypes : orOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₆.resultTypes orOp hOrIn₆]; grind
  -- Execute the six ops.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_riscv_li_forward (state := state') (inBounds := hin maskOp (by simp))
      (props := RISCVImmediateProperties.mk (IntegerAttr.mk mask (IntegerType.mk 64)))
      hMaskType hMaskProps hMaskOperands hMaskResTypes
  replace hRes₁ : s₁.variables.getVar? (ValuePtr.opResult (maskOp.getResult 0))
      = some (.reg (Data.RISCV.li (BitVec.ofInt 64 mask))) := hRes₁
  have hInputVal₁ : s₁.variables.getVar? input = some (.reg r) := by
    rw [hFrame₁ input
      (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hInputIn hMaskFresh)]
    exact hVal
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₁) (inBounds := hin lowOp (by simp))
      (f := fun r₁ r₂ => Data.RISCV.and r₂ r₁) (fun _ _ _ _ => rfl)
      hLowType hLowOperands hLowResTypes hRes₁ hInputVal₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
    interpretOp_riscv_slli_forward (state := s₂) (inBounds := hin lowShiftOp (by simp))
      (k := BitVec.ofInt 6 shamt)
      hLowShiftType hLowShiftImm hLowShiftOperands hLowShiftResTypes hRes₂
  have hInputVal₂ : s₂.variables.getVar? input = some (.reg r) := by
    rw [hFrame₂ input
      (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hInputIn₁ hLowFresh)]
    exact hInputVal₁
  have hInputVal₃ : s₃.variables.getVar? input = some (.reg r) := by
    rw [hFrame₃ input
      (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hInputIn₂ hLowShiftFresh)]
    exact hInputVal₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
    interpretOp_riscv_srli_forward (state := s₃) (inBounds := hin highShiftOp (by simp))
      (k := BitVec.ofInt 6 shamt)
      hHighShiftType hHighShiftImm hHighShiftOperands hHighShiftResTypes hInputVal₃
  have hMaskVal₂ : s₂.variables.getVar? (ValuePtr.opResult (maskOp.getResult 0))
      = some (.reg (Data.RISCV.li (BitVec.ofInt 64 mask))) := by
    rw [hFrame₂ _
      (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hMaskResIn₁ hLowFresh)]
    exact hRes₁
  have hMaskVal₃ : s₃.variables.getVar? (ValuePtr.opResult (maskOp.getResult 0))
      = some (.reg (Data.RISCV.li (BitVec.ofInt 64 mask))) := by
    rw [hFrame₃ _
      (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hMaskResIn₂ hLowShiftFresh)]
    exact hMaskVal₂
  have hMaskVal₄ : s₄.variables.getVar? (ValuePtr.opResult (maskOp.getResult 0))
      = some (.reg (Data.RISCV.li (BitVec.ofInt 64 mask))) := by
    rw [hFrame₄ _
      (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hMaskResIn₃ hHighShiftFresh)]
    exact hMaskVal₃
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₄) (inBounds := hin highOp (by simp))
      (f := fun r₁ r₂ => Data.RISCV.and r₂ r₁) (fun _ _ _ _ => rfl)
      hHighType hHighOperands hHighResTypes hMaskVal₄ hRes₄
  have hLowShiftVal₄ : s₄.variables.getVar? (ValuePtr.opResult (lowShiftOp.getResult 0))
      = some (.reg (Data.RISCV.slli (BitVec.ofInt 6 shamt)
          (Data.RISCV.and r (Data.RISCV.li (BitVec.ofInt 64 mask))))) := by
    rw [hFrame₄ _
      (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hLowShiftResIn₃ hHighShiftFresh)]
    exact hRes₃
  have hLowShiftVal₅ : s₅.variables.getVar? (ValuePtr.opResult (lowShiftOp.getResult 0))
      = some (.reg (Data.RISCV.slli (BitVec.ofInt 6 shamt)
          (Data.RISCV.and r (Data.RISCV.li (BitVec.ofInt 64 mask))))) := by
    rw [hFrame₅ _
      (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hLowShiftResIn₄ hHighFresh)]
    exact hLowShiftVal₄
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₅) (inBounds := hin orOp (by simp))
      (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl)
      hOrType hOrOperands hOrResTypes hLowShiftVal₅ hRes₅
  refine ⟨s₆, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, Interp]
  · exact hRes₆

set_option maxHeartbeats 4000000 in
/-- Correctness of the `bitreverse_local` lowering: the
    `castToReg → 3 × SWAR stage → rev8 (→ srli 32 for i32) → castBack` round trip refines
    `llvm.intr.bitreverse`. -/
theorem bitreverse_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics bitreverse_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, bitreverse_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchBitreverse op ctx.raw).isSome := by
    cases hM : matchBitreverse op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨operand, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchBitreverse_implies hMatch
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, hResOperType, intType, isT, hResType⟩ :=
    OperationPtr.Verified.llvm_intr__bitreverse opVerif hOpType
  -- The operand type is the integer type `intType`; resolve the type-destructuring match.
  have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [show operand.getType! ctx.raw = ⟨.integerType intType, isT⟩ from by grind]
  rw [hOperandType] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand's value and `bitreverse`.
  obtain ⟨xVal, hxVal, hMem, hRes, hCf⟩ :=
    matchUnaryOp_interpretOp_unfold (srcFn := fun {_} x _ => Data.LLVM.Int.bitreverse x)
      opInBounds hOpType hNumResults hOperands rfl (fun _ _ _ _ _ _ => rfl) hinterp hOperandType
  subst hCf
  -- The matched operand dominates the rewrite point in the source context.
  have hDomCtx : operand.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  peelSplittableCondition [hBw] hpattern
  -- Source value: `op`'s single result is `bitreverse` of its operand.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `operand` is not one of `op`'s results, and `op`'s result is in bounds.
  have vNotOp : ¬ operand ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  have hOperandIn : operand.InBounds ctx.raw := by rw [hOperandEq]; grind
  -- Peel the shared `castToReg`.
  simp only [Option.bind_eq_some_iff] at hpattern
  obtain ⟨⟨ctx₁, castOp⟩, hCast, hpattern⟩ := hpattern
  simp only [castToRegLocal] at hCast
  replace hCast := WfRewriter.createOp!_none_some hCast
  obtain ⟨_, _, _, hCast⟩ := hCast
  have Ecast := CtxExtends.of_createOp hCast opInBounds
  have hOpIn₁ := Ecast.inBounds op opInBounds
  have hCastIn₁ : castOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds _ hCast
  have hCastResIn₁ : (ValuePtr.opResult (castOp.getResult 0)).InBounds ctx₁.raw := by
    grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  have hBwCases : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  rcases hBwCases with hbw | hbw
  · -- ===== 64-bit: `castToReg → 3 stages (64-bit masks) → rev8 → castBack` =====
    rw [if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    simp only [Option.bind_eq_some_iff] at hpattern
    obtain ⟨⟨ctx₂, ops1, x1⟩, hSt1, hpattern⟩ := hpattern
    obtain ⟨⟨ctx₃, ops2, x2⟩, hSt2, hpattern⟩ := hpattern
    obtain ⟨⟨ctx₄, ops3, x3⟩, hSt3, hpattern⟩ := hpattern
    obtain ⟨⟨ctx₅, rev8Op⟩, hRev8, hpattern⟩ := hpattern
    replace hRev8 := WfRewriter.createOp!_none_some hRev8
    obtain ⟨_, _, _, hRev8⟩ := hRev8
    obtain ⟨⟨ctx₆, castBackOp⟩, hCastBack, hpattern⟩ := hpattern
    simp only [replaceWithRegLocal] at hCastBack
    replace hCastBack := WfRewriter.createOp!_none_some hCastBack
    obtain ⟨_, _, _, hCastBack⟩ := hCastBack
    obtain ⟨rfl, rfl, rfl⟩ := by simpa using hpattern
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Context extensions and their composites reaching the final context.
    have E₁ := bitreverseStageLocal_extends hOpIn₁ hSt1
    have hOpIn₂ := E₁.inBounds op hOpIn₁
    have E₂ := bitreverseStageLocal_extends hOpIn₂ hSt2
    have hOpIn₃ := E₂.inBounds op hOpIn₂
    have E₃ := bitreverseStageLocal_extends hOpIn₃ hSt3
    have hOpIn₄ := E₃.inBounds op hOpIn₃
    have Erev8 := CtxExtends.of_createOp hRev8 hOpIn₄
    have hOpIn₅ := Erev8.inBounds op hOpIn₄
    have Ecb := CtxExtends.of_createOp hCastBack hOpIn₅
    have FS5 : CtxExtends op ctx₅ ctx₆ := Ecb
    have FS4 : CtxExtends op ctx₄ ctx₆ := Erev8.trans FS5
    have FS3 : CtxExtends op ctx₃ ctx₆ := E₃.trans FS4
    have FS2 : CtxExtends op ctx₂ ctx₆ := E₂.trans FS3
    have FS1 : CtxExtends op ctx₁ ctx₆ := E₁.trans FS2
    have Ectx : CtxExtends op ctx ctx₆ := Ecast.trans FS1
    -- Read the refined operand in the target state.
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hOperandIn hxVal
        hDomCtx (Ectx.dominates operand hDomCtx) vNotOp
    -- In-bounds of the emitted ops in the final context.
    obtain ⟨hOps1In₂, hX1In₂⟩ := bitreverseStageLocal_inBounds hSt1
    obtain ⟨hOps2In₃, hX2In₃⟩ := bitreverseStageLocal_inBounds hSt2
    obtain ⟨hOps3In₄, hX3In₄⟩ := bitreverseStageLocal_inBounds hSt3
    have hOps1F : ∀ o ∈ ops1.toList, o.InBounds ctx₆.raw :=
      fun o ho => FS2.inBounds o (hOps1In₂ o ho)
    have hOps2F : ∀ o ∈ ops2.toList, o.InBounds ctx₆.raw :=
      fun o ho => FS3.inBounds o (hOps2In₃ o ho)
    have hOps3F : ∀ o ∈ ops3.toList, o.InBounds ctx₆.raw :=
      fun o ho => FS4.inBounds o (hOps3In₄ o ho)
    have hRev8In₅ : rev8Op.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds _ hRev8
    have hCBIn₆ : castBackOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds _ hCastBack
    -- Structural facts about the cast, `rev8`, and cast-back, in the final context.
    have hCastType : castOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
      rw [FS1.opType castOp hCastIn₁]; grind
    have hCastOperands : castOp.getOperands! ctx₆.raw = #[operand] := by
      rw [FS1.operands castOp hCastIn₁]; grind
    have hCastResTypes : castOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [FS1.resultTypes castOp hCastIn₁]; grind
    have hRev8Type : rev8Op.getOpType! ctx₆.raw = .riscv .rev8 := by
      rw [FS5.opType rev8Op hRev8In₅]; grind
    have hRev8Operands : rev8Op.getOperands! ctx₆.raw = #[x3] := by
      rw [FS5.operands rev8Op hRev8In₅]; grind
    have hRev8ResTypes : rev8Op.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [FS5.resultTypes rev8Op hRev8In₅]; grind
    have hCBType : ((op.getResult 0).get! ctx₅.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, isT⟩ : TypeAttr) := by
      have h1 := (Ecast.trans (E₁.trans (E₂.trans (E₃.trans Erev8)))).valueType
        (ValuePtr.opResult (op.getResult 0)) hResIn
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastBackType : castBackOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast :=
      by grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (rev8Op.getResult 0)] := by grind
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.integerType { bitwidth := 64 }, isT⟩] := by grind
    -- Execute the chain.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := FS1.inBounds castOp hCastIn₁)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨sA, hRun1, hMemA, hX1Val⟩ :=
      bitreverseStageLocal_run hOpIn₁ hSt1 FS2 hCastResIn₁ hRes₁ hOps1F
    obtain ⟨sB, hRun2, hMemB, hX2Val⟩ :=
      bitreverseStageLocal_run hOpIn₂ hSt2 FS3 hX1In₂ hX1Val hOps2F
    obtain ⟨sC, hRun3, hMemC, hX3Val⟩ :=
      bitreverseStageLocal_run hOpIn₃ hSt3 FS4 hX2In₃ hX2Val hOps3F
    obtain ⟨sD, hIRev8, hMemD, hRev8Res, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := sC) (inBounds := FS5.inBounds rev8Op hRev8In₅)
        (f := Data.RISCV.rev8) (fun _ _ _ _ => rfl) hRev8Type hRev8Operands hRev8ResTypes hX3Val
    obtain ⟨sE, hICB, hMemE, hCBRes, -⟩ :=
      interpretOp_castBack_forward (state := sD) (inBounds := hCBIn₆)
        hCastBackType hCastBackOperands hCastBackResTypes hRev8Res
    refine ⟨sE, ?_, by grind, ?_⟩
    · simp [Array.toList_append, interpretOpList_append, interpretOpList_cons, hI₁, hRun1,
        hRun2, hRun3, hIRev8, hICB, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
          (Data.RISCV.rev8
            (bitreverseStageReg 0x0f0f0f0f0f0f0f0f 4
              (bitreverseStageReg 0x3333333333333333 2
                (bitreverseStageReg 0x5555555555555555 1 (LLVM.Int.toReg xt))))) 64)], ?_, ?_⟩
      · simp [hCBRes, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bitreverse_isRefinedBy_toInt_rev8_swar hxtRef⟩
  · -- ===== 32-bit: `castToReg → 3 stages (32-bit masks) → rev8 → srli 32 → castBack` =====
    rw [if_pos hbw] at hpattern
    simp only [Option.bind_eq_some_iff] at hpattern
    obtain ⟨⟨ctx₂, ops1, x1⟩, hSt1, hpattern⟩ := hpattern
    obtain ⟨⟨ctx₃, ops2, x2⟩, hSt2, hpattern⟩ := hpattern
    obtain ⟨⟨ctx₄, ops3, x3⟩, hSt3, hpattern⟩ := hpattern
    obtain ⟨⟨ctx₅, rev8Op⟩, hRev8, hpattern⟩ := hpattern
    replace hRev8 := WfRewriter.createOp!_none_some hRev8
    obtain ⟨_, _, _, hRev8⟩ := hRev8
    obtain ⟨⟨ctx₆, srliOp⟩, hSrli, hpattern⟩ := hpattern
    replace hSrli := WfRewriter.createOp!_none_some hSrli
    obtain ⟨_, _, _, hSrli⟩ := hSrli
    obtain ⟨⟨ctx₇, castBackOp⟩, hCastBack, hpattern⟩ := hpattern
    simp only [replaceWithRegLocal] at hCastBack
    replace hCastBack := WfRewriter.createOp!_none_some hCastBack
    obtain ⟨_, _, _, hCastBack⟩ := hCastBack
    obtain ⟨rfl, rfl, rfl⟩ := by simpa using hpattern
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Context extensions and their composites reaching the final context.
    have E₁ := bitreverseStageLocal_extends hOpIn₁ hSt1
    have hOpIn₂ := E₁.inBounds op hOpIn₁
    have E₂ := bitreverseStageLocal_extends hOpIn₂ hSt2
    have hOpIn₃ := E₂.inBounds op hOpIn₂
    have E₃ := bitreverseStageLocal_extends hOpIn₃ hSt3
    have hOpIn₄ := E₃.inBounds op hOpIn₃
    have Erev8 := CtxExtends.of_createOp hRev8 hOpIn₄
    have hOpIn₅ := Erev8.inBounds op hOpIn₄
    have Esrli := CtxExtends.of_createOp hSrli hOpIn₅
    have hOpIn₆ := Esrli.inBounds op hOpIn₅
    have Ecb := CtxExtends.of_createOp hCastBack hOpIn₆
    have FS6 : CtxExtends op ctx₆ ctx₇ := Ecb
    have FS5 : CtxExtends op ctx₅ ctx₇ := Esrli.trans FS6
    have FS4 : CtxExtends op ctx₄ ctx₇ := Erev8.trans FS5
    have FS3 : CtxExtends op ctx₃ ctx₇ := E₃.trans FS4
    have FS2 : CtxExtends op ctx₂ ctx₇ := E₂.trans FS3
    have FS1 : CtxExtends op ctx₁ ctx₇ := E₁.trans FS2
    have Ectx : CtxExtends op ctx ctx₇ := Ecast.trans FS1
    -- Read the refined operand in the target state.
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hOperandIn hxVal
        hDomCtx (Ectx.dominates operand hDomCtx) vNotOp
    -- In-bounds of the emitted ops in the final context.
    obtain ⟨hOps1In₂, hX1In₂⟩ := bitreverseStageLocal_inBounds hSt1
    obtain ⟨hOps2In₃, hX2In₃⟩ := bitreverseStageLocal_inBounds hSt2
    obtain ⟨hOps3In₄, hX3In₄⟩ := bitreverseStageLocal_inBounds hSt3
    have hOps1F : ∀ o ∈ ops1.toList, o.InBounds ctx₇.raw :=
      fun o ho => FS2.inBounds o (hOps1In₂ o ho)
    have hOps2F : ∀ o ∈ ops2.toList, o.InBounds ctx₇.raw :=
      fun o ho => FS3.inBounds o (hOps2In₃ o ho)
    have hOps3F : ∀ o ∈ ops3.toList, o.InBounds ctx₇.raw :=
      fun o ho => FS4.inBounds o (hOps3In₄ o ho)
    have hRev8In₅ : rev8Op.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds _ hRev8
    have hSrliIn₆ : srliOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds _ hSrli
    have hCBIn₇ : castBackOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds _ hCastBack
    -- Structural facts about the cast, `rev8`, `srli`, and cast-back, in the final context.
    have hCastType : castOp.getOpType! ctx₇.raw = .builtin .unrealized_conversion_cast := by
      rw [FS1.opType castOp hCastIn₁]; grind
    have hCastOperands : castOp.getOperands! ctx₇.raw = #[operand] := by
      rw [FS1.operands castOp hCastIn₁]; grind
    have hCastResTypes : castOp.getResultTypes! ctx₇.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [FS1.resultTypes castOp hCastIn₁]; grind
    have hRev8Type : rev8Op.getOpType! ctx₇.raw = .riscv .rev8 := by
      rw [FS5.opType rev8Op hRev8In₅]; grind
    have hRev8Operands : rev8Op.getOperands! ctx₇.raw = #[x3] := by
      rw [FS5.operands rev8Op hRev8In₅]; grind
    have hRev8ResTypes : rev8Op.getResultTypes! ctx₇.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [FS5.resultTypes rev8Op hRev8In₅]; grind
    have hSrliType : srliOp.getOpType! ctx₇.raw = .riscv .srli := by
      rw [FS6.opType srliOp hSrliIn₆]; grind
    have hSrliOperands :
        srliOp.getOperands! ctx₇.raw = #[ValuePtr.opResult (rev8Op.getResult 0)] := by
      rw [FS6.operands srliOp hSrliIn₆]; grind
    have hSrliResTypes : srliOp.getResultTypes! ctx₇.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [FS6.resultTypes srliOp hSrliIn₆]; grind
    have hSrliProps : srliOp.getProperties! ctx₇.raw (.riscv .srli)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 32 (IntegerType.mk 64)) := by
      rw [FS6.properties srliOp hSrliIn₆]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hSrli (operation := srliOp)]
    have hSrliImm : BitVec.ofInt 6 (srliOp.getProperties! ctx₇.raw (.riscv .srli)).value.value
        = BitVec.ofInt 6 32 := by rw [hSrliProps]
    have hCBType : ((op.getResult 0).get! ctx₆.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, isT⟩ : TypeAttr) := by
      have h1 := (Ecast.trans (E₁.trans (E₂.trans (E₃.trans (Erev8.trans Esrli))))).valueType
        (ValuePtr.opResult (op.getResult 0)) hResIn
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastBackType : castBackOp.getOpType! ctx₇.raw = .builtin .unrealized_conversion_cast :=
      by grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₇.raw = #[ValuePtr.opResult (srliOp.getResult 0)] := by grind
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₇.raw
        = #[⟨Attribute.integerType { bitwidth := 32 }, isT⟩] := by grind
    -- Execute the chain.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := FS1.inBounds castOp hCastIn₁)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨sA, hRun1, hMemA, hX1Val⟩ :=
      bitreverseStageLocal_run hOpIn₁ hSt1 FS2 hCastResIn₁ hRes₁ hOps1F
    obtain ⟨sB, hRun2, hMemB, hX2Val⟩ :=
      bitreverseStageLocal_run hOpIn₂ hSt2 FS3 hX1In₂ hX1Val hOps2F
    obtain ⟨sC, hRun3, hMemC, hX3Val⟩ :=
      bitreverseStageLocal_run hOpIn₃ hSt3 FS4 hX2In₃ hX2Val hOps3F
    obtain ⟨sD, hIRev8, hMemD, hRev8Res, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := sC) (inBounds := FS5.inBounds rev8Op hRev8In₅)
        (f := Data.RISCV.rev8) (fun _ _ _ _ => rfl) hRev8Type hRev8Operands hRev8ResTypes hX3Val
    obtain ⟨sE, hISrli, hMemE, hSrliRes, -⟩ :=
      interpretOp_riscv_srli_forward (state := sD) (inBounds := FS6.inBounds srliOp hSrliIn₆)
        (k := BitVec.ofInt 6 32) hSrliType hSrliImm hSrliOperands hSrliResTypes hRev8Res
    obtain ⟨sF, hICB, hMemF, hCBRes, -⟩ :=
      interpretOp_castBack_forward (state := sE) (inBounds := hCBIn₇)
        hCastBackType hCastBackOperands hCastBackResTypes hSrliRes
    refine ⟨sF, ?_, by grind, ?_⟩
    · simp [Array.toList_append, interpretOpList_append, interpretOpList_cons, hI₁, hRun1,
        hRun2, hRun3, hIRev8, hISrli, hICB, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 32 (RISCV.Reg.toInt
          (Data.RISCV.srli (BitVec.ofInt 6 32)
            (Data.RISCV.rev8
              (bitreverseStageReg 0x0f0f0f0f 4
                (bitreverseStageReg 0x33333333 2
                  (bitreverseStageReg 0x55555555 1 (LLVM.Int.toReg xt)))))) 32)], ?_, ?_⟩
      · simp [hCBRes, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bitreverse_isRefinedBy_toInt_srli_rev8_swar hxtRef⟩

/--
info: 'Veir.bitreverse_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 bitreverse_isRefinedBy_toInt_rev8_swar._native.bv_decide.ax_1_6,
 bitreverse_isRefinedBy_toInt_srli_rev8_swar._native.bv_decide.ax_1_6,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms bitreverse_local_preservesSemantics

end Veir
