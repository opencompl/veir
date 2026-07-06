import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas

import Veir.Meta.BVDecide

/-!
  Correctness proofs for the RISC-V combines in `Combine.lean`.
-/

namespace Veir.Data.RISCV

/--
  Prove the correctness of the `right_identity_zero_add` combine.
-/
theorem right_identity_zero_add:
    (RISCV.add lhs (Data.RISCV.li (BitVec.ofInt 64 0))) = lhs := by
  veir_bv_decide

/--
  Prove the correctness of the `srl_sra_signbit` combine, phrased directly on the
  already-selected RISC-V register ops the combine rewrites: `riscv.srli 63
  (riscv.srai shamt x) = riscv.srli 63 x`. An arithmetic right shift by any amount
  `shamt` never changes the top bit, so a subsequent logical shift by 63 (which
  keeps only that bit) gives the same result as skipping the `srai` entirely. The
  RISC-V ops are total, so this is an exact equality. Mirrors LLVM's generic
  `DAGCombiner::visitSRL` rule `fold (srl (sra X, Y), 31) -> (srl X, 31)`.
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L11628-L11633
-/
theorem srl_sra_signbit {x : Reg} {shamt : BitVec 6} :
    RISCV.srli 63 (RISCV.srai shamt x) = RISCV.srli 63 x := by
  veir_bv_decide

/--
  Prove the correctness of the `srlw_sraw_signbit` combine (the `i32` analogue of
  `srl_sra_signbit`, at bit 31): `riscv.srliw 31 (riscv.sraiw shamt x) =
  riscv.srliw 31 x`.
-/
theorem srlw_sraw_signbit {x : Reg} {shamt : BitVec 5} :
    RISCV.srliw 31 (RISCV.sraiw shamt x) = RISCV.srliw 31 x := by
  veir_bv_decide

/--
  Prove the correctness of the `drop_slli_srli_boolGen` family: for a
  comparison op producing exactly 0 or 1, `riscv.slli 63` isolates its bit 0
  into bit 63 and `riscv.srli 63` moves it straight back, so the round trip is
  the identity and both shifts can be dropped entirely.
-/
theorem drop_slli_srli_slt {rs1 rs2 : Reg} :
    RISCV.srli 63 (RISCV.slli 63 (RISCV.slt rs2 rs1)) = RISCV.slt rs2 rs1 := by
  veir_bv_decide

/-- `sltu` analogue of `drop_slli_srli_slt`. -/
theorem drop_slli_srli_sltu {rs1 rs2 : Reg} :
    RISCV.srli 63 (RISCV.slli 63 (RISCV.sltu rs2 rs1)) = RISCV.sltu rs2 rs1 := by
  veir_bv_decide

/-- `slti` analogue of `drop_slli_srli_slt`. -/
theorem drop_slli_srli_slti {rs1 : Reg} {imm : BitVec 12} :
    RISCV.srli 63 (RISCV.slli 63 (RISCV.slti imm rs1)) = RISCV.slti imm rs1 := by
  veir_bv_decide

/-- `sltiu` analogue of `drop_slli_srli_slt`. -/
theorem drop_slli_srli_sltiu {rs1 : Reg} {imm : BitVec 12} :
    RISCV.srli 63 (RISCV.slli 63 (RISCV.sltiu imm rs1)) = RISCV.sltiu imm rs1 := by
  veir_bv_decide

/-- `seqz` analogue of `drop_slli_srli_slt`. -/
theorem drop_slli_srli_seqz {rs1 : Reg} :
    RISCV.srli 63 (RISCV.slli 63 (RISCV.seqz rs1)) = RISCV.seqz rs1 := by
  veir_bv_decide

/-- `snez` analogue of `drop_slli_srli_slt`. -/
theorem drop_slli_srli_snez {rs1 : Reg} :
    RISCV.srli 63 (RISCV.slli 63 (RISCV.snez rs1)) = RISCV.snez rs1 := by
  veir_bv_decide

/-- `sltz` analogue of `drop_slli_srli_slt`. -/
theorem drop_slli_srli_sltz {rs1 : Reg} :
    RISCV.srli 63 (RISCV.slli 63 (RISCV.sltz rs1)) = RISCV.sltz rs1 := by
  veir_bv_decide

/-- `sgtz` analogue of `drop_slli_srli_slt`. -/
theorem drop_slli_srli_sgtz {rs1 : Reg} :
    RISCV.srli 63 (RISCV.slli 63 (RISCV.sgtz rs1)) = RISCV.sgtz rs1 := by
  veir_bv_decide

/-- Prove the correctness of `riscv.zextw (riscv.zextw x) -> riscv.zextw x`. -/
theorem zextw_zextw {x : Reg} :
    RISCV.zextw (RISCV.zextw x) = RISCV.zextw x := by
  veir_bv_decide

/--
  Prove the correctness of dropping a `riscv.zextw` from the `rs2` operand of
  `riscv.addw`. The instruction reads only bits 31:0 of both operands.
-/
theorem drop_zextw_addw_rs2 {rs1 rs2 : Reg} :
    RISCV.addw (RISCV.zextw rs2) rs1 = RISCV.addw rs2 rs1 := by
  veir_bv_decide

/--
  Prove the correctness of dropping a `riscv.zextw` from the `rs1` operand of
  `riscv.addw`.
-/
theorem drop_zextw_addw_rs1 {rs1 rs2 : Reg} :
    RISCV.addw rs2 (RISCV.zextw rs1) = RISCV.addw rs2 rs1 := by
  veir_bv_decide

/--
  Convenience form for the common case where both `riscv.addw` operands are
  defined by `riscv.zextw`.
-/
theorem drop_zextw_addw {rs1 rs2 : Reg} :
    RISCV.addw (RISCV.zextw rs2) (RISCV.zextw rs1) = RISCV.addw rs2 rs1 := by
  veir_bv_decide

/--
  Prove the correctness of `riscv.addiw (riscv.zextw x), imm ->
  riscv.addiw x, imm`. `addiw` reads only bits 31:0 of its register operand.
-/
theorem drop_zextw_addiw {rs1 : Reg} {imm : BitVec 12} :
    RISCV.addiw imm (RISCV.zextw rs1) = RISCV.addiw imm rs1 := by
  veir_bv_decide

/--
  Prove the correctness of `riscv.roriw (riscv.zextw x), imm ->
  riscv.roriw x, imm`. `roriw` rotates only the low 32-bit word.
-/
theorem drop_zextw_roriw {rs1 : Reg} {shamt : BitVec 5} :
    RISCV.roriw shamt (RISCV.zextw rs1) = RISCV.roriw shamt rs1 := by
  veir_bv_decide

/--
  Prove the correctness of `riscv.srliw (riscv.zextw x), imm ->
  riscv.srliw x, imm`. `srliw` shifts only the low 32-bit word.
-/
theorem drop_zextw_srliw {rs1 : Reg} {shamt : BitVec 5} :
    RISCV.srliw shamt (RISCV.zextw rs1) = RISCV.srliw shamt rs1 := by
  veir_bv_decide

/--
  Prove the correctness of `riscv.sextw (riscv.zextw x) -> riscv.sextw x`.
  `sextw` is `addiw 0`, which reads only bits 31:0 of its operand.
-/
theorem drop_zextw_sextw {rs1 : Reg} :
    RISCV.sextw (RISCV.zextw rs1) = RISCV.sextw rs1 := by
  veir_bv_decide

/--
  Prove the correctness of dropping an outer `riscv.zextw` wrapping a bitwise
  `and` whose both operands are themselves `riscv.zextw`-guarded: each source has
  bits 63:32 cleared, so their `and` does too.
-/
theorem zextw_and {a b : Reg} :
    RISCV.zextw (RISCV.and (RISCV.zextw a) (RISCV.zextw b)) =
      RISCV.and (RISCV.zextw a) (RISCV.zextw b) := by
  veir_bv_decide

/-- `or` analogue of `zextw_and`. -/
theorem zextw_or {a b : Reg} :
    RISCV.zextw (RISCV.or (RISCV.zextw a) (RISCV.zextw b)) =
      RISCV.or (RISCV.zextw a) (RISCV.zextw b) := by
  veir_bv_decide

/-- `xor` analogue of `zextw_and`. -/
theorem zextw_xor {a b : Reg} :
    RISCV.zextw (RISCV.xor (RISCV.zextw a) (RISCV.zextw b)) =
      RISCV.xor (RISCV.zextw a) (RISCV.zextw b) := by
  veir_bv_decide

/--
  Prove the correctness of dropping a `riscv.zextw` from the value operand of
  `riscv.sw`: a word store only reads bits 31:0 of its source register (see the
  `.sw` case of `Interpreter.Basic.exec`, which stores just the low 4 bytes), and
  `zextw` leaves bits 31:0 unchanged -- it only clears bits 63:32.
-/
theorem drop_zextw_sw {rs1 : Reg} :
    (RISCV.zextw rs1).val.extractLsb 31 0 = rs1.val.extractLsb 31 0 := by
  veir_bv_decide

/--
  Prove the correctness of the `zextw_x0` combine: zero-extending the value 0
  (which is what the hard-wired zero register `x0` reads as -- an interpreter
  fact, not a `Reg`-algebra one, so it isn't itself part of this theorem) is a
  no-op.
-/
theorem zextw_x0 :
    RISCV.zextw (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.li (BitVec.ofInt 64 0) := by
  veir_bv_decide

/--
  Prove the correctness of the `zextw_li_low32` combine. The combine checks
  `0 ≤ v < 2^32` on the `Int` immediate `v`; that range is exactly the one where
  `BitVec.ofInt 64 v` (the value `riscv.li` materializes, see
  `Interpreter.Basic.exec`'s `.li` case) has bits 63:32 already clear, which is
  the hypothesis `h` below.
-/
theorem zextw_li_low32 {x : BitVec 64} (h : x.extractLsb 63 32 = 0#32) :
    RISCV.zextw (Data.RISCV.li x) = Data.RISCV.li x := by
  veir_bv_decide

/-! ## Sext-side mirrors of the `zextw` combines.

    `sextw` leaves bits 31:0 unchanged (it only rewrites bits 63:32 to a copy of
    bit 31), so every combine justified by "the consumer reads only bits 31:0"
    holds verbatim with `sextw` in place of `zextw`. The redundancy combines
    (idempotence, `x0`, constant) transfer too, with the constant guard shifting
    from the unsigned to the signed 32-bit range. -/

/-- Sext mirror of `drop_zextw_addw` (`rs2` operand). -/
theorem drop_sextw_addw_rs2 {rs1 rs2 : Reg} :
    RISCV.addw (RISCV.sextw rs2) rs1 = RISCV.addw rs2 rs1 := by
  veir_bv_decide

/-- Sext mirror of `drop_zextw_addw` (`rs1` operand). -/
theorem drop_sextw_addw_rs1 {rs1 rs2 : Reg} :
    RISCV.addw rs2 (RISCV.sextw rs1) = RISCV.addw rs2 rs1 := by
  veir_bv_decide

/-- Convenience form with both `riscv.addw` operands `sextw`-defined. -/
theorem drop_sextw_addw {rs1 rs2 : Reg} :
    RISCV.addw (RISCV.sextw rs2) (RISCV.sextw rs1) = RISCV.addw rs2 rs1 := by
  veir_bv_decide

/-- Sext mirror of `drop_zextw_addiw`. -/
theorem drop_sextw_addiw {rs1 : Reg} {imm : BitVec 12} :
    RISCV.addiw imm (RISCV.sextw rs1) = RISCV.addiw imm rs1 := by
  veir_bv_decide

/-- Sext mirror of `drop_zextw_roriw`. -/
theorem drop_sextw_roriw {rs1 : Reg} {shamt : BitVec 5} :
    RISCV.roriw shamt (RISCV.sextw rs1) = RISCV.roriw shamt rs1 := by
  veir_bv_decide

/-- Sext mirror of `drop_zextw_srliw`. -/
theorem drop_sextw_srliw {rs1 : Reg} {shamt : BitVec 5} :
    RISCV.srliw shamt (RISCV.sextw rs1) = RISCV.srliw shamt rs1 := by
  veir_bv_decide

/-- `drop_sextw_zextw`: `zextw` keeps only bits 31:0, so a `sextw` feeding it is
    redundant. (Mirror of `drop_zextw_sextw` with the extensions swapped.) -/
theorem drop_sextw_zextw {rs1 : Reg} :
    RISCV.zextw (RISCV.sextw rs1) = RISCV.zextw rs1 := by
  veir_bv_decide

/-- `sextw_sextw`: sign extension is idempotent. -/
theorem sextw_sextw {x : Reg} :
    RISCV.sextw (RISCV.sextw x) = RISCV.sextw x := by
  veir_bv_decide

/-- Sext mirror of `zextw_and`: `and` of two sign-extended operands is already
    sign-extended (bit i≥32 of the result is `a₃₁ & b₃₁`, which equals result
    bit 31), so the outer `sextw` is redundant. -/
theorem sextw_and {a b : Reg} :
    RISCV.sextw (RISCV.and (RISCV.sextw a) (RISCV.sextw b)) =
      RISCV.and (RISCV.sextw a) (RISCV.sextw b) := by
  veir_bv_decide

/-- `or` analogue of `sextw_and`. -/
theorem sextw_or {a b : Reg} :
    RISCV.sextw (RISCV.or (RISCV.sextw a) (RISCV.sextw b)) =
      RISCV.or (RISCV.sextw a) (RISCV.sextw b) := by
  veir_bv_decide

/-- `xor` analogue of `sextw_and`. -/
theorem sextw_xor {a b : Reg} :
    RISCV.sextw (RISCV.xor (RISCV.sextw a) (RISCV.sextw b)) =
      RISCV.xor (RISCV.sextw a) (RISCV.sextw b) := by
  veir_bv_decide

/-- Sext mirror of `drop_zextw_sw`: a word store reads only bits 31:0 of its
    value operand, which `sextw` leaves unchanged. -/
theorem drop_sextw_sw {rs1 : Reg} :
    (RISCV.sextw rs1).val.extractLsb 31 0 = rs1.val.extractLsb 31 0 := by
  veir_bv_decide

/-- Sext mirror of `zextw_x0`: sign-extending the value 0 (what `x0` reads as) is
    a no-op. -/
theorem sextw_x0 :
    RISCV.sextw (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.li (BitVec.ofInt 64 0) := by
  veir_bv_decide

/-- Sext mirror of `zextw_li_low32`. The combine checks `-2^31 ≤ v < 2^31` on the
    `Int` immediate `v`; that signed 32-bit range is exactly where
    `BitVec.ofInt 64 v` already equals the sign-extension of its own low 32 bits,
    which is the hypothesis `h` below. -/
theorem sextw_li_low32 {x : BitVec 64} (h : (x.extractLsb 31 0).signExtend 64 = x) :
    RISCV.sextw (Data.RISCV.li x) = Data.RISCV.li x := by
  veir_bv_decide

end Veir.Data.RISCV
