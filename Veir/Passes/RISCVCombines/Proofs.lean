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
  `and` when only the *left* operand is `riscv.zextw`-guarded (the right operand
  `b` is arbitrary): `and` forces a result bit to zero whenever either operand's
  bit is zero, so the guarded left operand alone clears bits 63:32 of the result.
  This subsumes the both-operands-guarded case, and is what lets `zextw_and` fire
  with `oneOperandSuffices := true`.
-/
theorem zextw_and_left {a b : Reg} :
    RISCV.zextw (RISCV.and (RISCV.zextw a) b) = RISCV.and (RISCV.zextw a) b := by
  veir_bv_decide

/-- Right-operand mirror of `zextw_and_left`. -/
theorem zextw_and_right {a b : Reg} :
    RISCV.zextw (RISCV.and a (RISCV.zextw b)) = RISCV.and a (RISCV.zextw b) := by
  veir_bv_decide

/--
  The both-operands-guarded case of `zextw_and`, kept for symmetry with the
  `or`/`xor` proofs below (each source has bits 63:32 cleared, so their `and`
  does too). Subsumed by `zextw_and_left`/`zextw_and_right`.
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

/-! ## Byte- and half-word mirrors of the `zextw`/`sextw` combines.

    Every `zextw`/`sextw` combine that rests only on "the extension establishes a
    fixed pattern in the bits above its width, which some consumer ignores /
    another extension re-establishes" holds verbatim at the 8- and 16-bit widths.
    `zextb`/`zexth` clear bits 63:8 / 63:16; `sextb`/`sexth` set them to bit 7 /
    bit 15. The `*w`-only combines (`addw`/`addiw`/`roriw`/`srliw`/cross-`w`) are
    deliberately absent: those consumers read bits 31:0, which the narrower
    extensions do *not* preserve. -/

/-- Idempotence at the byte/half widths (mirrors `zextw_zextw`/`sextw_sextw`). -/
theorem zextb_zextb {x : Reg} : RISCV.zextb (RISCV.zextb x) = RISCV.zextb x := by
  veir_bv_decide

theorem zexth_zexth {x : Reg} : RISCV.zexth (RISCV.zexth x) = RISCV.zexth x := by
  veir_bv_decide

theorem sextb_sextb {x : Reg} : RISCV.sextb (RISCV.sextb x) = RISCV.sextb x := by
  veir_bv_decide

theorem sexth_sexth {x : Reg} : RISCV.sexth (RISCV.sexth x) = RISCV.sexth x := by
  veir_bv_decide

/-- Byte/half mirrors of `zextw_and_left`/`_right` and the `or`/`xor` folds: a
    zero-extension over a bitwise op is redundant when the operands clear the same
    high bits (`and` needs only one such operand; `or`/`xor` need both). -/
theorem zextb_and_left {a b : Reg} :
    RISCV.zextb (RISCV.and (RISCV.zextb a) b) = RISCV.and (RISCV.zextb a) b := by
  veir_bv_decide

theorem zextb_and_right {a b : Reg} :
    RISCV.zextb (RISCV.and a (RISCV.zextb b)) = RISCV.and a (RISCV.zextb b) := by
  veir_bv_decide

theorem zextb_or {a b : Reg} :
    RISCV.zextb (RISCV.or (RISCV.zextb a) (RISCV.zextb b)) =
      RISCV.or (RISCV.zextb a) (RISCV.zextb b) := by
  veir_bv_decide

theorem zextb_xor {a b : Reg} :
    RISCV.zextb (RISCV.xor (RISCV.zextb a) (RISCV.zextb b)) =
      RISCV.xor (RISCV.zextb a) (RISCV.zextb b) := by
  veir_bv_decide

theorem zexth_and_left {a b : Reg} :
    RISCV.zexth (RISCV.and (RISCV.zexth a) b) = RISCV.and (RISCV.zexth a) b := by
  veir_bv_decide

theorem zexth_and_right {a b : Reg} :
    RISCV.zexth (RISCV.and a (RISCV.zexth b)) = RISCV.and a (RISCV.zexth b) := by
  veir_bv_decide

theorem zexth_or {a b : Reg} :
    RISCV.zexth (RISCV.or (RISCV.zexth a) (RISCV.zexth b)) =
      RISCV.or (RISCV.zexth a) (RISCV.zexth b) := by
  veir_bv_decide

theorem zexth_xor {a b : Reg} :
    RISCV.zexth (RISCV.xor (RISCV.zexth a) (RISCV.zexth b)) =
      RISCV.xor (RISCV.zexth a) (RISCV.zexth b) := by
  veir_bv_decide

/-- Byte/half sext mirrors of `sextw_and`/`_or`/`_xor`: both operands must be
    sign-extended (a single one can't force bits above the width to match the sign
    bit). -/
theorem sextb_and {a b : Reg} :
    RISCV.sextb (RISCV.and (RISCV.sextb a) (RISCV.sextb b)) =
      RISCV.and (RISCV.sextb a) (RISCV.sextb b) := by
  veir_bv_decide

theorem sextb_or {a b : Reg} :
    RISCV.sextb (RISCV.or (RISCV.sextb a) (RISCV.sextb b)) =
      RISCV.or (RISCV.sextb a) (RISCV.sextb b) := by
  veir_bv_decide

theorem sextb_xor {a b : Reg} :
    RISCV.sextb (RISCV.xor (RISCV.sextb a) (RISCV.sextb b)) =
      RISCV.xor (RISCV.sextb a) (RISCV.sextb b) := by
  veir_bv_decide

theorem sexth_and {a b : Reg} :
    RISCV.sexth (RISCV.and (RISCV.sexth a) (RISCV.sexth b)) =
      RISCV.and (RISCV.sexth a) (RISCV.sexth b) := by
  veir_bv_decide

theorem sexth_or {a b : Reg} :
    RISCV.sexth (RISCV.or (RISCV.sexth a) (RISCV.sexth b)) =
      RISCV.or (RISCV.sexth a) (RISCV.sexth b) := by
  veir_bv_decide

theorem sexth_xor {a b : Reg} :
    RISCV.sexth (RISCV.xor (RISCV.sexth a) (RISCV.sexth b)) =
      RISCV.xor (RISCV.sexth a) (RISCV.sexth b) := by
  veir_bv_decide

/-- Store mirrors of `drop_zextw_sw`/`drop_sextw_sw`: `sh` writes only bits 15:0
    and `sb` only bits 7:0, which the matching-width extension leaves unchanged. -/
theorem drop_zexth_sh {rs1 : Reg} :
    (RISCV.zexth rs1).val.extractLsb 15 0 = rs1.val.extractLsb 15 0 := by
  veir_bv_decide

theorem drop_sexth_sh {rs1 : Reg} :
    (RISCV.sexth rs1).val.extractLsb 15 0 = rs1.val.extractLsb 15 0 := by
  veir_bv_decide

theorem drop_zextb_sb {rs1 : Reg} :
    (RISCV.zextb rs1).val.extractLsb 7 0 = rs1.val.extractLsb 7 0 := by
  veir_bv_decide

theorem drop_sextb_sb {rs1 : Reg} :
    (RISCV.sextb rs1).val.extractLsb 7 0 = rs1.val.extractLsb 7 0 := by
  veir_bv_decide

/-- Byte/half mirrors of `zextw_x0`/`sextw_x0`: extending the value 0 (what `x0`
    reads as) is a no-op at any width. -/
theorem zextb_x0 :
    RISCV.zextb (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.li (BitVec.ofInt 64 0) := by
  veir_bv_decide

theorem zexth_x0 :
    RISCV.zexth (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.li (BitVec.ofInt 64 0) := by
  veir_bv_decide

theorem sextb_x0 :
    RISCV.sextb (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.li (BitVec.ofInt 64 0) := by
  veir_bv_decide

theorem sexth_x0 :
    RISCV.sexth (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.li (BitVec.ofInt 64 0) := by
  veir_bv_decide

/-- Byte/half mirrors of `zextw_li_low32`/`sextw_li_low32`. The combines check the
    unsigned range `[0, 2^width)` (zero-extension) or signed range
    `[-2^(width-1), 2^(width-1))` (sign-extension) on the `Int` immediate; the
    hypotheses below are the corresponding facts about the materialized value. -/
theorem zextb_li_low8 {x : BitVec 64} (h : x.extractLsb 63 8 = 0#56) :
    RISCV.zextb (Data.RISCV.li x) = Data.RISCV.li x := by
  veir_bv_decide

theorem zexth_li_low16 {x : BitVec 64} (h : x.extractLsb 63 16 = 0#48) :
    RISCV.zexth (Data.RISCV.li x) = Data.RISCV.li x := by
  veir_bv_decide

theorem sextb_li_low8 {x : BitVec 64} (h : (x.extractLsb 7 0).signExtend 64 = x) :
    RISCV.sextb (Data.RISCV.li x) = Data.RISCV.li x := by
  veir_bv_decide

theorem sexth_li_low16 {x : BitVec 64} (h : (x.extractLsb 15 0).signExtend 64 = x) :
    RISCV.sexth (Data.RISCV.li x) = Data.RISCV.li x := by
  veir_bv_decide

/-- Operand-order variant of `right_identity_zero_add`: the RISC-V interpreter computes
    `riscv.add x y` as `RISCV.add op2 op1` (operands reversed), so for `riscv.add x (riscv.li 0)`
    the materialized result is `RISCV.add (li 0) x` with `li 0` as the *first* argument. Needed by
    `right_identity_zero_add_local_preservesSemantics` in `CombineSemantics.lean`. -/
theorem right_identity_zero_add_comm {lhs : Reg} :
    RISCV.add (Data.RISCV.li (BitVec.ofInt 64 0)) lhs = lhs := by
  veir_bv_decide

/-! ## `Int`-range forms of the `ext (li v)` folds.

    The `ext_li_range`/`zextw_li_low32`/`sextw_li_low32` combines guard on the *integer* immediate
    `v` (`lo ≤ v < hi`); their correctness obligation is the register equality
    `ext (li (BitVec.ofInt 64 v)) = li (BitVec.ofInt 64 v)`. Each lemma below bridges the `Int` range
    to the `BitVec` hypothesis of the corresponding `*_li_low*` lemma above: for a zero-extension the
    high field of `BitVec.ofInt 64 v` is clear; for a sign-extension `BitVec.ofInt 64 v` equals the
    sign-extension of its own low `width` bits. These are what
    `ext_li_range_local_preservesSemantics` (and the `zextw`/`sextw` instances) consume. -/

theorem zextb_li_ofInt {v : Int} (h0 : 0 ≤ v) (h1 : v < 256) :
    RISCV.zextb (Data.RISCV.li (BitVec.ofInt 64 v)) = Data.RISCV.li (BitVec.ofInt 64 v) := by
  apply zextb_li_low8
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

theorem zexth_li_ofInt {v : Int} (h0 : 0 ≤ v) (h1 : v < 65536) :
    RISCV.zexth (Data.RISCV.li (BitVec.ofInt 64 v)) = Data.RISCV.li (BitVec.ofInt 64 v) := by
  apply zexth_li_low16
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

theorem zextw_li_ofInt {v : Int} (h0 : 0 ≤ v) (h1 : v < 4294967296) :
    RISCV.zextw (Data.RISCV.li (BitVec.ofInt 64 v)) = Data.RISCV.li (BitVec.ofInt 64 v) := by
  apply zextw_li_low32
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

theorem sextb_li_ofInt {v : Int} (h0 : -128 ≤ v) (h1 : v < 128) :
    RISCV.sextb (Data.RISCV.li (BitVec.ofInt 64 v)) = Data.RISCV.li (BitVec.ofInt 64 v) := by
  apply sextb_li_low8
  have hA : (BitVec.ofInt 64 v).extractLsb 7 0 = BitVec.ofInt 8 v := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
      Nat.shiftRight_zero, Nat.reducePow]
    omega
  rw [hA]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt, BitVec.toInt_ofInt,
    show (2 ^ 8 : Nat) = 256 from rfl, show (2 ^ 64 : Nat) = 18446744073709551616 from rfl]
  simp only [Int.bmod]
  omega

theorem sexth_li_ofInt {v : Int} (h0 : -32768 ≤ v) (h1 : v < 32768) :
    RISCV.sexth (Data.RISCV.li (BitVec.ofInt 64 v)) = Data.RISCV.li (BitVec.ofInt 64 v) := by
  apply sexth_li_low16
  have hA : (BitVec.ofInt 64 v).extractLsb 15 0 = BitVec.ofInt 16 v := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
      Nat.shiftRight_zero, Nat.reducePow]
    omega
  rw [hA]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt, BitVec.toInt_ofInt,
    show (2 ^ 16 : Nat) = 65536 from rfl, show (2 ^ 64 : Nat) = 18446744073709551616 from rfl]
  simp only [Int.bmod]
  omega

theorem sextw_li_ofInt {v : Int} (h0 : -2147483648 ≤ v) (h1 : v < 2147483648) :
    RISCV.sextw (Data.RISCV.li (BitVec.ofInt 64 v)) = Data.RISCV.li (BitVec.ofInt 64 v) := by
  apply sextw_li_low32
  have hA : (BitVec.ofInt 64 v).extractLsb 31 0 = BitVec.ofInt 32 v := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
      Nat.shiftRight_zero, Nat.reducePow]
    omega
  rw [hA]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt, BitVec.toInt_ofInt,
    show (2 ^ 32 : Nat) = 4294967296 from rfl, show (2 ^ 64 : Nat) = 18446744073709551616 from rfl]
  simp only [Int.bmod]
  omega

/-- Correctness of the `li_zero_to_x0` combine at the data level: materializing `0`
    with `riscv.li 0` yields exactly what the hard-wired zero register `x0` reads
    (`⟨0⟩`). `Data.RISCV.li (BitVec.ofInt 64 0) = ⟨BitVec.ofInt 64 0⟩` and
    `BitVec.ofInt 64 0 = 0#64`. Needed by `li_zero_to_x0_local_preservesSemantics`
    in `CombineSemantics.lean`. (The `0#64`-phrased mirror `li_zero_eq_x0` lives in
    `Veir/Passes/InstructionSelection/Proofs.lean`.) -/
theorem li_ofInt_zero_eq_x0 : Data.RISCV.li (BitVec.ofInt 64 0) = ⟨0⟩ := by
  simp only [Data.RISCV.li, Reg.mk.injEq]
  bv_decide

end Veir.Data.RISCV
