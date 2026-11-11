module

public import Veir.Data.RISCV.Reg.Basic
public import Veir.Data.RISCV.Reg.Lemmas
public import Veir.ForLean
public import Veir.Dialects.RISCV.Properties
public import Veir.Passes.RISCVCombines.Combine

import Veir.Meta.Tactic.BVDecide
import Std.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide
meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Lemmas
import all Veir.Passes.RISCVCombines.Combine
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.GlobalOpInfo

public section

/-!
  Correctness proofs for the RISC-V combines in `Combine.lean`.
-/

namespace Veir.Data.RISCV

/-! ## Conventions

Each lemma in this namespace that is named after a combine is the local correctness statement of
that combine's Puddle pattern, stated exactly as its CTree validity proof in
`Veir.Passes.RISCVCombines.Validity` sees it:

* register operations take their operands as `(rs2, rs1)`, the reverse of the SSA operand order,
  because that is how `Riscv.interpretOp'` applies them;
* an immediate the pattern constrains is read through `RISCVImmediateProperties.immField`, and the
  constraint is a hypothesis in the form the Puddle matcher states it;
* an immediate the pattern does not constrain is an arbitrary bit vector.

The validity proofs close their register goals with these lemmas (`proveCombineValid using`), so a
statement that drifts from its pattern no longer builds. -/

/-! ### Signed immediate guards

Combine guards compare `value.toInt` with integer literals. `bv_decide` does not see these `Int`
facts, so they are restated as signed bit-vector comparisons. -/

section toInt

variable {x : BitVec 64} {c : Int}

theorem le_toInt_iff_sle (h₁ : -2 ^ 63 ≤ c) (h₂ : c < 2 ^ 63) :
    c ≤ x.toInt ↔ (BitVec.ofInt 64 c).sle x := by
  rw [BitVec.sle_iff_toInt_le, BitVec.toInt_ofInt_eq_self (by decide) h₁ h₂]

theorem toInt_le_iff_sle (h₁ : -2 ^ 63 ≤ c) (h₂ : c < 2 ^ 63) :
    x.toInt ≤ c ↔ x.sle (BitVec.ofInt 64 c) := by
  rw [BitVec.sle_iff_toInt_le, BitVec.toInt_ofInt_eq_self (by decide) h₁ h₂]

theorem lt_toInt_iff_slt (h₁ : -2 ^ 63 ≤ c) (h₂ : c < 2 ^ 63) :
    c < x.toInt ↔ (BitVec.ofInt 64 c).slt x := by
  rw [BitVec.slt_iff_toInt_lt, BitVec.toInt_ofInt_eq_self (by decide) h₁ h₂]

theorem toInt_lt_iff_slt (h₁ : -2 ^ 63 ≤ c) (h₂ : c < 2 ^ 63) :
    x.toInt < c ↔ x.slt (BitVec.ofInt 64 c) := by
  rw [BitVec.slt_iff_toInt_lt, BitVec.toInt_ofInt_eq_self (by decide) h₁ h₂]

theorem toInt_eq_iff_eq_ofInt (h₁ : -2 ^ 63 ≤ c) (h₂ : c < 2 ^ 63) :
    x.toInt = c ↔ x = BitVec.ofInt 64 c := by
  rw [← BitVec.toInt_inj, BitVec.toInt_ofInt_eq_self (by decide) h₁ h₂]

end toInt

/-- Normalize the matcher guards on immediates into bit-vector facts, then bit-blast. -/
local macro "guarded_bv_decide" : tactic => `(tactic| (
  simp_all [_root_.Veir.RISCV.liFitsSImm12, RISCVImmediateProperties.immField,
    le_toInt_iff_sle, toInt_le_iff_sle, lt_toInt_iff_slt, toInt_lt_iff_slt, toInt_eq_iff_eq_ofInt]
  all_goals veir_bv_decide))

/-! ### Stored bytes

A store writes a little-endian prefix of its value register, which depends only on the low bits
of the register. -/

theorem toByteArrayLE_extract_four {a b : BitVec 64} (h : a.setWidth 32 = b.setWidth 32) :
    (UInt64.ofBitVec a).toByteArrayLE.extract 0 4 = (UInt64.ofBitVec b).toByteArrayLE.extract 0 4 := by
  apply ByteArray.ext
  simp [ByteArray.data_extract, UInt64.toByteArrayLE, ← UInt8.toBitVec_inj]
  bv_decide

theorem toByteArrayLE_extract_two {a b : BitVec 64} (h : a.setWidth 16 = b.setWidth 16) :
    (UInt64.ofBitVec a).toByteArrayLE.extract 0 2 = (UInt64.ofBitVec b).toByteArrayLE.extract 0 2 := by
  apply ByteArray.ext
  simp [ByteArray.data_extract, UInt64.toByteArrayLE, ← UInt8.toBitVec_inj]
  bv_decide

theorem toByteArrayLE_extract_one {a b : BitVec 64} (h : a.setWidth 8 = b.setWidth 8) :
    (UInt64.ofBitVec a).toByteArrayLE.extract 0 1 = (UInt64.ofBitVec b).toByteArrayLE.extract 0 1 := by
  apply ByteArray.ext
  simp [ByteArray.data_extract, UInt64.toByteArrayLE, ← UInt8.toBitVec_inj]
  bv_decide

/-! ## Identities, booleans and immediates -/

/-- `riscv.add x (riscv.li 0) -> x` (`right_identity_zero_add`). The matcher fixes the
    materialized constant to `0#64`. -/
theorem right_identity_zero_add {x : Reg} :
    RISCV.add (RISCV.li 0#64) x = x := by
  veir_bv_decide

/-- `riscv.add x (riscv.li c) -> riscv.addi x c` (`add_li_to_addi`): the signed bounds from
    `liFitsSImm12` ensure that truncating `c` to 12 bits and sign-extending recovers `c`. -/
theorem add_li_to_addi {x : Reg} {p : RISCVImmediateProperties}
    (h : _root_.Veir.RISCV.liFitsSImm12 p = true) :
    RISCV.add (RISCV.li p.value) x = RISCV.addi (p.immField 12) x := by
  guarded_bv_decide

/-- `riscv.add (riscv.li c) x -> riscv.addi x c` (`add_li_to_addi_commuted`). -/
theorem add_li_to_addi_commuted {x : Reg} {p : RISCVImmediateProperties}
    (h : _root_.Veir.RISCV.liFitsSImm12 p = true) :
    RISCV.add x (RISCV.li p.value) = RISCV.addi (p.immField 12) x := by
  guarded_bv_decide

/-- `riscv.li 0 -> rv64.get_register x0` (`li_zero_to_x0`): `x0` reads as the zero register
    value, which is what `li 0` materializes. -/
theorem li_zero_to_x0 : RISCV.li 0#64 = ⟨0#64⟩ := by
  simp [RISCV.li]

/-! Shift-amount combines. The amount is SSA operand 1, i.e. the first argument of the
    register operation. The mask hypotheses are the guard of `drop_shift_amount_mask_pattern`. -/

theorem sll_amount_andi {x amount : Reg} {p : RISCVImmediateProperties}
    (h : (p.value &&& 63#64 == 63#64) = true) :
    RISCV.sll (RISCV.andi (p.immField 12) amount) x = RISCV.sll amount x := by
  guarded_bv_decide

theorem srl_amount_andi {x amount : Reg} {p : RISCVImmediateProperties}
    (h : (p.value &&& 63#64 == 63#64) = true) :
    RISCV.srl (RISCV.andi (p.immField 12) amount) x = RISCV.srl amount x := by
  guarded_bv_decide

theorem sra_amount_andi {x amount : Reg} {p : RISCVImmediateProperties}
    (h : (p.value &&& 63#64 == 63#64) = true) :
    RISCV.sra (RISCV.andi (p.immField 12) amount) x = RISCV.sra amount x := by
  guarded_bv_decide

theorem sllw_amount_andi {x amount : Reg} {p : RISCVImmediateProperties}
    (h : (p.value &&& 31#64 == 31#64) = true) :
    RISCV.sllw (RISCV.andi (p.immField 12) amount) x = RISCV.sllw amount x := by
  guarded_bv_decide

theorem srlw_amount_andi {x amount : Reg} {p : RISCVImmediateProperties}
    (h : (p.value &&& 31#64 == 31#64) = true) :
    RISCV.srlw (RISCV.andi (p.immField 12) amount) x = RISCV.srlw amount x := by
  guarded_bv_decide

theorem sraw_amount_andi {x amount : Reg} {p : RISCVImmediateProperties}
    (h : (p.value &&& 31#64 == 31#64) = true) :
    RISCV.sraw (RISCV.andi (p.immField 12) amount) x = RISCV.sraw amount x := by
  guarded_bv_decide

theorem sll_amount_zextw {x amount : Reg} :
    RISCV.sll (RISCV.zextw amount) x = RISCV.sll amount x := by
  veir_bv_decide

theorem srl_amount_zextw {x amount : Reg} :
    RISCV.srl (RISCV.zextw amount) x = RISCV.srl amount x := by
  veir_bv_decide

theorem sra_amount_zextw {x amount : Reg} :
    RISCV.sra (RISCV.zextw amount) x = RISCV.sra amount x := by
  veir_bv_decide

theorem sllw_amount_zextw {x amount : Reg} :
    RISCV.sllw (RISCV.zextw amount) x = RISCV.sllw amount x := by
  veir_bv_decide

theorem srlw_amount_zextw {x amount : Reg} :
    RISCV.srlw (RISCV.zextw amount) x = RISCV.srlw amount x := by
  veir_bv_decide

theorem sraw_amount_zextw {x amount : Reg} :
    RISCV.sraw (RISCV.zextw amount) x = RISCV.sraw amount x := by
  veir_bv_decide

/--
  `riscv.srli 63 (riscv.srai _ x) -> riscv.srli 63 x` (`srl_sra_signbit`): an arithmetic right
  shift by any amount never changes the top bit, so a subsequent logical shift by 63 (which keeps
  only that bit) gives the same result as skipping the `srai` entirely. Mirrors LLVM's generic
  `DAGCombiner::visitSRL` rule `fold (srl (sra X, Y), 31) -> (srl X, 31)`.
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L11628-L11633
-/
theorem srl_sra_signbit {x : Reg} {shamt : BitVec 6} {p : RISCVImmediateProperties}
    (h : p.value.toInt = ((64 : Nat) : Int) - 1) :
    RISCV.srli (p.immField 6) (RISCV.srai shamt x) = RISCV.srli (p.immField 6) x := by
  guarded_bv_decide

/-- The `i32` analogue of `srl_sra_signbit`, at bit 31 (`srlw_sraw_signbit`). -/
theorem srlw_sraw_signbit {x : Reg} {shamt : BitVec 5} {p : RISCVImmediateProperties}
    (h : p.value.toInt = ((32 : Nat) : Int) - 1) :
    RISCV.srliw (p.immField 5) (RISCV.sraiw shamt x) = RISCV.srliw (p.immField 5) x := by
  guarded_bv_decide

/-!
  The `drop_slli_srli_boolGen` family: for a comparison op producing exactly 0 or 1,
  `riscv.slli 63` isolates its bit 0 into bit 63 and `riscv.srli 63` moves it straight back, so
  the round trip is the identity and both shifts can be dropped entirely.
-/

theorem drop_slli_srli_slt {rs1 rs2 : Reg} {p q : RISCVImmediateProperties}
    (hp : p.value = 63#64) (hq : q.value = 63#64) :
    RISCV.srli (p.immField 6) (RISCV.slli (q.immField 6) (RISCV.slt rs2 rs1)) =
      RISCV.slt rs2 rs1 := by
  guarded_bv_decide

theorem drop_slli_srli_sltu {rs1 rs2 : Reg} {p q : RISCVImmediateProperties}
    (hp : p.value = 63#64) (hq : q.value = 63#64) :
    RISCV.srli (p.immField 6) (RISCV.slli (q.immField 6) (RISCV.sltu rs2 rs1)) =
      RISCV.sltu rs2 rs1 := by
  guarded_bv_decide

theorem drop_slli_srli_slti {rs1 : Reg} {imm : BitVec 12} {p q : RISCVImmediateProperties}
    (hp : p.value = 63#64) (hq : q.value = 63#64) :
    RISCV.srli (p.immField 6) (RISCV.slli (q.immField 6) (RISCV.slti imm rs1)) =
      RISCV.slti imm rs1 := by
  guarded_bv_decide

theorem drop_slli_srli_sltiu {rs1 : Reg} {imm : BitVec 12} {p q : RISCVImmediateProperties}
    (hp : p.value = 63#64) (hq : q.value = 63#64) :
    RISCV.srli (p.immField 6) (RISCV.slli (q.immField 6) (RISCV.sltiu imm rs1)) =
      RISCV.sltiu imm rs1 := by
  guarded_bv_decide

theorem drop_slli_srli_seqz {rs1 : Reg} {p q : RISCVImmediateProperties}
    (hp : p.value = 63#64) (hq : q.value = 63#64) :
    RISCV.srli (p.immField 6) (RISCV.slli (q.immField 6) (RISCV.seqz rs1)) =
      RISCV.seqz rs1 := by
  guarded_bv_decide

theorem drop_slli_srli_snez {rs1 : Reg} {p q : RISCVImmediateProperties}
    (hp : p.value = 63#64) (hq : q.value = 63#64) :
    RISCV.srli (p.immField 6) (RISCV.slli (q.immField 6) (RISCV.snez rs1)) =
      RISCV.snez rs1 := by
  guarded_bv_decide

theorem drop_slli_srli_sltz {rs1 : Reg} {p q : RISCVImmediateProperties}
    (hp : p.value = 63#64) (hq : q.value = 63#64) :
    RISCV.srli (p.immField 6) (RISCV.slli (q.immField 6) (RISCV.sltz rs1)) =
      RISCV.sltz rs1 := by
  guarded_bv_decide

theorem drop_slli_srli_sgtz {rs1 : Reg} {p q : RISCVImmediateProperties}
    (hp : p.value = 63#64) (hq : q.value = 63#64) :
    RISCV.srli (p.immField 6) (RISCV.slli (q.immField 6) (RISCV.sgtz rs1)) =
      RISCV.sgtz rs1 := by
  guarded_bv_decide

/-- `riscv.andi 1 (riscv.srli 63 x) -> riscv.srli 63 x` (`drop_andi_one_srli`): `srli 63` leaves
    only bit 0, so masking it with 1 changes nothing. -/
theorem drop_andi_one_srli {x : Reg} {p q : RISCVImmediateProperties}
    (hp : p.value = 1#64) (hq : q.value = 63#64) :
    RISCV.andi (p.immField 12) (RISCV.srli (q.immField 6) x) = RISCV.srli (q.immField 6) x := by
  guarded_bv_decide

/-! ## Redundant extensions -/

/-- Each extension is idempotent (`drop_redundant_ext`): the inner extension already establishes
    the high-bit pattern the outer one would. -/
theorem zextw_zextw {x : Reg} : RISCV.zextw (RISCV.zextw x) = RISCV.zextw x := by
  veir_bv_decide

theorem sextw_sextw {x : Reg} : RISCV.sextw (RISCV.sextw x) = RISCV.sextw x := by
  veir_bv_decide

theorem zextb_zextb {x : Reg} : RISCV.zextb (RISCV.zextb x) = RISCV.zextb x := by
  veir_bv_decide

theorem zexth_zexth {x : Reg} : RISCV.zexth (RISCV.zexth x) = RISCV.zexth x := by
  veir_bv_decide

theorem sextb_sextb {x : Reg} : RISCV.sextb (RISCV.sextb x) = RISCV.sextb x := by
  veir_bv_decide

theorem sexth_sexth {x : Reg} : RISCV.sexth (RISCV.sexth x) = RISCV.sexth x := by
  veir_bv_decide

/-- A byte zero-extension is already a word zero-extension (`zextw_zextb`). -/
theorem zextw_zextb {x : Reg} :
    RISCV.zextw (RISCV.zextb x) = RISCV.zextb x := by
  veir_bv_decide

/-! ## Extensions of materialized constants

`riscv.<ext> (riscv.li c) -> riscv.li c` when the matcher's range guard on `c` holds: for a
zero-extension the unsigned range below `2^width`, for a sign-extension the signed range
`[-2^(width-1), 2^(width-1))`. -/

theorem zextw_li_low32 {c : BitVec 64} (h : (!decide (c ≥ 4294967296#64)) = true) :
    RISCV.zextw (RISCV.li c) = RISCV.li c := by
  guarded_bv_decide

theorem sextw_li_low32 {c : BitVec 64}
    (h : (!decide (c.toInt < -2147483648 ∨ c.toInt ≥ 2147483648)) = true) :
    RISCV.sextw (RISCV.li c) = RISCV.li c := by
  guarded_bv_decide

theorem zextb_li_low8 {c : BitVec 64} (h : (!decide (c.toInt < 0 ∨ c.toInt ≥ 256)) = true) :
    RISCV.zextb (RISCV.li c) = RISCV.li c := by
  guarded_bv_decide

theorem zexth_li_low16 {c : BitVec 64} (h : (!decide (c.toInt < 0 ∨ c.toInt ≥ 65536)) = true) :
    RISCV.zexth (RISCV.li c) = RISCV.li c := by
  guarded_bv_decide

theorem sextb_li_low8 {c : BitVec 64} (h : (!decide (c.toInt < -128 ∨ c.toInt ≥ 128)) = true) :
    RISCV.sextb (RISCV.li c) = RISCV.li c := by
  guarded_bv_decide

theorem sexth_li_low16 {c : BitVec 64} (h : (!decide (c.toInt < -32768 ∨ c.toInt ≥ 32768)) = true) :
    RISCV.sexth (RISCV.li c) = RISCV.li c := by
  guarded_bv_decide

/-! ## Byte-load and byte-packing combines.

    The register-level model below represents the byte fetched from memory by
    an arbitrary `Reg`: `lbu` produces its `zextb` form. These combines reuse
    existing load results without moving or recreating memory accesses; the
    equalities here establish the value transformations. -/

/-- `zextb (lbu byte) = lbu byte`: an unsigned byte load is already
    zero-extended. -/
theorem zextb_lbu {byte : Reg} :
    RISCV.zextb (RISCV.zextb byte) = RISCV.zextb byte := by
  veir_bv_decide

/-- `andi 255 (lbu byte) = lbu byte`: an unsigned byte load is already masked.
    The combine reuses the existing load result. -/
theorem andi_255_lbu {byte : Reg} :
    RISCV.andi 255 (RISCV.zextb byte) = RISCV.zextb byte := by
  veir_bv_decide

/-- The byte-packing pre-canonicalization is valid for each selected shift:
    a word shift of a zero-extended byte, followed by `zextw`, is the same as
    the corresponding full-width shift. -/
theorem zextw_slliw_lbu_8 {byte : Reg} :
    RISCV.zextw (RISCV.slliw 8 (RISCV.zextb byte)) = RISCV.slli 8 (RISCV.zextb byte) := by
  veir_bv_decide

theorem zextw_slliw_lbu_16 {byte : Reg} :
    RISCV.zextw (RISCV.slliw 16 (RISCV.zextb byte)) = RISCV.slli 16 (RISCV.zextb byte) := by
  veir_bv_decide

theorem zextw_slliw_lbu_24 {byte : Reg} :
    RISCV.zextw (RISCV.slliw 24 (RISCV.zextb byte)) = RISCV.slli 24 (RISCV.zextb byte) := by
  veir_bv_decide

/-- `or (lbu lo) (slli (lbu hi), 8) -> packh lo hi`.

    `RISCV.or` takes its operands as `(rs2, rs1)`, so the register-level
    expression lists the shifted `hi` before `lo`. -/
theorem packh_low_bytes {lo hi : Reg} :
    RISCV.or (RISCV.slli 8 (RISCV.zextb hi)) (RISCV.zextb lo) =
      RISCV.packh (RISCV.zextb hi) (RISCV.zextb lo) := by
  veir_bv_decide

/-- `or (slli (lbu hi), 8) (lbu lo) -> packh lo hi`. -/
theorem packh_low_bytes_commuted {lo hi : Reg} :
    RISCV.or (RISCV.zextb lo) (RISCV.slli 8 (RISCV.zextb hi)) =
      RISCV.packh (RISCV.zextb hi) (RISCV.zextb lo) := by
  veir_bv_decide

/-- `or (slli (lbu b2), 16) (slli (lbu b3), 24) ->
    slli (packh b2 b3), 16`.

    `RISCV.or` takes its operands as `(rs2, rs1)`, so the register-level
    expression lists the `b3` shift before the `b2` shift. -/
theorem packh_high_bytes {b2 b3 : Reg} :
    RISCV.or (RISCV.slli 24 (RISCV.zextb b3)) (RISCV.slli 16 (RISCV.zextb b2)) =
      RISCV.slli 16 (RISCV.packh (RISCV.zextb b3) (RISCV.zextb b2)) := by
  veir_bv_decide

/-- `or (slli (lbu b3), 24) (slli (lbu b2), 16) ->
    slli (packh b2 b3), 16`. -/
theorem packh_high_bytes_commuted {b2 b3 : Reg} :
    RISCV.or (RISCV.slli 16 (RISCV.zextb b2)) (RISCV.slli 24 (RISCV.zextb b3)) =
      RISCV.slli 16 (RISCV.packh (RISCV.zextb b3) (RISCV.zextb b2)) := by
  veir_bv_decide

/-! ## Extensions of bitwise operations

`riscv.<ext> (riscv.<op> a b) -> riscv.<op> a b` when the guarded operands already carry the
extension's high-bit pattern. `and` under a zero-extension needs only one guarded operand (SSA
`lhs` or `rhs`); every other combination needs both. In SSA order the operands are
`riscv.<op> a, b`, so the register operation is applied as `RISCV.<op> b a`. -/

theorem zextw_and_lhs {a b : Reg} :
    RISCV.zextw (RISCV.and b (RISCV.zextw a)) = RISCV.and b (RISCV.zextw a) := by
  veir_bv_decide

theorem zextw_and_rhs {a b : Reg} :
    RISCV.zextw (RISCV.and (RISCV.zextw b) a) = RISCV.and (RISCV.zextw b) a := by
  veir_bv_decide

theorem zextw_or {a b : Reg} :
    RISCV.zextw (RISCV.or (RISCV.zextw b) (RISCV.zextw a)) =
      RISCV.or (RISCV.zextw b) (RISCV.zextw a) := by
  veir_bv_decide

theorem zextw_xor {a b : Reg} :
    RISCV.zextw (RISCV.xor (RISCV.zextw b) (RISCV.zextw a)) =
      RISCV.xor (RISCV.zextw b) (RISCV.zextw a) := by
  veir_bv_decide

theorem zextb_and_lhs {a b : Reg} :
    RISCV.zextb (RISCV.and b (RISCV.zextb a)) = RISCV.and b (RISCV.zextb a) := by
  veir_bv_decide

theorem zextb_and_rhs {a b : Reg} :
    RISCV.zextb (RISCV.and (RISCV.zextb b) a) = RISCV.and (RISCV.zextb b) a := by
  veir_bv_decide

theorem zextb_or {a b : Reg} :
    RISCV.zextb (RISCV.or (RISCV.zextb b) (RISCV.zextb a)) =
      RISCV.or (RISCV.zextb b) (RISCV.zextb a) := by
  veir_bv_decide

theorem zextb_xor {a b : Reg} :
    RISCV.zextb (RISCV.xor (RISCV.zextb b) (RISCV.zextb a)) =
      RISCV.xor (RISCV.zextb b) (RISCV.zextb a) := by
  veir_bv_decide

theorem zexth_and_lhs {a b : Reg} :
    RISCV.zexth (RISCV.and b (RISCV.zexth a)) = RISCV.and b (RISCV.zexth a) := by
  veir_bv_decide

theorem zexth_and_rhs {a b : Reg} :
    RISCV.zexth (RISCV.and (RISCV.zexth b) a) = RISCV.and (RISCV.zexth b) a := by
  veir_bv_decide

theorem zexth_or {a b : Reg} :
    RISCV.zexth (RISCV.or (RISCV.zexth b) (RISCV.zexth a)) =
      RISCV.or (RISCV.zexth b) (RISCV.zexth a) := by
  veir_bv_decide

theorem zexth_xor {a b : Reg} :
    RISCV.zexth (RISCV.xor (RISCV.zexth b) (RISCV.zexth a)) =
      RISCV.xor (RISCV.zexth b) (RISCV.zexth a) := by
  veir_bv_decide

theorem sextw_and {a b : Reg} :
    RISCV.sextw (RISCV.and (RISCV.sextw b) (RISCV.sextw a)) =
      RISCV.and (RISCV.sextw b) (RISCV.sextw a) := by
  veir_bv_decide

theorem sextw_or {a b : Reg} :
    RISCV.sextw (RISCV.or (RISCV.sextw b) (RISCV.sextw a)) =
      RISCV.or (RISCV.sextw b) (RISCV.sextw a) := by
  veir_bv_decide

theorem sextw_xor {a b : Reg} :
    RISCV.sextw (RISCV.xor (RISCV.sextw b) (RISCV.sextw a)) =
      RISCV.xor (RISCV.sextw b) (RISCV.sextw a) := by
  veir_bv_decide

theorem sextb_and {a b : Reg} :
    RISCV.sextb (RISCV.and (RISCV.sextb b) (RISCV.sextb a)) =
      RISCV.and (RISCV.sextb b) (RISCV.sextb a) := by
  veir_bv_decide

theorem sextb_or {a b : Reg} :
    RISCV.sextb (RISCV.or (RISCV.sextb b) (RISCV.sextb a)) =
      RISCV.or (RISCV.sextb b) (RISCV.sextb a) := by
  veir_bv_decide

theorem sextb_xor {a b : Reg} :
    RISCV.sextb (RISCV.xor (RISCV.sextb b) (RISCV.sextb a)) =
      RISCV.xor (RISCV.sextb b) (RISCV.sextb a) := by
  veir_bv_decide

theorem sexth_and {a b : Reg} :
    RISCV.sexth (RISCV.and (RISCV.sexth b) (RISCV.sexth a)) =
      RISCV.and (RISCV.sexth b) (RISCV.sexth a) := by
  veir_bv_decide

theorem sexth_or {a b : Reg} :
    RISCV.sexth (RISCV.or (RISCV.sexth b) (RISCV.sexth a)) =
      RISCV.or (RISCV.sexth b) (RISCV.sexth a) := by
  veir_bv_decide

theorem sexth_xor {a b : Reg} :
    RISCV.sexth (RISCV.xor (RISCV.sexth b) (RISCV.sexth a)) =
      RISCV.xor (RISCV.sexth b) (RISCV.sexth a) := by
  veir_bv_decide

/-! ## Extensions of a stored value

A word store (`sw`) writes the first four little-endian bytes of its value register, a halfword
store (`sh`) two and a byte store (`sb`) one (see the store cases of `Riscv.interpretOp'`). Each
extension below leaves those bytes unchanged. -/

theorem drop_zextw_sw {rs1 : Reg} :
    (UInt64.ofBitVec (RISCV.zextw rs1).val).toByteArrayLE.extract 0 4 =
      (UInt64.ofBitVec rs1.val).toByteArrayLE.extract 0 4 :=
  toByteArrayLE_extract_four (by veir_bv_decide)

theorem drop_sextw_sw {rs1 : Reg} :
    (UInt64.ofBitVec (RISCV.sextw rs1).val).toByteArrayLE.extract 0 4 =
      (UInt64.ofBitVec rs1.val).toByteArrayLE.extract 0 4 :=
  toByteArrayLE_extract_four (by veir_bv_decide)

theorem drop_zexth_sh {rs1 : Reg} :
    (UInt64.ofBitVec (RISCV.zexth rs1).val).toByteArrayLE.extract 0 2 =
      (UInt64.ofBitVec rs1.val).toByteArrayLE.extract 0 2 :=
  toByteArrayLE_extract_two (by veir_bv_decide)

theorem drop_sexth_sh {rs1 : Reg} :
    (UInt64.ofBitVec (RISCV.sexth rs1).val).toByteArrayLE.extract 0 2 =
      (UInt64.ofBitVec rs1.val).toByteArrayLE.extract 0 2 :=
  toByteArrayLE_extract_two (by veir_bv_decide)

theorem drop_zextb_sb {rs1 : Reg} :
    (UInt64.ofBitVec (RISCV.zextb rs1).val).toByteArrayLE.extract 0 1 =
      (UInt64.ofBitVec rs1.val).toByteArrayLE.extract 0 1 :=
  toByteArrayLE_extract_one (by veir_bv_decide)

theorem drop_sextb_sb {rs1 : Reg} :
    (UInt64.ofBitVec (RISCV.sextb rs1).val).toByteArrayLE.extract 0 1 =
      (UInt64.ofBitVec rs1.val).toByteArrayLE.extract 0 1 :=
  toByteArrayLE_extract_one (by veir_bv_decide)

theorem drop_zextw_sb {rs1 : Reg} :
    (UInt64.ofBitVec (RISCV.zextw rs1).val).toByteArrayLE.extract 0 1 =
      (UInt64.ofBitVec rs1.val).toByteArrayLE.extract 0 1 :=
  toByteArrayLE_extract_one (by veir_bv_decide)

theorem drop_sextw_sb {rs1 : Reg} :
    (UInt64.ofBitVec (RISCV.sextw rs1).val).toByteArrayLE.extract 0 1 =
      (UInt64.ofBitVec rs1.val).toByteArrayLE.extract 0 1 :=
  toByteArrayLE_extract_one (by veir_bv_decide)

/-! ## Extensions of `x0` (not CTree-certified, see `Veir.Passes.RISCVCombines.Validity`) -/

/--
  Prove the correctness of the `zextw_x0` combine: zero-extending the value 0
  (which is what the hard-wired zero register `x0` reads as -- an interpreter
  fact, not a `Reg`-algebra one, so it isn't itself part of this theorem) is a
  no-op.
-/
theorem zextw_x0 :
    RISCV.zextw (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.li (BitVec.ofInt 64 0) := by
  veir_bv_decide

/-- Sext mirror of `zextw_x0`: sign-extending the value 0 (what `x0` reads as) is
    a no-op. -/
theorem sextw_x0 :
    RISCV.sextw (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.li (BitVec.ofInt 64 0) := by
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

/-! ## `sextw` of a sign-extending producer

`riscv.sextw (op …) -> op …` (`sextw_signExtendingOpW`) when `op` already returns a sign-extended
32-bit value. -/

theorem sextw_addw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.addw rs2 rs1) = RISCV.addw rs2 rs1 := by
  veir_bv_decide

theorem sextw_addiw {rs1 : Reg} {imm : BitVec 12} :
    RISCV.sextw (RISCV.addiw imm rs1) = RISCV.addiw imm rs1 := by
  veir_bv_decide

theorem sextw_subw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.subw rs2 rs1) = RISCV.subw rs2 rs1 := by
  veir_bv_decide

theorem sextw_mulw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.mulw rs2 rs1) = RISCV.mulw rs2 rs1 := by
  veir_bv_decide

theorem sextw_divw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.divw rs2 rs1) = RISCV.divw rs2 rs1 := by
  veir_bv_decide

theorem sextw_divuw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.divuw rs2 rs1) = RISCV.divuw rs2 rs1 := by
  veir_bv_decide

theorem sextw_remw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.remw rs2 rs1) = RISCV.remw rs2 rs1 := by
  veir_bv_decide

theorem sextw_remuw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.remuw rs2 rs1) = RISCV.remuw rs2 rs1 := by
  veir_bv_decide

theorem sextw_sllw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.sllw rs2 rs1) = RISCV.sllw rs2 rs1 := by
  veir_bv_decide

theorem sextw_slliw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.sextw (RISCV.slliw imm rs1) = RISCV.slliw imm rs1 := by
  veir_bv_decide

theorem sextw_srlw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.srlw rs2 rs1) = RISCV.srlw rs2 rs1 := by
  veir_bv_decide

theorem sextw_srliw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.sextw (RISCV.srliw imm rs1) = RISCV.srliw imm rs1 := by
  veir_bv_decide

theorem sextw_sraw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.sraw rs2 rs1) = RISCV.sraw rs2 rs1 := by
  veir_bv_decide

theorem sextw_sraiw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.sextw (RISCV.sraiw imm rs1) = RISCV.sraiw imm rs1 := by
  veir_bv_decide

theorem sextw_rolw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.rolw rs2 rs1) = RISCV.rolw rs2 rs1 := by
  veir_bv_decide

theorem sextw_rorw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.rorw rs2 rs1) = RISCV.rorw rs2 rs1 := by
  veir_bv_decide

theorem sextw_roriw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.sextw (RISCV.roriw imm rs1) = RISCV.roriw imm rs1 := by
  veir_bv_decide

theorem sextw_packw {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.packw rs2 rs1) = RISCV.packw rs2 rs1 := by
  veir_bv_decide

theorem sextw_lui {imm : BitVec 20} :
    RISCV.sextw (RISCV.lui imm) = RISCV.lui imm := by
  veir_bv_decide

theorem sextw_cpop {rs1 : Reg} :
    RISCV.sextw (RISCV.cpop rs1) = RISCV.cpop rs1 := by
  veir_bv_decide

theorem sextw_cpopw {rs1 : Reg} :
    RISCV.sextw (RISCV.cpopw rs1) = RISCV.cpopw rs1 := by
  veir_bv_decide

theorem sextw_clz {rs1 : Reg} :
    RISCV.sextw (RISCV.clz rs1) = RISCV.clz rs1 := by
  veir_bv_decide

theorem sextw_clzw {rs1 : Reg} :
    RISCV.sextw (RISCV.clzw rs1) = RISCV.clzw rs1 := by
  veir_bv_decide

theorem sextw_ctz {rs1 : Reg} :
    RISCV.sextw (RISCV.ctz rs1) = RISCV.ctz rs1 := by
  veir_bv_decide

theorem sextw_ctzw {rs1 : Reg} :
    RISCV.sextw (RISCV.ctzw rs1) = RISCV.ctzw rs1 := by
  veir_bv_decide

theorem sextw_slt {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.slt rs2 rs1) = RISCV.slt rs2 rs1 := by
  veir_bv_decide

theorem sextw_sltu {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.sltu rs2 rs1) = RISCV.sltu rs2 rs1 := by
  veir_bv_decide

theorem sextw_slti {rs1 : Reg} {imm : BitVec 12} :
    RISCV.sextw (RISCV.slti imm rs1) = RISCV.slti imm rs1 := by
  veir_bv_decide

theorem sextw_sltiu {rs1 : Reg} {imm : BitVec 12} :
    RISCV.sextw (RISCV.sltiu imm rs1) = RISCV.sltiu imm rs1 := by
  veir_bv_decide

theorem sextw_bext {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.bext rs2 rs1) = RISCV.bext rs2 rs1 := by
  veir_bv_decide

theorem sextw_bexti {rs1 : Reg} {imm : BitVec 6} :
    RISCV.sextw (RISCV.bexti imm rs1) = RISCV.bexti imm rs1 := by
  veir_bv_decide

theorem sextw_sextb {rs1 : Reg} :
    RISCV.sextw (RISCV.sextb rs1) = RISCV.sextb rs1 := by
  veir_bv_decide

theorem sextw_sexth {rs1 : Reg} :
    RISCV.sextw (RISCV.sexth rs1) = RISCV.sexth rs1 := by
  veir_bv_decide

theorem sextw_zexth {rs1 : Reg} :
    RISCV.sextw (RISCV.zexth rs1) = RISCV.zexth rs1 := by
  veir_bv_decide

theorem sextw_packh {rs1 rs2 : Reg} :
    RISCV.sextw (RISCV.packh rs2 rs1) = RISCV.packh rs2 rs1 := by
  veir_bv_decide

theorem sextw_srai {rs1 : Reg} {imm : BitVec 6} (h : 32#6 ≤ imm) :
    RISCV.sextw (RISCV.srai imm rs1) = RISCV.srai imm rs1 := by
  veir_bv_decide

theorem sextw_srli {rs1 : Reg} {imm : BitVec 6} (h : 32#6 < imm) :
    RISCV.sextw (RISCV.srli imm rs1) = RISCV.srli imm rs1 := by
  veir_bv_decide

theorem sextw_andi {rs1 : Reg} {imm : BitVec 12} (h : (!imm.msb) = true) :
    RISCV.sextw (RISCV.andi imm rs1) = RISCV.andi imm rs1 := by
  veir_bv_decide

theorem sextw_ori {rs1 : Reg} {imm : BitVec 12} (h : imm.msb = true) :
    RISCV.sextw (RISCV.ori imm rs1) = RISCV.ori imm rs1 := by
  veir_bv_decide

/-! ## Extensions of an operand the consumer ignores

`riscv.<dst> (riscv.<ext> x) … -> riscv.<dst> x …` (`drop_ext_low_word`): the consumer reads only
operand bits 31:0, which `zextw` and `sextw` leave unchanged. `_rs1` and `_rs2` name the extended
SSA operand of a binary consumer. The amount (`rs2`) cases of `sllw`/`srlw`/`sraw` under `zextw`
are `sllw_amount_zextw`, `srlw_amount_zextw` and `sraw_amount_zextw`. -/

theorem drop_zextw_addw_rs1 {rs1 rs2 : Reg} :
    RISCV.addw rs2 (RISCV.zextw rs1) = RISCV.addw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_addw_rs2 {rs1 rs2 : Reg} :
    RISCV.addw (RISCV.zextw rs2) rs1 = RISCV.addw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_addiw {rs1 : Reg} {imm : BitVec 12} :
    RISCV.addiw imm (RISCV.zextw rs1) = RISCV.addiw imm rs1 := by
  veir_bv_decide

theorem drop_zextw_roriw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.roriw imm (RISCV.zextw rs1) = RISCV.roriw imm rs1 := by
  veir_bv_decide

theorem drop_zextw_srliw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.srliw imm (RISCV.zextw rs1) = RISCV.srliw imm rs1 := by
  veir_bv_decide

theorem drop_zextw_subw_rs1 {rs1 rs2 : Reg} :
    RISCV.subw rs2 (RISCV.zextw rs1) = RISCV.subw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_subw_rs2 {rs1 rs2 : Reg} :
    RISCV.subw (RISCV.zextw rs2) rs1 = RISCV.subw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_mulw_rs1 {rs1 rs2 : Reg} :
    RISCV.mulw rs2 (RISCV.zextw rs1) = RISCV.mulw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_mulw_rs2 {rs1 rs2 : Reg} :
    RISCV.mulw (RISCV.zextw rs2) rs1 = RISCV.mulw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_divw_rs1 {rs1 rs2 : Reg} :
    RISCV.divw rs2 (RISCV.zextw rs1) = RISCV.divw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_divw_rs2 {rs1 rs2 : Reg} :
    RISCV.divw (RISCV.zextw rs2) rs1 = RISCV.divw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_divuw_rs1 {rs1 rs2 : Reg} :
    RISCV.divuw rs2 (RISCV.zextw rs1) = RISCV.divuw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_divuw_rs2 {rs1 rs2 : Reg} :
    RISCV.divuw (RISCV.zextw rs2) rs1 = RISCV.divuw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_remw_rs1 {rs1 rs2 : Reg} :
    RISCV.remw rs2 (RISCV.zextw rs1) = RISCV.remw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_remw_rs2 {rs1 rs2 : Reg} :
    RISCV.remw (RISCV.zextw rs2) rs1 = RISCV.remw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_remuw_rs1 {rs1 rs2 : Reg} :
    RISCV.remuw rs2 (RISCV.zextw rs1) = RISCV.remuw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_remuw_rs2 {rs1 rs2 : Reg} :
    RISCV.remuw (RISCV.zextw rs2) rs1 = RISCV.remuw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_sllw_rs1 {rs1 rs2 : Reg} :
    RISCV.sllw rs2 (RISCV.zextw rs1) = RISCV.sllw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_srlw_rs1 {rs1 rs2 : Reg} :
    RISCV.srlw rs2 (RISCV.zextw rs1) = RISCV.srlw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_sraw_rs1 {rs1 rs2 : Reg} :
    RISCV.sraw rs2 (RISCV.zextw rs1) = RISCV.sraw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_rolw_rs1 {rs1 rs2 : Reg} :
    RISCV.rolw rs2 (RISCV.zextw rs1) = RISCV.rolw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_rolw_rs2 {rs1 rs2 : Reg} :
    RISCV.rolw (RISCV.zextw rs2) rs1 = RISCV.rolw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_rorw_rs1 {rs1 rs2 : Reg} :
    RISCV.rorw rs2 (RISCV.zextw rs1) = RISCV.rorw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_rorw_rs2 {rs1 rs2 : Reg} :
    RISCV.rorw (RISCV.zextw rs2) rs1 = RISCV.rorw rs2 rs1 := by
  veir_bv_decide

theorem drop_zextw_sraiw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.sraiw imm (RISCV.zextw rs1) = RISCV.sraiw imm rs1 := by
  veir_bv_decide

theorem drop_zextw_slliuw {rs1 : Reg} {imm : BitVec 6} :
    RISCV.slliuw imm (RISCV.zextw rs1) = RISCV.slliuw imm rs1 := by
  veir_bv_decide

theorem drop_zextw_clzw {rs1 : Reg} :
    RISCV.clzw (RISCV.zextw rs1) = RISCV.clzw rs1 := by
  veir_bv_decide

theorem drop_zextw_ctzw {rs1 : Reg} :
    RISCV.ctzw (RISCV.zextw rs1) = RISCV.ctzw rs1 := by
  veir_bv_decide

theorem drop_zextw_cpopw {rs1 : Reg} :
    RISCV.cpopw (RISCV.zextw rs1) = RISCV.cpopw rs1 := by
  veir_bv_decide

theorem drop_zextw_sextw {rs1 : Reg} :
    RISCV.sextw (RISCV.zextw rs1) = RISCV.sextw rs1 := by
  veir_bv_decide

theorem drop_sextw_addw_rs1 {rs1 rs2 : Reg} :
    RISCV.addw rs2 (RISCV.sextw rs1) = RISCV.addw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_addw_rs2 {rs1 rs2 : Reg} :
    RISCV.addw (RISCV.sextw rs2) rs1 = RISCV.addw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_addiw {rs1 : Reg} {imm : BitVec 12} :
    RISCV.addiw imm (RISCV.sextw rs1) = RISCV.addiw imm rs1 := by
  veir_bv_decide

theorem drop_sextw_roriw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.roriw imm (RISCV.sextw rs1) = RISCV.roriw imm rs1 := by
  veir_bv_decide

theorem drop_sextw_srliw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.srliw imm (RISCV.sextw rs1) = RISCV.srliw imm rs1 := by
  veir_bv_decide

theorem drop_sextw_subw_rs1 {rs1 rs2 : Reg} :
    RISCV.subw rs2 (RISCV.sextw rs1) = RISCV.subw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_subw_rs2 {rs1 rs2 : Reg} :
    RISCV.subw (RISCV.sextw rs2) rs1 = RISCV.subw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_mulw_rs1 {rs1 rs2 : Reg} :
    RISCV.mulw rs2 (RISCV.sextw rs1) = RISCV.mulw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_mulw_rs2 {rs1 rs2 : Reg} :
    RISCV.mulw (RISCV.sextw rs2) rs1 = RISCV.mulw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_divw_rs1 {rs1 rs2 : Reg} :
    RISCV.divw rs2 (RISCV.sextw rs1) = RISCV.divw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_divw_rs2 {rs1 rs2 : Reg} :
    RISCV.divw (RISCV.sextw rs2) rs1 = RISCV.divw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_divuw_rs1 {rs1 rs2 : Reg} :
    RISCV.divuw rs2 (RISCV.sextw rs1) = RISCV.divuw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_divuw_rs2 {rs1 rs2 : Reg} :
    RISCV.divuw (RISCV.sextw rs2) rs1 = RISCV.divuw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_remw_rs1 {rs1 rs2 : Reg} :
    RISCV.remw rs2 (RISCV.sextw rs1) = RISCV.remw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_remw_rs2 {rs1 rs2 : Reg} :
    RISCV.remw (RISCV.sextw rs2) rs1 = RISCV.remw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_remuw_rs1 {rs1 rs2 : Reg} :
    RISCV.remuw rs2 (RISCV.sextw rs1) = RISCV.remuw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_remuw_rs2 {rs1 rs2 : Reg} :
    RISCV.remuw (RISCV.sextw rs2) rs1 = RISCV.remuw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_sllw_rs1 {rs1 rs2 : Reg} :
    RISCV.sllw rs2 (RISCV.sextw rs1) = RISCV.sllw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_sllw_rs2 {rs1 rs2 : Reg} :
    RISCV.sllw (RISCV.sextw rs2) rs1 = RISCV.sllw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_srlw_rs1 {rs1 rs2 : Reg} :
    RISCV.srlw rs2 (RISCV.sextw rs1) = RISCV.srlw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_srlw_rs2 {rs1 rs2 : Reg} :
    RISCV.srlw (RISCV.sextw rs2) rs1 = RISCV.srlw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_sraw_rs1 {rs1 rs2 : Reg} :
    RISCV.sraw rs2 (RISCV.sextw rs1) = RISCV.sraw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_sraw_rs2 {rs1 rs2 : Reg} :
    RISCV.sraw (RISCV.sextw rs2) rs1 = RISCV.sraw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_rolw_rs1 {rs1 rs2 : Reg} :
    RISCV.rolw rs2 (RISCV.sextw rs1) = RISCV.rolw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_rolw_rs2 {rs1 rs2 : Reg} :
    RISCV.rolw (RISCV.sextw rs2) rs1 = RISCV.rolw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_rorw_rs1 {rs1 rs2 : Reg} :
    RISCV.rorw rs2 (RISCV.sextw rs1) = RISCV.rorw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_rorw_rs2 {rs1 rs2 : Reg} :
    RISCV.rorw (RISCV.sextw rs2) rs1 = RISCV.rorw rs2 rs1 := by
  veir_bv_decide

theorem drop_sextw_sraiw {rs1 : Reg} {imm : BitVec 5} :
    RISCV.sraiw imm (RISCV.sextw rs1) = RISCV.sraiw imm rs1 := by
  veir_bv_decide

theorem drop_sextw_slliuw {rs1 : Reg} {imm : BitVec 6} :
    RISCV.slliuw imm (RISCV.sextw rs1) = RISCV.slliuw imm rs1 := by
  veir_bv_decide

theorem drop_sextw_clzw {rs1 : Reg} :
    RISCV.clzw (RISCV.sextw rs1) = RISCV.clzw rs1 := by
  veir_bv_decide

theorem drop_sextw_ctzw {rs1 : Reg} :
    RISCV.ctzw (RISCV.sextw rs1) = RISCV.ctzw rs1 := by
  veir_bv_decide

theorem drop_sextw_cpopw {rs1 : Reg} :
    RISCV.cpopw (RISCV.sextw rs1) = RISCV.cpopw rs1 := by
  veir_bv_decide

theorem drop_sextw_zextw {rs1 : Reg} :
    RISCV.zextw (RISCV.sextw rs1) = RISCV.zextw rs1 := by
  veir_bv_decide

end Veir.Data.RISCV

end
