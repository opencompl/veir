module

public import  Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Basic
meta import Veir.Meta.Tactic.BVDecide
import Std.Tactic.BVDecide

public section

namespace Veir.Data.RISCV

@[simp]
theorem forall_val_eq {P : Reg → Prop} :
    (∀ (r : Reg), r.val = v → P r) ↔ P ⟨v⟩ := by
  grind [cases Reg]

theorem Reg.val.inj : {x y : Reg} → x.val = y.val → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

@[veir_bv_normalize]
theorem val_inj (r1 r2 : Reg) :
    r1 = r2 ↔ r1.val = r2.val := ⟨(· ▸ rfl), Reg.val.inj⟩

@[veir_bv_normalize]
theorem val_li : (li imm).val = imm := (rfl)

@[veir_bv_normalize]
theorem val_lui : (lui imm).val = (imm ++ 0#12).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_auipc :
  (auipc imm pc).val = ((imm ++ 0#12).signExtend 64) + pc.val := (rfl)

@[veir_bv_normalize]
theorem val_addi :
  (addi imm r).val = r.val + imm.signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_slti :
  (slti imm r).val = (BitVec.ofBool (r.val.slt (imm.signExtend 64))).zeroExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_sltiu :
  (sltiu imm r).val = (BitVec.ofBool (r.val.ult (imm.signExtend 64))).zeroExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_andi :
  (andi imm r).val = r.val.and (imm.signExtend 64) := (rfl)

@[veir_bv_normalize]
theorem val_ori :
  (ori imm r).val = r.val.or (imm.signExtend 64) := (rfl)

@[veir_bv_normalize]
theorem val_xori :
  (xori imm r).val = r.val.xor (imm.signExtend 64) := (rfl)

@[veir_bv_normalize]
theorem val_addiw :
  (addiw imm r).val = (((imm.signExtend 64) + r.val).setWidth 32).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_slli :
  (slli shamt r).val = r.val <<< shamt := (rfl)

@[veir_bv_normalize]
theorem val_srli :
  (srli shamt r).val = r.val >>> shamt := (rfl)

@[veir_bv_normalize]
theorem val_srai :
  (srai shamt r).val = (r.val.sshiftRight' shamt).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_add :
  (add r2 r1).val = r1.val + r2.val := (rfl)

@[veir_bv_normalize]
theorem val_sub :
  (sub r2 r1).val = r1.val - r2.val := (rfl)

@[veir_bv_normalize]
theorem val_sll :
  (sll r2 r1).val = r1.val <<< (r2.val.extractLsb 5 0) := (rfl)

@[veir_bv_normalize]
theorem val_slt :
  (slt r2 r1).val = (BitVec.ofBool (r1.val.slt r2.val)).setWidth 64 := (rfl)

@[veir_bv_normalize]
theorem val_sltu :
  (sltu r2 r1).val = (BitVec.ofBool (r1.val.ult r2.val)).setWidth 64 := (rfl)

@[veir_bv_normalize]
theorem val_xor :
  (xor r2 r1).val = r1.val.xor r2.val := (rfl)

@[veir_bv_normalize]
theorem val_srl :
  (srl r2 r1).val = r1.val >>> (r2.val.extractLsb 5 0) := (rfl)

@[veir_bv_normalize]
theorem val_sra :
  (sra r2 r1).val = r1.val.sshiftRight' (r2.val.extractLsb 5 0) := (rfl)

@[veir_bv_normalize]
theorem val_or :
  (or r2 r1).val = r1.val.or r2.val := (rfl)

@[veir_bv_normalize]
theorem val_and :
  (and r2 r1).val = r1.val.and r2.val := (rfl)

@[veir_bv_normalize]
theorem val_slliw :
  (slliw shamt r).val = ((r.val.extractLsb' 0 32) <<< shamt).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_srliw :
  (srliw shamt r).val = ((r.val.extractLsb' 0 32) >>> shamt).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_sraiw :
  (sraiw shamt r).val = ((r.val.extractLsb' 0 32).sshiftRight' shamt).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_addw :
  (addw r2 r1).val = ((r1.val.extractLsb' 0 32) + (r2.val.extractLsb' 0 32)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_subw :
  (subw r2 r1).val = ((r1.val.extractLsb' 0 32) - (r2.val.extractLsb' 0 32)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_sllw :
  (sllw r2 r1).val = ((r1.val.extractLsb' 0 32) <<< ((r2.val.extractLsb' 0 32).extractLsb' 0 5)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_srlw :
  (srlw r2 r1).val =
    ((r1.val.extractLsb' 0 32) >>> ((r2.val.extractLsb' 0 32).extractLsb' 0 5)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_sraw :
  (sraw r2 r1).val =
    ((r1.val.extractLsb 31 0).sshiftRight' (r2.val.extractLsb 4 0)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_rem : (rem r2 r1).val = r1.val.srem r2.val := (rfl)

@[veir_bv_normalize]
theorem val_remu : (remu r2 r1).val = r1.val.umod r2.val := (rfl)

@[veir_bv_normalize]
theorem val_remw :
  (remw r2 r1).val =
    ((r1.val.extractLsb 31 0).srem (r2.val.extractLsb 31 0)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_remuw :
  (remuw r2 r1).val =
    ((r1.val.extractLsb 31 0).umod (r2.val.extractLsb 31 0)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_mul : (mul r2 r1).val = r1.val * r2.val := (rfl)

@[veir_bv_normalize]
theorem val_mulh :
  (mulh r2 r1).val = (r1.val.signExtend 129 * r2.val.signExtend 129).extractLsb 127 64 := (rfl)

@[veir_bv_normalize]
theorem val_mulhu :
  (mulhu r2 r1).val =
    ((r1.val.zeroExtend 128 * r2.val.zeroExtend 128).extractLsb' 0 128).extractLsb 127 64 := (rfl)

@[veir_bv_normalize]
theorem val_mulhsu :
  (mulhsu r2 r1).val = (r1.val.signExtend 129 * r2.val.zeroExtend 129).extractLsb 127 64 := (rfl)

@[veir_bv_normalize]
theorem val_mulw :
  (mulw r2 r1).val =
    ((r1.val.extractLsb 31 0).extractLsb 31 0 * (r2.val.extractLsb 31 0).extractLsb 31 0).signExtend 64 :=
  (rfl)

@[veir_bv_normalize]
theorem val_div :
  (div r2 r1).val = if r2.val = 0#64 then -1#64 else r1.val.sdiv r2.val := by
  simp [div]
  split <;>  (rfl)

@[veir_bv_normalize]
theorem val_divw :
  (divw r2 r1).val =
    (if r2.val.extractLsb 31 0 = 0#32
     then -1#32
     else (r1.val.extractLsb 31 0).sdiv (r2.val.extractLsb 31 0)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_divu :
  (divu r2 r1).val = if r2.val = 0#64 then (-1 : BitVec 64) else r1.val.udiv r2.val := by
  simp [divu]
  split <;>  (rfl)

@[veir_bv_normalize]
theorem val_divuw :
  (divuw r2 r1).val =
    (if r2.val.extractLsb 31 0 = 0#32
     then -1#32
     else (r1.val.extractLsb 31 0).udiv (r2.val.extractLsb 31 0)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_adduw :
  (adduw r2 r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< 0#2 + r2.val := (rfl)

@[veir_bv_normalize]
theorem val_sh1adduw :
  (sh1adduw r2 r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< 1#2 + r2.val := (rfl)

@[veir_bv_normalize]
theorem val_sh2adduw :
  (sh2adduw r2 r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< 2#2 + r2.val := (rfl)

@[veir_bv_normalize]
theorem val_sh3adduw :
  (sh3adduw r2 r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< 3#2 + r2.val := (rfl)

@[veir_bv_normalize]
theorem val_sh1add : (sh1add r2 r1).val = r1.val <<< 1#2 + r2.val := (rfl)

@[veir_bv_normalize]
theorem val_sh2add : (sh2add r2 r1).val = r1.val <<< 2#2 + r2.val := (rfl)

@[veir_bv_normalize]
theorem val_sh3add : (sh3add r2 r1).val = r1.val <<< 3#2 + r2.val := (rfl)

@[veir_bv_normalize]
theorem val_slliuw :
  (slliuw shamt r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< shamt := (rfl)

@[veir_bv_normalize]
theorem val_andn : (andn r2 r1).val = r1.val &&& ~~~r2.val := (rfl)

@[veir_bv_normalize]
theorem val_orn : (orn r2 r1).val = r1.val ||| ~~~r2.val := (rfl)

@[veir_bv_normalize]
theorem val_xnor : (xnor r2 r1).val = ~~~ (r1.val ^^^ r2.val) := (rfl)

@[veir_bv_normalize]
theorem val_max :
  (max r2 r1).val = (if r2.val.slt r1.val then r1.val else r2.val).extractLsb' 0 64 := (rfl)

@[veir_bv_normalize]
theorem val_maxu :
  (maxu r2 r1).val = (if r2.val.ult r1.val then r1.val else r2.val).extractLsb' 0 64 := (rfl)

@[veir_bv_normalize]
theorem val_min :
  (min r2 r1).val = (if r1.val.slt r2.val then r1.val else r2.val).extractLsb' 0 64 := (rfl)

@[veir_bv_normalize]
theorem val_minu :
  (minu r2 r1).val = (if r1.val.ult r2.val then r1.val else r2.val).extractLsb' 0 64 := (rfl)

@[veir_bv_normalize]
theorem val_rol :
  (rol r2 r1).val =  (r1.val <<< (r2.val.extractLsb 5 0)) ||| (r1.val >>> (64#6 - (r2.val.extractLsb 5 0))) :=
  (rfl)

@[veir_bv_normalize]
theorem val_ror :
  (ror r2 r1).val =
    (r1.val >>> (r2.val.extractLsb 5 0)) ||| (r1.val <<< (64#6 - (r2.val.extractLsb 5 0))) := (rfl)

@[veir_bv_normalize]
theorem val_rolw :
  (rolw r2 r1).val =
    ((r1.val.extractLsb 31 0 <<< (r2.val.extractLsb 4 0)) ||| (r1.val.extractLsb 31 0 >>> (32#5 - (r2.val.extractLsb 4 0)))).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_rorw :
  (rorw r2 r1).val =
    ((r1.val.extractLsb 31 0 >>> (r2.val.extractLsb 4 0)) ||| (r1.val.extractLsb 31 0 <<< (32#5 - (r2.val.extractLsb 4 0)))).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_sextb : (sextb r1).val = (r1.val.extractLsb 7 0).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_sexth : (sexth r1).val = (r1.val.extractLsb 15 0).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_zexth : (zexth r1).val = (r1.val.extractLsb 15 0).zeroExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_clz : (clz r1).val = r1.val.clz := (rfl)

@[veir_bv_normalize]
theorem val_clzw :
  (clzw r1).val = (r1.val.extractLsb 31 0).clz.zeroExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_ctz : (ctz r1).val = r1.val.ctz := (rfl)

@[veir_bv_normalize]
theorem val_ctzw :
  (ctzw r1).val = (r1.val.extractLsb 31 0).ctz.zeroExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_cpop : (cpop r1).val = r1.val.cpop := (rfl)

@[veir_bv_normalize]
theorem val_cpopw :
  (cpopw r1).val = (r1.val.extractLsb 31 0).cpop.zeroExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_roriw :
  (roriw shamt r1).val =
    ((r1.val.extractLsb 31 0 >>> shamt) ||| (r1.val.extractLsb 31 0 <<< (32 - shamt))).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_rori :
  (rori shamt r1).val = (r1.val >>> shamt) ||| (r1.val <<< (64 - shamt)) := (rfl)

@[veir_bv_normalize]
theorem val_orcb :
  (orcb r1).val =
    orcByte (r1.val.extractLsb 63 56) ++ orcByte (r1.val.extractLsb 55 48) ++
    orcByte (r1.val.extractLsb 47 40) ++ orcByte (r1.val.extractLsb 39 32) ++
    orcByte (r1.val.extractLsb 31 24) ++ orcByte (r1.val.extractLsb 23 16) ++
    orcByte (r1.val.extractLsb 15 8) ++ orcByte (r1.val.extractLsb 7 0) := (rfl)

@[veir_bv_normalize]
theorem orcByte_eq :
  orcByte bv = if bv = 0#8 then 0#8 else 255#8 := (rfl)

@[veir_bv_normalize]
theorem val_rev8 :
  (rev8 r1).val =
    r1.val.extractLsb 7 0 ++ r1.val.extractLsb 15 8 ++
    r1.val.extractLsb 23 16 ++ r1.val.extractLsb 31 24 ++
    r1.val.extractLsb 39 32 ++ r1.val.extractLsb 47 40 ++
    r1.val.extractLsb 55 48 ++ r1.val.extractLsb 63 56 := (rfl)

@[veir_bv_normalize]
theorem val_brev8 :
  (brev8 r1).val =
    (r1.val.extractLsb 63 56).reverse ++ (r1.val.extractLsb 55 48).reverse ++
    (r1.val.extractLsb 47 40).reverse ++ (r1.val.extractLsb 39 32).reverse ++
    (r1.val.extractLsb 31 24).reverse ++ (r1.val.extractLsb 23 16).reverse ++
    (r1.val.extractLsb 15 8).reverse ++ (r1.val.extractLsb 7 0).reverse := (rfl)

@[veir_bv_normalize]
theorem val_bclr :
  (bclr r2 r1).val =
    r1.val &&& ~~~(((1#1).zeroExtend 64) <<< (r2.val.extractLsb 5 0)) := (rfl)

@[veir_bv_normalize]
theorem val_bext :
  (bext r2 r1).val =
      (if r1.val &&& (((1#1).setWidth 64) <<< (r2.val.extractLsb 5 0)) != 0#64
       then 1#1 else 0#1).setWidth 64 := (rfl)

@[veir_bv_normalize]
theorem val_binv :
  (binv r2 r1).val =
    r1.val ^^^ (((1#1).zeroExtend 64) <<< (r2.val.extractLsb 5 0)) := (rfl)

@[veir_bv_normalize]
theorem val_bset :
  (bset r2 r1).val =
    r1.val ||| (((1#1).zeroExtend 64) <<< (r2.val.extractLsb 5 0)) := (rfl)

@[veir_bv_normalize]
theorem val_bclri :
  (bclri shamt r1).val = r1.val &&& ~~~((1#1).setWidth 64 <<< shamt) := (rfl)

@[veir_bv_normalize]
theorem val_bexti :
  (bexti shamt r1).val =
      (if r1.val &&& (((1#1).setWidth 64) <<< shamt) != 0#64 then 1#1 else 0#1).setWidth 64 := (rfl)

@[veir_bv_normalize]
theorem val_binvi :
  (binvi shamt r1).val = r1.val ^^^ (((1#1).zeroExtend 64) <<< shamt) := (rfl)

@[veir_bv_normalize]
theorem val_bseti :
  (bseti shamt r1).val = r1.val ||| (((1#1).zeroExtend 64) <<< shamt) := (rfl)

@[veir_bv_normalize]
theorem val_pack :
  (pack r2 r1).val =
    r2.val.extractLsb 31 0 ++ r1.val.extractLsb 31 0 := (rfl)

@[veir_bv_normalize]
theorem val_packh :
  (packh r2 r1).val =
    ((r2.val.extractLsb 7 0) ++ (r1.val.extractLsb 7 0)).zeroExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_packw :
  (packw r2 r1).val =
    ((r2.val.extractLsb 15 0) ++ (r1.val.extractLsb 15 0)).signExtend 64 := (rfl)

@[veir_bv_normalize]
theorem val_czeroeqz :
  (czeroeqz r2 r1).val = (if r2.val == 0 then 0 else r1.val) := (rfl)

@[veir_bv_normalize]
theorem val_czeronez :
  (czeronez r2 r1).val = (if r2.val != 0 then 0 else r1.val) := (rfl)

@[veir_bv_normalize]
theorem val_mv : (mv r1).val = (addi 0 r1).val := (rfl)

@[veir_bv_normalize]
theorem val_not : (not r1).val = (xori (-1) r1).val := (rfl)

@[veir_bv_normalize]
theorem val_neg : (neg r1).val = (sub r1 (li 0)).val := (rfl)

@[veir_bv_normalize]
theorem val_negw : (negw r1).val = (subw r1 (li 0)).val := (rfl)

@[veir_bv_normalize]
theorem val_sextw : (sextw r1).val = (addiw 0 r1).val := (rfl)

@[veir_bv_normalize]
theorem val_zextb : (zextb r1).val = (andi 255 r1).val := (rfl)

@[veir_bv_normalize]
theorem val_zextw : (zextw r1).val = (adduw (li 0) r1).val := (rfl)

@[veir_bv_normalize]
theorem val_seqz : (seqz r1).val = (sltiu 1 r1).val := (rfl)

@[veir_bv_normalize]
theorem val_snez : (snez r1).val = (sltu r1 (li 0)).val := (rfl)

@[veir_bv_normalize]
theorem val_sltz : (sltz r1).val = (slt (li 0) r1).val := (rfl)

@[veir_bv_normalize]
theorem val_sgtz : (sgtz r1).val = (slt r1 (li 0)).val := (rfl)

/-! ### add -/

@[veir_bv_normalize]
theorem add_li_zero (r : Reg) : add (li 0#64) r = r := by
  simp [add, li]

@[veir_bv_normalize]
theorem add_li_addi (c : BitVec 64) (r : Reg) (h₁ : -2048 ≤ c.toInt) (h₂ : c.toInt ≤ 2047) :
    add (li c) r = addi (c.setWidth 12) r := by
  simp only [add, li, addi, BitVec.add_eq, Reg.mk.injEq, BitVec.add_right_inj]
  simp only [Nat.reduceLeDiff, ← BitVec.signExtend_eq_setWidth_of_le, ← BitVec.toInt_inj,
    BitVec.toInt_signExtend, Nat.min_eq_left, Nat.reducePow, Nat.min_eq_right, Int.bmod_bmod]
  rw [Int.bmod_eq_of_le (by omega) (by omega)]


@[veir_bv_normalize]
theorem add_li_addi_comm (c : BitVec 64) (r : Reg) (h₁ : -2048 ≤ c.toInt) (h₂ : c.toInt ≤ 2047) :
    add r (li c) = addi (c.setWidth 12) r := by
  simp [add, li, addi, BitVec.add_eq, Reg.mk.injEq]
  rw [BitVec.add_comm, BitVec.add_right_inj]
  simp only [Nat.reduceLeDiff, ← BitVec.signExtend_eq_setWidth_of_le, ← BitVec.toInt_inj,
    BitVec.toInt_signExtend, Nat.min_eq_left, Nat.reducePow, Nat.min_eq_right, Int.bmod_bmod]
  rw [Int.bmod_eq_of_le (by omega) (by omega)]

/-! ### and -/

@[veir_bv_normalize]
theorem and_li_zextw (r : Reg) : and (li ((BitVec.allOnes 32).setWidth 64)) r = zextw r := by
  simp only [and, li, zextw, adduw, Nat.sub_zero, -Nat.reduceAdd, BitVec.truncate_eq_setWidth,
    BitVec.shiftLeft_eq', BitVec.toNat_ofNat, -Nat.reducePow, Nat.zero_mod, BitVec.shiftLeft_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, Reg.mk.injEq]
  ext k hk
  simp only [BitVec.getElem_and, BitVec.getElem_setWidth, Nat.reduceAdd, BitVec.getLsbD_extract,
    Nat.sub_zero, Nat.zero_add]
  by_cases hk' : r.val.getLsbD k
  <;> simp [hk', -BitVec.reduceAllOnes, Bool.true_and, BitVec.getLsbD_allOnes,
      ← BitVec.getLsbD_eq_getElem]
  omega

@[veir_bv_normalize]
theorem and_li_zextw_comm (r : Reg) : and r (li ((BitVec.allOnes 32).setWidth 64)) = zextw r := by
  simp only [and, li, zextw, adduw, Nat.sub_zero, -Nat.reduceAdd, BitVec.truncate_eq_setWidth,
    BitVec.shiftLeft_eq', BitVec.toNat_ofNat, -Nat.reducePow, Nat.zero_mod, BitVec.shiftLeft_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, Reg.mk.injEq]
  ext k hk
  simp only [BitVec.getElem_and, BitVec.getElem_setWidth, Nat.reduceAdd, BitVec.getLsbD_extract,
    Nat.sub_zero, Nat.zero_add]
  by_cases hk' : r.val.getLsbD k
  <;> simp [hk', -BitVec.reduceAllOnes, BitVec.getLsbD_allOnes,
      ← BitVec.getLsbD_eq_getElem]
  omega

/-! ### or

Byte packing: the operands are zero-extended bytes, as returned by `lbu`. -/

@[veir_bv_normalize]
theorem or_slli_packh (hi lo : BitVec 8) :
    or (slli 8#6 ⟨hi.setWidth 64⟩) ⟨lo.setWidth 64⟩ = packh ⟨hi.setWidth 64⟩ ⟨lo.setWidth 64⟩ := by
  simp [packh, slli, or]
  grind

@[veir_bv_normalize]
theorem or_slli_packh_comm (hi lo : BitVec 8) :
    or ⟨lo.setWidth 64⟩ (slli 8#6 ⟨hi.setWidth 64⟩) = packh ⟨hi.setWidth 64⟩ ⟨lo.setWidth 64⟩ := by
  simp [or, slli, packh]
  grind

@[veir_bv_normalize]
theorem or_slli_slli_packh (hi lo : BitVec 8) :
    or (slli 24#6 ⟨hi.setWidth 64⟩) (slli 16#6 ⟨lo.setWidth 64⟩) =
      slli 16#6 (packh ⟨hi.setWidth 64⟩ ⟨lo.setWidth 64⟩) := by
  simp [or, slli, packh]
  grind

@[veir_bv_normalize]
theorem or_slli_slli_packh_comm (hi lo : BitVec 8) :
    or (slli 16#6 ⟨lo.setWidth 64⟩) (slli 24#6 ⟨hi.setWidth 64⟩) =
      slli 16#6 (packh ⟨hi.setWidth 64⟩ ⟨lo.setWidth 64⟩) := by
  simp [or, slli, packh]
  grind

/-! ### andi -/

@[veir_bv_normalize]
theorem andi_one_srli (r : Reg) : andi 1#12 (srli 63#6 r) = srli 63#6 r := by
  simp [srli, andi]
  grind

@[veir_bv_normalize]
theorem andi_mk_setWidth (x : BitVec 8) :
    andi ((BitVec.allOnes 8).setWidth 12) ⟨x.setWidth 64⟩ = ⟨x.setWidth 64⟩ := by
  simp only [andi, BitVec.and_eq, Reg.mk.injEq]
  ext k hk
  simp only [BitVec.getElem_and, BitVec.getElem_setWidth, Bool.and_eq_left_iff_imp]
  intro h
  have := BitVec.getLsbD_of_ge (x := x) k
  have : k < 8 := by
    apply Classical.byContradiction
    intro hcontra
    simp at hcontra
    specialize this hcontra
    simp [this] at h
  simp only [BitVec.getElem_signExtend, show k < 12 by omega, ↓reduceDIte, BitVec.getElem_setWidth,
    BitVec.getLsbD_allOnes]
  simp [this]

/-! ### Shift amounts

A shift reads only the low six (`sll`, `srl`, `sra`) or five (`sllw`, `srlw`, `sraw`) bits of its
amount, the first argument. -/

@[veir_bv_normalize]
theorem sll_andi_left (c : BitVec 64) (r2 r1 : Reg)
    (h : c &&& (BitVec.allOnes 6).setWidth 64 = (BitVec.allOnes 6).setWidth 64) :
    sll (andi (c.setWidth 12) r2) r1 = sll r2 r1 := by
  simp [andi, sll]
  congr
  sorry

@[veir_bv_normalize]
theorem srl_andi_left (c : BitVec 64) (r2 r1 : Reg)
    (h : c &&& (BitVec.allOnes 6).setWidth 64 = (BitVec.allOnes 6).setWidth 64) :
    srl (andi (c.setWidth 12) r2) r1 = srl r2 r1 := by
  simp only [srl, andi, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sra_andi_left (c : BitVec 64) (r2 r1 : Reg)
    (h : c &&& (BitVec.allOnes 6).setWidth 64 = (BitVec.allOnes 6).setWidth 64) :
    sra (andi (c.setWidth 12) r2) r1 = sra r2 r1 := by
  simp only [sra, andi, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sllw_andi_left (c : BitVec 64) (r2 r1 : Reg)
    (h : c &&& (BitVec.allOnes 5).setWidth 64 = (BitVec.allOnes 5).setWidth 64) :
    sllw (andi (c.setWidth 12) r2) r1 = sllw r2 r1 := by
  simp only [sllw, andi, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem srlw_andi_left (c : BitVec 64) (r2 r1 : Reg)
    (h : c &&& (BitVec.allOnes 5).setWidth 64 = (BitVec.allOnes 5).setWidth 64) :
    srlw (andi (c.setWidth 12) r2) r1 = srlw r2 r1 := by
  simp only [srlw, andi, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sraw_andi_left (c : BitVec 64) (r2 r1 : Reg)
    (h : c &&& (BitVec.allOnes 5).setWidth 64 = (BitVec.allOnes 5).setWidth 64) :
    sraw (andi (c.setWidth 12) r2) r1 = sraw r2 r1 := by
  simp only [sraw, andi, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sll_zextw_left (r2 r1 : Reg) : sll (zextw r2) r1 = sll r2 r1 := by
  simp [sll, zextw, adduw, li]

@[veir_bv_normalize]
theorem srl_zextw_left (r2 r1 : Reg) : srl (zextw r2) r1 = srl r2 r1 := by
  simp [srl, zextw, adduw, li]

@[veir_bv_normalize]
theorem sra_zextw_left (r2 r1 : Reg) : sra (zextw r2) r1 = sra r2 r1 := by
  simp [sra, zextw, adduw, li]

/-! ### srli -/

@[veir_bv_normalize]
theorem srli_srai (c : BitVec 64) (shamt : BitVec 6) (r : Reg) (h : c.toInt = 63) :
    srli (c.setWidth 6) (srai shamt r) = srli (c.setWidth 6) r := by
  simp [srli, srai]
  grind

@[veir_bv_normalize]
theorem srli_slli_slt (r2 r1 : Reg) : srli 63#6 (slli 63#6 (slt r2 r1)) = slt r2 r1 := by
  simp [srli, slli, slt]
  grind

@[veir_bv_normalize]
theorem srli_slli_sltu (r2 r1 : Reg) : srli 63#6 (slli 63#6 (sltu r2 r1)) = sltu r2 r1 := by
  simp [srli, slli, sltu]
  grind

@[veir_bv_normalize]
theorem srli_slli_slti (imm : BitVec 12) (r : Reg) :
    srli 63#6 (slli 63#6 (slti imm r)) = slti imm r := by
  simp [srli, slli, slti]
  grind

@[veir_bv_normalize]
theorem srli_slli_sltiu (imm : BitVec 12) (r : Reg) :
    srli 63#6 (slli 63#6 (sltiu imm r)) = sltiu imm r := by
  simp [srli, slli, sltiu]
  grind

@[veir_bv_normalize]
theorem srli_slli_seqz (r : Reg) : srli 63#6 (slli 63#6 (seqz r)) = seqz r := by
  simp [srli, slli, seqz, sltiu]
  grind

@[veir_bv_normalize]
theorem srli_slli_snez (r : Reg) : srli 63#6 (slli 63#6 (snez r)) = snez r := by
  simp [srli, slli, snez, sltu, li]
  grind

@[veir_bv_normalize]
theorem srli_slli_sltz (r : Reg) : srli 63#6 (slli 63#6 (sltz r)) = sltz r := by
  simp [srli, slli, sltz, slt, li]
  grind

@[veir_bv_normalize]
theorem srli_slli_sgtz (r : Reg) : srli 63#6 (slli 63#6 (sgtz r)) = sgtz r := by
  simp [srli, slli, sgtz, slt, li]
  grind

/-! ### srliw -/

@[veir_bv_normalize]
theorem srliw_sraiw (c : BitVec 64) (shamt : BitVec 5) (r : Reg) (h : c.toInt = 31) :
    srliw (c.setWidth 5) (sraiw shamt r) = srliw (c.setWidth 5) r := by
  obtain rfl : c = 31#64 := BitVec.eq_of_toInt_eq (by simpa using h)
  simp only [srliw, sraiw, Reg.mk.injEq]
  bv_decide

/-! ### zextw -/

@[veir_bv_normalize]
theorem zextw_zextw (r : Reg) : zextw (zextw r) = zextw r := by
  simp [zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem zextw_li (c : BitVec 64) (h : c < 4294967296#64) : zextw (li c) = li c := by
  simp only [zextw, li, adduw, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem zextw_zextb (r : Reg) : zextw (zextb r) = zextb r := by
  simp only [zextw, zextb, adduw, li, andi, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem zextw_sextw (r : Reg) : zextw (sextw r) = zextw r := by
  simp only [zextw, sextw, adduw, li, addiw]
  grind

@[veir_bv_normalize]
theorem zextw_slliw_mk_setWidth_8 (x : BitVec 8) :
    zextw (slliw 8#5 ⟨x.setWidth 64⟩) = slli 8#6 ⟨x.setWidth 64⟩ := by
  simp [zextw, slliw, slli, adduw, li]
  grind

@[veir_bv_normalize]
theorem zextw_slliw_mk_setWidth_16 (x : BitVec 8) :
    zextw (slliw 16#5 ⟨x.setWidth 64⟩) = slli 16#6 ⟨x.setWidth 64⟩ := by
  simp [zextw, slliw, slli, adduw, li]
  grind

@[veir_bv_normalize]
theorem zextw_slliw_mk_setWidth_24 (x : BitVec 8) :
    zextw (slliw 24#5 ⟨x.setWidth 64⟩) = slli 24#6 ⟨x.setWidth 64⟩ := by
  simp [zextw, slliw, slli, adduw, li]
  grind

@[veir_bv_normalize]
theorem zextw_and_zextw_left (r2 r1 : Reg) :
    zextw (and (zextw r2) r1) = and (zextw r2) r1 := by
  simp [zextw, and, adduw, li]
  grind

@[veir_bv_normalize]
theorem zextw_and_zextw_right (r2 r1 : Reg) :
    zextw (and r2 (zextw r1)) = and r2 (zextw r1) := by
  simp [zextw, and, adduw, li]
  grind

@[veir_bv_normalize]
theorem zextw_or_zextw (r2 r1 : Reg) :
    zextw (or (zextw r2) (zextw r1)) = or (zextw r2) (zextw r1) := by
  simp [zextw, or, adduw, li]
  grind

@[veir_bv_normalize]
theorem zextw_xor_zextw (r2 r1 : Reg) :
    zextw (xor (zextw r2) (zextw r1)) = xor (zextw r2) (zextw r1) := by
  simp [zextw, xor, adduw, li]
  grind

/-! ### zextb -/

@[veir_bv_normalize]
theorem zextb_zextb (r : Reg) : zextb (zextb r) = zextb r := by
  simp only [zextb, andi]
  grind

@[veir_bv_normalize]
theorem zextb_li (c : BitVec 64) (h₁ : 0 ≤ c.toInt) (h₂ : c.toInt < 256) :
    zextb (li c) = li c := by
  have h₁ : (0#64).sle c := by simpa [BitVec.sle_iff_toInt_le] using h₁
  have h₂ : c.slt 256#64 := by simpa [BitVec.slt_iff_toInt_lt] using h₂
  simp only [zextb, li, andi, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem zextb_mk_setWidth (x : BitVec 8) : zextb ⟨x.setWidth 64⟩ = ⟨x.setWidth 64⟩ := by
  simp only [zextb, andi, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem zextb_and_zextb_left (r2 r1 : Reg) :
    zextb (and (zextb r2) r1) = and (zextb r2) r1 := by
  simp only [zextb, and, andi]
  grind

@[veir_bv_normalize]
theorem zextb_and_zextb_right (r2 r1 : Reg) :
    zextb (and r2 (zextb r1)) = and r2 (zextb r1) := by
  simp only [zextb, and, andi]
  grind

@[veir_bv_normalize]
theorem zextb_or_zextb (r2 r1 : Reg) :
    zextb (or (zextb r2) (zextb r1)) = or (zextb r2) (zextb r1) := by
  simp [zextb, or, andi]
  grind

@[veir_bv_normalize]
theorem zextb_xor_zextb (r2 r1 : Reg) :
    zextb (xor (zextb r2) (zextb r1)) = xor (zextb r2) (zextb r1) := by
  simp [zextb, xor, andi]
  grind

/-! ### zexth -/

@[veir_bv_normalize]
theorem zexth_zexth (r : Reg) : zexth (zexth r) = zexth r := by
  simp [zexth]
  grind

@[veir_bv_normalize]
theorem zexth_li (c : BitVec 64) (h₁ : 0 ≤ c.toInt) (h₂ : c.toInt < 65536) :
    zexth (li c) = li c := by
  have h₁ : (0#64).sle c := by simpa [BitVec.sle_iff_toInt_le] using h₁
  have h₂ : c.slt 65536#64 := by simpa [BitVec.slt_iff_toInt_lt] using h₂
  simp only [zexth, li, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem zexth_and_zexth_left (r2 r1 : Reg) :
    zexth (and (zexth r2) r1) = and (zexth r2) r1 := by
  simp [zexth, and]
  grind

@[veir_bv_normalize]
theorem zexth_and_zexth_right (r2 r1 : Reg) :
    zexth (and r2 (zexth r1)) = and r2 (zexth r1) := by
  simp [zexth, and]
  grind

@[veir_bv_normalize]
theorem zexth_or_zexth (r2 r1 : Reg) :
    zexth (or (zexth r2) (zexth r1)) = or (zexth r2) (zexth r1) := by
  simp [zexth, or]
  grind

@[veir_bv_normalize]
theorem zexth_xor_zexth (r2 r1 : Reg) :
    zexth (xor (zexth r2) (zexth r1)) = xor (zexth r2) (zexth r1) := by
  simp [zexth, xor]
  grind

/-! ### sextb -/

@[veir_bv_normalize]
theorem sextb_sextb (r : Reg) : sextb (sextb r) = sextb r := by
  simp [sextb]
  grind

@[veir_bv_normalize]
theorem sextb_li (c : BitVec 64) (h₁ : -128 ≤ c.toInt) (h₂ : c.toInt < 128) :
    sextb (li c) = li c := by
  have h₁ : (-128#64).sle c := by simpa [BitVec.sle_iff_toInt_le] using h₁
  have h₂ : c.slt 128#64 := by simpa [BitVec.slt_iff_toInt_lt] using h₂
  simp only [sextb, li, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sextb_and_sextb (r2 r1 : Reg) :
    sextb (and (sextb r2) (sextb r1)) = and (sextb r2) (sextb r1) := by
  simp [sextb, and]
  grind

@[veir_bv_normalize]
theorem sextb_or_sextb (r2 r1 : Reg) :
    sextb (or (sextb r2) (sextb r1)) = or (sextb r2) (sextb r1) := by
  simp [sextb, or]
  grind

@[veir_bv_normalize]
theorem sextb_xor_sextb (r2 r1 : Reg) :
    sextb (xor (sextb r2) (sextb r1)) = xor (sextb r2) (sextb r1) := by
  simp [sextb, xor]
  grind

/-! ### sexth -/

@[veir_bv_normalize]
theorem sexth_sexth (r : Reg) : sexth (sexth r) = sexth r := by
  simp [sexth]
  grind

@[veir_bv_normalize]
theorem sexth_li (c : BitVec 64) (h₁ : -32768 ≤ c.toInt) (h₂ : c.toInt < 32768) :
    sexth (li c) = li c := by
  have h₁ : (-32768#64).sle c := by simpa [BitVec.sle_iff_toInt_le] using h₁
  have h₂ : c.slt 32768#64 := by simpa [BitVec.slt_iff_toInt_lt] using h₂
  simp only [sexth, li, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sexth_and_sexth (r2 r1 : Reg) :
    sexth (and (sexth r2) (sexth r1)) = and (sexth r2) (sexth r1) := by
  simp [sexth, and]
  grind

@[veir_bv_normalize]
theorem sexth_or_sexth (r2 r1 : Reg) :
    sexth (or (sexth r2) (sexth r1)) = or (sexth r2) (sexth r1) := by
  simp [sexth, or]
  grind

@[veir_bv_normalize]
theorem sexth_xor_sexth (r2 r1 : Reg) :
    sexth (xor (sexth r2) (sexth r1)) = xor (sexth r2) (sexth r1) := by
  simp [sexth, xor]
  grind

/-! ### sextw -/

@[veir_bv_normalize]
theorem sextw_sextw (r : Reg) : sextw (sextw r) = sextw r := by
  simp only [sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_li (c : BitVec 64) (h₁ : -2147483648 ≤ c.toInt) (h₂ : c.toInt < 2147483648) :
    sextw (li c) = li c := by
  simp [sextw, li, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_zextw (r : Reg) : sextw (zextw r) = sextw r := by
  simp only [sextw, zextw, addiw, adduw, li]
  grind

@[veir_bv_normalize]
theorem sextw_and_sextw (r2 r1 : Reg) :
    sextw (and (sextw r2) (sextw r1)) = and (sextw r2) (sextw r1) := by
  simp [sextw, and, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_or_sextw (r2 r1 : Reg) :
    sextw (or (sextw r2) (sextw r1)) = or (sextw r2) (sextw r1) := by
  simp [sextw, or, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_xor_sextw (r2 r1 : Reg) :
    sextw (xor (sextw r2) (sextw r1)) = xor (sextw r2) (sextw r1) := by
  simp [sextw, xor, addiw]
  grind

/-! `sextw` of a loaded value: a signed load sign-extends the bits it read, an unsigned load
zero-extends them. -/

@[veir_bv_normalize]
theorem sextw_mk_signExtend_32 (x : BitVec 32) :
    sextw ⟨x.signExtend 64⟩ = ⟨x.signExtend 64⟩ := by
  simp only [sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_mk_signExtend_16 (x : BitVec 16) :
    sextw ⟨x.signExtend 64⟩ = ⟨x.signExtend 64⟩ := by
  simp [sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_mk_signExtend_8 (x : BitVec 8) :
    sextw ⟨x.signExtend 64⟩ = ⟨x.signExtend 64⟩ := by
  simp [sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_mk_setWidth_16 (x : BitVec 16) : sextw ⟨x.setWidth 64⟩ = ⟨x.setWidth 64⟩ := by
  simp [sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_mk_setWidth_8 (x : BitVec 8) : sextw ⟨x.setWidth 64⟩ = ⟨x.setWidth 64⟩ := by
  simp [sextw, addiw]
  grind

/-! `sextw` of an operation that already returns a sign-extended 32-bit value. -/

@[veir_bv_normalize]
theorem sextw_addw (r2 r1 : Reg) : sextw (addw r2 r1) = addw r2 r1 := by
  simp only [sextw, addw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_addiw (imm : BitVec 12) (r : Reg) : sextw (addiw imm r) = addiw imm r := by
  simp only [sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_subw (r2 r1 : Reg) : sextw (subw r2 r1) = subw r2 r1 := by
  simp only [sextw, subw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_mulw (r2 r1 : Reg) : sextw (mulw r2 r1) = mulw r2 r1 := by
  simp only [sextw, mulw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_divw (r2 r1 : Reg) : sextw (divw r2 r1) = divw r2 r1 := by
  simp only [sextw, divw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_divuw (r2 r1 : Reg) : sextw (divuw r2 r1) = divuw r2 r1 := by
  simp only [sextw, divuw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_remw (r2 r1 : Reg) : sextw (remw r2 r1) = remw r2 r1 := by
  simp only [sextw, remw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_remuw (r2 r1 : Reg) : sextw (remuw r2 r1) = remuw r2 r1 := by
  simp only [sextw, remuw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_sllw (r2 r1 : Reg) : sextw (sllw r2 r1) = sllw r2 r1 := by
  simp only [sextw, sllw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_slliw (shamt : BitVec 5) (r : Reg) : sextw (slliw shamt r) = slliw shamt r := by
  simp only [sextw, slliw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_srlw (r2 r1 : Reg) : sextw (srlw r2 r1) = srlw r2 r1 := by
  simp only [sextw, srlw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_srliw (shamt : BitVec 5) (r : Reg) : sextw (srliw shamt r) = srliw shamt r := by
  simp only [sextw, srliw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_sraw (r2 r1 : Reg) : sextw (sraw r2 r1) = sraw r2 r1 := by
  simp only [sextw, sraw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_sraiw (shamt : BitVec 5) (r : Reg) : sextw (sraiw shamt r) = sraiw shamt r := by
  simp only [sextw, sraiw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_rolw (r2 r1 : Reg) : sextw (rolw r2 r1) = rolw r2 r1 := by
  simp [sextw, rolw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_rorw (r2 r1 : Reg) : sextw (rorw r2 r1) = rorw r2 r1 := by
  simp [sextw, rorw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_roriw (shamt : BitVec 5) (r : Reg) : sextw (roriw shamt r) = roriw shamt r := by
  simp [sextw, roriw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_packw (r2 r1 : Reg) : sextw (packw r2 r1) = packw r2 r1 := by
  simp only [sextw, packw, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_lui (imm : BitVec 20) : sextw (lui imm) = lui imm := by
  simp only [sextw, lui, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_cpop (r : Reg) : sextw (cpop r) = cpop r := by
  simp only [sextw, cpop, addiw, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sextw_cpopw (r : Reg) : sextw (cpopw r) = cpopw r := by
  simp only [sextw, cpopw, addiw, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sextw_clz (r : Reg) : sextw (clz r) = clz r := by
  simp only [sextw, clz, addiw, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sextw_clzw (r : Reg) : sextw (clzw r) = clzw r := by
  simp only [sextw, clzw, addiw, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sextw_ctz (r : Reg) : sextw (ctz r) = ctz r := by
  simp only [sextw, ctz, addiw, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sextw_ctzw (r : Reg) : sextw (ctzw r) = ctzw r := by
  simp only [sextw, ctzw, addiw, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem sextw_slt (r2 r1 : Reg) : sextw (slt r2 r1) = slt r2 r1 := by
  simp [sextw, slt, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_sltu (r2 r1 : Reg) : sextw (sltu r2 r1) = sltu r2 r1 := by
  simp [sextw, sltu, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_slti (imm : BitVec 12) (r : Reg) : sextw (slti imm r) = slti imm r := by
  simp [sextw, slti, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_sltiu (imm : BitVec 12) (r : Reg) : sextw (sltiu imm r) = sltiu imm r := by
  simp [sextw, sltiu, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_bext (r2 r1 : Reg) : sextw (bext r2 r1) = bext r2 r1 := by
  simp only [sextw, bext, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_bexti (shamt : BitVec 6) (r : Reg) : sextw (bexti shamt r) = bexti shamt r := by
  simp only [sextw, bexti, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_sextb (r : Reg) : sextw (sextb r) = sextb r := by
  simp [sextw, sextb, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_sexth (r : Reg) : sextw (sexth r) = sexth r := by
  simp [sextw, sexth, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_zexth (r : Reg) : sextw (zexth r) = zexth r := by
  simp [sextw, zexth, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_packh (r2 r1 : Reg) : sextw (packh r2 r1) = packh r2 r1 := by
  simp [sextw, packh, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_srai (shamt : BitVec 6) (r : Reg) (h : 32#6 ≤ shamt) :
    sextw (srai shamt r) = srai shamt r := by
  simp [sextw, srai, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_srli (shamt : BitVec 6) (r : Reg) (h : 32#6 < shamt) :
    sextw (srli shamt r) = srli shamt r := by
  simp [sextw, srli, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_andi (imm : BitVec 12) (r : Reg) (h : imm.msb = false) :
    sextw (andi imm r) = andi imm r := by
  simp [sextw, andi, addiw]
  grind

@[veir_bv_normalize]
theorem sextw_ori (imm : BitVec 12) (r : Reg) (h : imm.msb = true) :
    sextw (ori imm r) = ori imm r := by
  simp [sextw, ori, addiw]
  grind

/-! ### Extensions of an operand the consumer ignores

The consumer reads only bits 31:0 of the operand, which `zextw` and `sextw` leave unchanged. -/

@[veir_bv_normalize]
theorem addw_zextw_left (r2 r1 : Reg) : addw (zextw r2) r1 = addw r2 r1 := by
  simp only [addw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem addw_zextw_right (r2 r1 : Reg) : addw r2 (zextw r1) = addw r2 r1 := by
  simp only [addw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem addw_sextw_left (r2 r1 : Reg) : addw (sextw r2) r1 = addw r2 r1 := by
  simp only [addw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem addw_sextw_right (r2 r1 : Reg) : addw r2 (sextw r1) = addw r2 r1 := by
  simp only [addw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem subw_zextw_left (r2 r1 : Reg) : subw (zextw r2) r1 = subw r2 r1 := by
  simp only [subw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem subw_zextw_right (r2 r1 : Reg) : subw r2 (zextw r1) = subw r2 r1 := by
  simp only [subw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem subw_sextw_left (r2 r1 : Reg) : subw (sextw r2) r1 = subw r2 r1 := by
  simp only [subw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem subw_sextw_right (r2 r1 : Reg) : subw r2 (sextw r1) = subw r2 r1 := by
  simp only [subw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem mulw_zextw_left (r2 r1 : Reg) : mulw (zextw r2) r1 = mulw r2 r1 := by
  simp [mulw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem mulw_zextw_right (r2 r1 : Reg) : mulw r2 (zextw r1) = mulw r2 r1 := by
  simp [mulw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem mulw_sextw_left (r2 r1 : Reg) : mulw (sextw r2) r1 = mulw r2 r1 := by
  simp [mulw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem mulw_sextw_right (r2 r1 : Reg) : mulw r2 (sextw r1) = mulw r2 r1 := by
  simp [mulw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem divw_zextw_left (r2 r1 : Reg) : divw (zextw r2) r1 = divw r2 r1 := by
  simp [divw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem divw_zextw_right (r2 r1 : Reg) : divw r2 (zextw r1) = divw r2 r1 := by
  simp only [divw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem divw_sextw_left (r2 r1 : Reg) : divw (sextw r2) r1 = divw r2 r1 := by
  simp [divw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem divw_sextw_right (r2 r1 : Reg) : divw r2 (sextw r1) = divw r2 r1 := by
  simp only [divw, sextw, addiw]
  bv_decide

@[veir_bv_normalize]
theorem divuw_zextw_left (r2 r1 : Reg) : divuw (zextw r2) r1 = divuw r2 r1 := by
  simp [divuw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem divuw_zextw_right (r2 r1 : Reg) : divuw r2 (zextw r1) = divuw r2 r1 := by
  simp [divuw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem divuw_sextw_left (r2 r1 : Reg) : divuw (sextw r2) r1 = divuw r2 r1 := by
  simp [divuw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem divuw_sextw_right (r2 r1 : Reg) : divuw r2 (sextw r1) = divuw r2 r1 := by
  simp [divuw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem remw_zextw_left (r2 r1 : Reg) : remw (zextw r2) r1 = remw r2 r1 := by
  simp only [remw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem remw_zextw_right (r2 r1 : Reg) : remw r2 (zextw r1) = remw r2 r1 := by
  simp only [remw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem remw_sextw_left (r2 r1 : Reg) : remw (sextw r2) r1 = remw r2 r1 := by
  simp only [remw, sextw, addiw]
  bv_decide

@[veir_bv_normalize]
theorem remw_sextw_right (r2 r1 : Reg) : remw r2 (sextw r1) = remw r2 r1 := by
  simp only [remw, sextw, addiw]
  bv_decide

@[veir_bv_normalize]
theorem remuw_zextw_left (r2 r1 : Reg) : remuw (zextw r2) r1 = remuw r2 r1 := by
  simp [remuw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem remuw_zextw_right (r2 r1 : Reg) : remuw r2 (zextw r1) = remuw r2 r1 := by
  simp [remuw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem remuw_sextw_left (r2 r1 : Reg) : remuw (sextw r2) r1 = remuw r2 r1 := by
  simp only [remuw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem remuw_sextw_right (r2 r1 : Reg) : remuw r2 (sextw r1) = remuw r2 r1 := by
  simp only [remuw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sllw_zextw_left (r2 r1 : Reg) : sllw (zextw r2) r1 = sllw r2 r1 := by
  simp [sllw, zextw, adduw, li]

@[veir_bv_normalize]
theorem sllw_zextw_right (r2 r1 : Reg) : sllw r2 (zextw r1) = sllw r2 r1 := by
  simp [sllw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem sllw_sextw_left (r2 r1 : Reg) : sllw (sextw r2) r1 = sllw r2 r1 := by
  simp only [sllw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sllw_sextw_right (r2 r1 : Reg) : sllw r2 (sextw r1) = sllw r2 r1 := by
  simp only [sllw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem srlw_zextw_left (r2 r1 : Reg) : srlw (zextw r2) r1 = srlw r2 r1 := by
  simp [srlw, zextw, adduw, li]

@[veir_bv_normalize]
theorem srlw_zextw_right (r2 r1 : Reg) : srlw r2 (zextw r1) = srlw r2 r1 := by
  simp [srlw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem srlw_sextw_left (r2 r1 : Reg) : srlw (sextw r2) r1 = srlw r2 r1 := by
  simp only [srlw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem srlw_sextw_right (r2 r1 : Reg) : srlw r2 (sextw r1) = srlw r2 r1 := by
  simp only [srlw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sraw_zextw_left (r2 r1 : Reg) : sraw (zextw r2) r1 = sraw r2 r1 := by
  simp [sraw, zextw, adduw, li]

@[veir_bv_normalize]
theorem sraw_zextw_right (r2 r1 : Reg) : sraw r2 (zextw r1) = sraw r2 r1 := by
  simp [sraw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem sraw_sextw_left (r2 r1 : Reg) : sraw (sextw r2) r1 = sraw r2 r1 := by
  simp only [sraw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sraw_sextw_right (r2 r1 : Reg) : sraw r2 (sextw r1) = sraw r2 r1 := by
  simp only [sraw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem rolw_zextw_left (r2 r1 : Reg) : rolw (zextw r2) r1 = rolw r2 r1 := by
  simp [rolw, zextw, adduw, li]

@[veir_bv_normalize]
theorem rolw_zextw_right (r2 r1 : Reg) : rolw r2 (zextw r1) = rolw r2 r1 := by
  simp only [rolw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem rolw_sextw_left (r2 r1 : Reg) : rolw (sextw r2) r1 = rolw r2 r1 := by
  simp only [rolw, sextw, addiw, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem rolw_sextw_right (r2 r1 : Reg) : rolw r2 (sextw r1) = rolw r2 r1 := by
  simp only [rolw, sextw, addiw]
  bv_decide

@[veir_bv_normalize]
theorem rorw_zextw_left (r2 r1 : Reg) : rorw (zextw r2) r1 = rorw r2 r1 := by
  simp [rorw, zextw, adduw, li]

@[veir_bv_normalize]
theorem rorw_zextw_right (r2 r1 : Reg) : rorw r2 (zextw r1) = rorw r2 r1 := by
  simp only [rorw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem rorw_sextw_left (r2 r1 : Reg) : rorw (sextw r2) r1 = rorw r2 r1 := by
  simp only [rorw, sextw, addiw, Reg.mk.injEq]
  bv_decide

@[veir_bv_normalize]
theorem rorw_sextw_right (r2 r1 : Reg) : rorw r2 (sextw r1) = rorw r2 r1 := by
  simp only [rorw, sextw, addiw]
  bv_decide

@[veir_bv_normalize]
theorem addiw_zextw (imm : BitVec 12) (r : Reg) : addiw imm (zextw r) = addiw imm r := by
  simp only [addiw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem addiw_sextw (imm : BitVec 12) (r : Reg) : addiw imm (sextw r) = addiw imm r := by
  simp only [addiw, sextw]
  grind

@[veir_bv_normalize]
theorem roriw_zextw (shamt : BitVec 5) (r : Reg) : roriw shamt (zextw r) = roriw shamt r := by
  simp only [roriw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem roriw_sextw (shamt : BitVec 5) (r : Reg) : roriw shamt (sextw r) = roriw shamt r := by
  simp only [roriw, sextw, addiw]
  bv_decide

@[veir_bv_normalize]
theorem srliw_zextw (shamt : BitVec 5) (r : Reg) : srliw shamt (zextw r) = srliw shamt r := by
  simp [srliw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem srliw_sextw (shamt : BitVec 5) (r : Reg) : srliw shamt (sextw r) = srliw shamt r := by
  simp only [srliw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem sraiw_zextw (shamt : BitVec 5) (r : Reg) : sraiw shamt (zextw r) = sraiw shamt r := by
  simp [sraiw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem sraiw_sextw (shamt : BitVec 5) (r : Reg) : sraiw shamt (sextw r) = sraiw shamt r := by
  simp only [sraiw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem slliuw_zextw (shamt : BitVec 6) (r : Reg) :
    slliuw shamt (zextw r) = slliuw shamt r := by
  simp [slliuw, zextw, adduw, li]
  grind

@[veir_bv_normalize]
theorem slliuw_sextw (shamt : BitVec 6) (r : Reg) :
    slliuw shamt (sextw r) = slliuw shamt r := by
  simp only [slliuw, sextw, addiw]
  grind

@[veir_bv_normalize]
theorem clzw_zextw (r : Reg) : clzw (zextw r) = clzw r := by
  simp only [clzw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem clzw_sextw (r : Reg) : clzw (sextw r) = clzw r := by
  simp only [clzw, sextw, addiw]
  bv_decide

@[veir_bv_normalize]
theorem ctzw_zextw (r : Reg) : ctzw (zextw r) = ctzw r := by
  simp only [ctzw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem ctzw_sextw (r : Reg) : ctzw (sextw r) = ctzw r := by
  simp only [ctzw, sextw, addiw]
  bv_decide

@[veir_bv_normalize]
theorem cpopw_zextw (r : Reg) : cpopw (zextw r) = cpopw r := by
  simp only [cpopw, zextw, adduw, li]
  bv_decide

@[veir_bv_normalize]
theorem cpopw_sextw (r : Reg) : cpopw (sextw r) = cpopw r := by
  simp only [cpopw, sextw, addiw]
  bv_decide
