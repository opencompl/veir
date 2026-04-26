module

public import  Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Basic

public section

namespace Veir.Data.RISCV

theorem Reg.val.inj : {x y : Reg} → x.val = y.val → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

@[reg_toBitVec]
theorem val_inj (r1 r2 : Reg) :
    r1 = r2 ↔ r1.val = r2.val := ⟨(· ▸ rfl), Reg.val.inj⟩

@[reg_toBitVec]
theorem val_li : (li imm).val = imm := (rfl)

@[reg_toBitVec]
theorem val_lui : (lui imm).val = (imm ++ 0#12).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_auipc :
  (auipc imm pc).val = ((imm ++ 0#12).signExtend 64) + pc.val := (rfl)

@[reg_toBitVec]
theorem val_addi :
  (addi imm r).val = r.val + imm.signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_slti :
  (slti imm r).val = (BitVec.ofBool (r.val.slt (imm.signExtend 64))).zeroExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_sltiu :
  (sltiu imm r).val = (BitVec.ofBool (r.val.ult (imm.signExtend 64))).zeroExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_andi :
  (andi imm r).val = r.val.and (imm.signExtend 64) := (rfl)

@[reg_toBitVec]
theorem val_ori :
  (ori imm r).val = r.val.or (imm.signExtend 64) := (rfl)

@[reg_toBitVec]
theorem val_xori :
  (xori imm r).val = r.val.xor (imm.signExtend 64) := (rfl)

@[reg_toBitVec]
theorem val_addiw :
  (addiw imm r).val = (((imm.signExtend 64) + r.val).setWidth 32).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_slli :
  (slli shamt r).val = r.val <<< shamt := (rfl)

@[reg_toBitVec]
theorem val_srli :
  (srli shamt r).val = r.val >>> shamt := (rfl)

@[reg_toBitVec]
theorem val_srai :
  (srai shamt r).val = (r.val.sshiftRight' shamt).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_add :
  (add r2 r1).val = r1.val + r2.val := (rfl)

@[reg_toBitVec]
theorem val_sub :
  (sub r2 r1).val = r1.val - r2.val := (rfl)

@[reg_toBitVec]
theorem val_sll :
  (sll r2 r1).val = r1.val <<< (r2.val.extractLsb 5 0) := (rfl)

@[reg_toBitVec]
theorem val_slt :
  (slt r2 r1).val = (BitVec.ofBool (r1.val.slt r2.val)).setWidth 64 := (rfl)

@[reg_toBitVec]
theorem val_sltu :
  (sltu r2 r1).val = (BitVec.ofBool (r1.val.ult r2.val)).setWidth 64 := (rfl)

@[reg_toBitVec]
theorem val_xor :
  (xor r2 r1).val = r1.val.xor r2.val := (rfl)

@[reg_toBitVec]
theorem val_srl :
  (srl r2 r1).val = r1.val >>> (r2.val.extractLsb 5 0) := (rfl)

@[reg_toBitVec]
theorem val_sra :
  (sra r2 r1).val = r1.val.sshiftRight' (r2.val.extractLsb 5 0) := (rfl)

@[reg_toBitVec]
theorem val_or :
  (or r2 r1).val = r1.val.or r2.val := (rfl)

@[reg_toBitVec]
theorem val_and :
  (and r2 r1).val = r1.val.and r2.val := (rfl)

@[reg_toBitVec]
theorem val_slliw :
  (slliw shamt r).val = ((r.val.extractLsb' 0 32) <<< shamt).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_srliw :
  (srliw shamt r).val = ((r.val.extractLsb' 0 32) >>> shamt).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_sraiw :
  (sraiw shamt r).val = ((r.val.extractLsb' 0 32).sshiftRight' shamt).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_addw :
  (addw r2 r1).val = ((r1.val.extractLsb' 0 32) + (r2.val.extractLsb' 0 32)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_subw :
  (subw r2 r1).val = ((r1.val.extractLsb' 0 32) - (r2.val.extractLsb' 0 32)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_sllw :
  (sllw r2 r1).val = ((r1.val.extractLsb' 0 32) <<< ((r2.val.extractLsb' 0 32).extractLsb' 0 5)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_srlw :
  (srlw r2 r1).val =
    ((r1.val.extractLsb' 0 32) >>> ((r2.val.extractLsb' 0 32).extractLsb' 0 5)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_sraw :
  (sraw r2 r1).val =
    ((r1.val.extractLsb 31 0).sshiftRight' (r2.val.extractLsb 4 0)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_rem : (rem r2 r1).val = r1.val.srem r2.val := (rfl)

@[reg_toBitVec]
theorem val_remu : (remu r2 r1).val = r1.val.umod r2.val := (rfl)

@[reg_toBitVec]
theorem val_remw :
  (remw r2 r1).val =
    ((r1.val.extractLsb 31 0).srem (r2.val.extractLsb 31 0)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_remuw :
  (remuw r2 r1).val =
    ((r1.val.extractLsb 31 0).umod (r2.val.extractLsb 31 0)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_mul : (mul r2 r1).val = r2.val * r1.val := (rfl)

@[reg_toBitVec]
theorem val_mulh :
  (mulh r2 r1).val = (r1.val.signExtend 129 * r2.val.signExtend 129).extractLsb 127 64 := (rfl)

@[reg_toBitVec]
theorem val_mulhu :
  (mulhu r2 r1).val =
    ((r1.val.zeroExtend 128 * r2.val.zeroExtend 128).extractLsb' 0 128).extractLsb 127 64 := (rfl)

@[reg_toBitVec]
theorem val_mulhsu :
  (mulhsu r2 r1).val = (r1.val.signExtend 129 * r2.val.zeroExtend 129).extractLsb 127 64 := (rfl)

@[reg_toBitVec]
theorem val_mulw :
  (mulw r2 r1).val =
    ((r1.val.extractLsb 31 0).extractLsb 31 0 * (r2.val.extractLsb 31 0).extractLsb 31 0).signExtend 64 :=
  (rfl)

@[reg_toBitVec]
theorem val_div :
  (div r2 r1).val = if r2.val = 0#64 then -1#64 else r1.val.sdiv r2.val := by
  simp [div]
  split <;>  (rfl)

@[reg_toBitVec]
theorem val_divw :
  (divw r2 r1).val =
    (if r2.val.extractLsb 31 0 = 0#32
     then -1#32
     else (r1.val.extractLsb 31 0).sdiv (r2.val.extractLsb 31 0)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_divu :
  (divu r2 r1).val = if r2.val = 0#64 then (-1 : BitVec 64) else r1.val.udiv r2.val := by
  simp [divu]
  split <;>  (rfl)

@[reg_toBitVec]
theorem val_divuw :
  (divuw r2 r1).val =
    (if r2.val.extractLsb 31 0 = 0#32
     then -1#32
     else (r1.val.extractLsb 31 0).udiv (r2.val.extractLsb 31 0)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_adduw :
  (adduw r2 r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< 0#2 + r2.val := (rfl)

@[reg_toBitVec]
theorem val_sh1adduw :
  (sh1adduw r2 r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< 1#2 + r2.val := (rfl)

@[reg_toBitVec]
theorem val_sh2adduw :
  (sh2adduw r2 r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< 2#2 + r2.val := (rfl)

@[reg_toBitVec]
theorem val_sh3adduw :
  (sh3adduw r2 r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< 3#2 + r2.val := (rfl)

@[reg_toBitVec]
theorem val_sh1add : (sh1add r2 r1).val = r1.val <<< 1#2 + r2.val := (rfl)

@[reg_toBitVec]
theorem val_sh2add : (sh2add r2 r1).val = r1.val <<< 2#2 + r2.val := (rfl)

@[reg_toBitVec]
theorem val_sh3add : (sh3add r2 r1).val = r1.val <<< 3#2 + r2.val := (rfl)

@[reg_toBitVec]
theorem val_slliuw :
  (slliuw shamt r1).val = (r1.val.extractLsb 31 0).zeroExtend 64 <<< shamt := (rfl)

@[reg_toBitVec]
theorem val_andn : (andn r2 r1).val = r1.val &&& ~~~r2.val := (rfl)

@[reg_toBitVec]
theorem val_orn : (orn r2 r1).val = r1.val ||| ~~~r2.val := (rfl)

@[reg_toBitVec]
theorem val_xnor : (xnor r2 r1).val = ~~~ (r1.val ^^^ r2.val) := (rfl)

@[reg_toBitVec]
theorem val_max :
  (max r2 r1).val = (if r2.val.slt r1.val then r1.val else r2.val).extractLsb' 0 64 := (rfl)

@[reg_toBitVec]
theorem val_maxu :
  (maxu r2 r1).val = (if r2.val.ult r1.val then r1.val else r2.val).extractLsb' 0 64 := (rfl)

@[reg_toBitVec]
theorem val_min :
  (min r2 r1).val = (if r1.val.slt r2.val then r1.val else r2.val).extractLsb' 0 64 := (rfl)

@[reg_toBitVec]
theorem val_minu :
  (minu r2 r1).val = (if r1.val.ult r2.val then r1.val else r2.val).extractLsb' 0 64 := (rfl)

@[reg_toBitVec]
theorem val_rol :
  (rol r2 r1).val =  (r1.val <<< (r2.val.extractLsb 5 0)) ||| (r1.val >>> (64#6 - (r2.val.extractLsb 5 0))) :=
  (rfl)

@[reg_toBitVec]
theorem val_ror :
  (ror r2 r1).val =
    (r1.val >>> (r2.val.extractLsb 5 0)) ||| (r1.val <<< (64#6 - (r2.val.extractLsb 5 0))) := (rfl)

@[reg_toBitVec]
theorem val_rolw :
  (rolw r2 r1).val =
    ((r1.val.extractLsb 31 0 <<< (r2.val.extractLsb 4 0)) ||| (r1.val.extractLsb 31 0 >>> (32#5 - (r2.val.extractLsb 4 0)))).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_rorw :
  (rorw r2 r1).val =
    ((r1.val.extractLsb 31 0 >>> (r2.val.extractLsb 4 0)) ||| (r1.val.extractLsb 31 0 <<< (32#5 - (r2.val.extractLsb 4 0)))).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_sextb : (sextb r1).val = (r1.val.extractLsb 7 0).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_sexth : (sexth r1).val = (r1.val.extractLsb 15 0).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_zexth : (zexth r1).val = (r1.val.extractLsb 15 0).zeroExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_clz : (clz r1).val = r1.val.clz := (rfl)

@[reg_toBitVec]
theorem val_clzw :
  (clzw r1).val = (r1.val.extractLsb 31 0).clz.zeroExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_ctz : (ctz r1).val = r1.val.ctz := (rfl)

@[reg_toBitVec]
theorem val_ctzw :
  (ctzw r1).val = (r1.val.extractLsb 31 0).ctz.zeroExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_cpop : (cpop r1).val = r1.val.cpop := (rfl)

@[reg_toBitVec]
theorem val_cpopw :
  (cpopw r1).val = (r1.val.extractLsb 31 0).cpop.zeroExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_roriw :
  (roriw shamt r1).val =
    ((r1.val.extractLsb 31 0 >>> shamt) ||| (r1.val.extractLsb 31 0 <<< (32 - shamt))).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_rori :
  (rori shamt r1).val = (r1.val >>> shamt) ||| (r1.val <<< (64 - shamt)) := (rfl)

@[reg_toBitVec]
theorem val_bclr :
  (bclr r2 r1).val =
    r1.val &&& ~~~(((1#1).zeroExtend 64) <<< (r2.val.extractLsb 5 0)) := (rfl)

@[reg_toBitVec]
theorem val_bext :
  (bext r2 r1).val =
      (if r1.val &&& (((1#1).setWidth 64) <<< (r2.val.extractLsb 5 0)) != 0#64
       then 1#1 else 0#1).setWidth 64 := (rfl)

@[reg_toBitVec]
theorem val_binv :
  (binv r2 r1).val =
    r1.val ^^^ (((1#1).zeroExtend 64) <<< (r2.val.extractLsb 5 0)) := (rfl)

@[reg_toBitVec]
theorem val_bset :
  (bset r2 r1).val =
    r1.val ||| (((1#1).zeroExtend 64) <<< (r2.val.extractLsb 5 0)) := (rfl)

@[reg_toBitVec]
theorem val_bclri :
  (bclri shamt r1).val = r1.val &&& ~~~((1#1).setWidth 64 <<< shamt) := (rfl)

@[reg_toBitVec]
theorem val_bexti :
  (bexti shamt r1).val =
      (if r1.val &&& (((1#1).setWidth 64) <<< shamt) != 0#64 then 1#1 else 0#1).setWidth 64 := (rfl)

@[reg_toBitVec]
theorem val_binvi :
  (binvi shamt r1).val = r1.val ^^^ (((1#1).zeroExtend 64) <<< shamt) := (rfl)

@[reg_toBitVec]
theorem val_bseti :
  (bseti shamt r1).val = r1.val ||| (((1#1).zeroExtend 64) <<< shamt) := (rfl)

@[reg_toBitVec]
theorem val_pack :
  (pack r2 r1).val =
    r2.val.extractLsb 31 0 ++ r1.val.extractLsb 31 0 := (rfl)

@[reg_toBitVec]
theorem val_packh :
  (packh r2 r1).val =
    ((r2.val.extractLsb 7 0) ++ (r1.val.extractLsb 7 0)).zeroExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_packw :
  (packw r2 r1).val =
    ((r2.val.extractLsb 15 0) ++ (r1.val.extractLsb 15 0)).signExtend 64 := (rfl)

@[reg_toBitVec]
theorem val_mv : (mv r1).val = (addi 0 r1).val := (rfl)

@[reg_toBitVec]
theorem val_not : (not r1).val = (xori (-1) r1).val := (rfl)

@[reg_toBitVec]
theorem val_neg : (neg r1).val = (sub r1 (li 0)).val := (rfl)

@[reg_toBitVec]
theorem val_negw : (negw r1).val = (subw r1 (li 0)).val := (rfl)

@[reg_toBitVec]
theorem val_sextw : (sextw r1).val = (addiw 0 r1).val := (rfl)

@[reg_toBitVec]
theorem val_zextb : (zextb r1).val = (andi 255 r1).val := (rfl)

@[reg_toBitVec]
theorem val_zextw : (zextw r1).val = (adduw (li 0) r1).val := (rfl)

@[reg_toBitVec]
theorem val_seqz : (seqz r1).val = (sltiu 1 r1).val := (rfl)

@[reg_toBitVec]
theorem val_snez : (snez r1).val = (sltu r1 (li 0)).val := (rfl)

@[reg_toBitVec]
theorem val_sltz : (sltz r1).val = (slt (li 0) r1).val := (rfl)

@[reg_toBitVec]
theorem val_sgtz : (sgtz r1).val = (slt r1 (li 0)).val := (rfl)
