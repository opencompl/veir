module

/-
# Operation Codes

This file defines the `OpCode` inductive type, which represents the set of registered
operation codes in the Veir intermediate representation (IR). Each `OpCode` corresponds
to an operation definition.
-/

import Std.Data.HashMap

open Std

namespace Veir

public section

/--
  An operation code (OpCode) identifies the type of an operation.
  Each OpCode corresponds to a specific operation.
-/
inductive OpCode
  /- ARITH -/
  | arith_constant
  | arith_addi
  | arith_subi
  | arith_muli
  | arith_andi
  /- FUNC -/
  | func_func
  | func_return
  | builtin_unregistered
  | builtin_module
  /- LLVM -/
  | llvm_constant
  | llvm_and
  | llvm_or
  | llvm_xor
  | llvm_add
  | llvm_sub
  | llvm_shl
  | llvm_lshr
  | llvm_ashr
  | llvm_mul
  | llvm_sdiv
  | llvm_udiv
  | llvm_srem
  | llvm_urem
  | llvm_icmp
  | llvm_select
  | llvm_trunc
  | llvm_sext
  | llvm_zext
  | llvm_return
  /- RISCV -/
  | riscv_li
  | riscv_lui
  | riscv_auipc
  | riscv_addi
  | riscv_slti
  | riscv_sltiu
  | riscv_andi
  | riscv_ori
  | riscv_xori
  | riscv_addiw
  | riscv_slli
  | riscv_srli
  | riscv_srai
  | riscv_add
  | riscv_sub
  | riscv_sll
  | riscv_slt
  | riscv_sltu
  | riscv_xor
  | riscv_srl
  | riscv_sra
  | riscv_or
  | riscv_and
  | riscv_slliw
  | riscv_srliw
  | riscv_sraiw
  | riscv_addw
  | riscv_subw
  | riscv_sllw
  | riscv_srlw
  | riscv_sraw
  | riscv_rem
  | riscv_remu
  | riscv_remw
  | riscv_remuw
  | riscv_mul
  | riscv_mulh
  | riscv_mulhu
  | riscv_mulhsu
  | riscv_mulw
  | riscv_div
  | riscv_divw
  | riscv_divu
  | riscv_divuw
  | riscv_adduw
  | riscv_sh1adduw
  | riscv_sh2adduw
  | riscv_sh3adduw
  | riscv_sh1add
  | riscv_sh2add
  | riscv_sh3add
  | riscv_slliuw
  | riscv_andn
  | riscv_orn
  | riscv_xnor
  | riscv_max
  | riscv_maxu
  | riscv_min
  | riscv_minu
  | riscv_rol
  | riscv_ror
  | riscv_rolw
  | riscv_rorw
  | riscv_sextb
  | riscv_sexth
  | riscv_zexth
  | riscv_clz
  | riscv_clzw
  | riscv_ctz
  | riscv_ctzw
  | riscv_roriw
  | riscv_rori
  | riscv_bclr
  | riscv_bext
  | riscv_binv
  | riscv_bset
  | riscv_bclri
  | riscv_bexti
  | riscv_binvi
  | riscv_bseti
  | riscv_pack
  | riscv_packh
  | riscv_packw
  /- TEST -/
  | test_test
deriving Inhabited, Repr, Hashable, DecidableEq

/--
  Convert an operation name to its corresponding OpCode.
-/
def OpCode.fromName (name : ByteArray) : OpCode :=
  if name = "builtin.module".toByteArray then builtin_module
  /- ARITH -/
  else if name = "arith.constant".toByteArray then arith_constant
  else if name = "arith.addi".toByteArray then arith_addi
  else if name = "arith.subi".toByteArray then arith_subi
  else if name = "arith.muli".toByteArray then arith_muli
  else if name = "arith.andi".toByteArray then arith_andi
  /- FUNC -/
  else if name = "func.func".toByteArray then func_func
  else if name = "func.return".toByteArray then func_return
  /- TEST -/
  else if name = "test.test".toByteArray then test_test
  /- LLVM -/
  else if name = "llvm.constant".toByteArray then llvm_constant
  else if name = "llvm.and".toByteArray then llvm_and
  else if name = "llvm.or".toByteArray then llvm_or
  else if name = "llvm.xor".toByteArray then llvm_xor
  else if name = "llvm.add".toByteArray then llvm_add
  else if name = "llvm.sub".toByteArray then llvm_sub
  else if name = "llvm.shl".toByteArray then llvm_shl
  else if name = "llvm.lshr".toByteArray then llvm_lshr
  else if name = "llvm.ashr".toByteArray then llvm_ashr
  else if name = "llvm.mul".toByteArray then llvm_mul
  else if name = "llvm.sdiv".toByteArray then llvm_sdiv
  else if name = "llvm.udiv".toByteArray then llvm_udiv
  else if name = "llvm.srem".toByteArray then llvm_srem
  else if name = "llvm.urem".toByteArray then llvm_urem
  else if name = "llvm.icmp".toByteArray then llvm_icmp
  else if name = "llvm.select".toByteArray then llvm_select
  else if name = "llvm.trunc".toByteArray then llvm_trunc
  else if name = "llvm.sext".toByteArray then llvm_sext
  else if name = "llvm.zext".toByteArray then llvm_zext
  else if name = "llvm.return".toByteArray then llvm_return
  /- RISCV -/
  else if name = "riscv.li".toByteArray then riscv_li
  else if name = "riscv.lui".toByteArray then riscv_lui
  else if name = "riscv.auipc".toByteArray then riscv_auipc
  else if name = "riscv.addi".toByteArray then riscv_addi
  else if name = "riscv.slti".toByteArray then riscv_slti
  else if name = "riscv.sltiu".toByteArray then riscv_sltiu
  else if name = "riscv.andi".toByteArray then riscv_andi
  else if name = "riscv.ori".toByteArray then riscv_ori
  else if name = "riscv.xori".toByteArray then riscv_xori
  else if name = "riscv.addiw".toByteArray then riscv_addiw
  else if name = "riscv.slli".toByteArray then riscv_slli
  else if name = "riscv.srli".toByteArray then riscv_srli
  else if name = "riscv.srai".toByteArray then riscv_srai
  else if name = "riscv.add".toByteArray then riscv_add
  else if name = "riscv.sub".toByteArray then riscv_sub
  else if name = "riscv.sll".toByteArray then riscv_sll
  else if name = "riscv.slt".toByteArray then riscv_slt
  else if name = "riscv.sltu".toByteArray then riscv_sltu
  else if name = "riscv.xor".toByteArray then riscv_xor
  else if name = "riscv.srl".toByteArray then riscv_srl
  else if name = "riscv.sra".toByteArray then riscv_sra
  else if name = "riscv.or".toByteArray then riscv_or
  else if name = "riscv.and".toByteArray then riscv_and
  else if name = "riscv.slliw".toByteArray then riscv_slliw
  else if name = "riscv.srliw".toByteArray then riscv_srliw
  else if name = "riscv.sraiw".toByteArray then riscv_sraiw
  else if name = "riscv.addw".toByteArray then riscv_addw
  else if name = "riscv.subw".toByteArray then riscv_subw
  else if name = "riscv.sllw".toByteArray then riscv_sllw
  else if name = "riscv.srlw".toByteArray then riscv_srlw
  else if name = "riscv.sraw".toByteArray then riscv_sraw
  else if name = "riscv.rem".toByteArray then riscv_rem
  else if name = "riscv.remu".toByteArray then riscv_remu
  else if name = "riscv.remw".toByteArray then riscv_remw
  else if name = "riscv.remuw".toByteArray then riscv_remuw
  else if name = "riscv.mul".toByteArray then riscv_mul
  else if name = "riscv.mulh".toByteArray then riscv_mulh
  else if name = "riscv.mulhu".toByteArray then riscv_mulhu
  else if name = "riscv.mulhsu".toByteArray then riscv_mulhsu
  else if name = "riscv.mulw".toByteArray then riscv_mulw
  else if name = "riscv.div".toByteArray then riscv_div
  else if name = "riscv.divw".toByteArray then riscv_divw
  else if name = "riscv.divu".toByteArray then riscv_divu
  else if name = "riscv.divuw".toByteArray then riscv_divuw
  else if name = "riscv.adduw".toByteArray then riscv_adduw
  else if name = "riscv.sh1adduw".toByteArray then riscv_sh1adduw
  else if name = "riscv.sh2adduw".toByteArray then riscv_sh2adduw
  else if name = "riscv.sh3adduw".toByteArray then riscv_sh3adduw
  else if name = "riscv.sh1add".toByteArray then riscv_sh1add
  else if name = "riscv.sh2add".toByteArray then riscv_sh2add
  else if name = "riscv.sh3add".toByteArray then riscv_sh3add
  else if name = "riscv.slliuw".toByteArray then riscv_slliuw
  else if name = "riscv.andn".toByteArray then riscv_andn
  else if name = "riscv.orn".toByteArray then riscv_orn
  else if name = "riscv.xnor".toByteArray then riscv_xnor
  else if name = "riscv.max".toByteArray then riscv_max
  else if name = "riscv.maxu".toByteArray then riscv_maxu
  else if name = "riscv.min".toByteArray then riscv_min
  else if name = "riscv.minu".toByteArray then riscv_minu
  else if name = "riscv.rol".toByteArray then riscv_rol
  else if name = "riscv.ror".toByteArray then riscv_ror
  else if name = "riscv.rolw".toByteArray then riscv_rolw
  else if name = "riscv.rorw".toByteArray then riscv_rorw
  else if name = "riscv.sextb".toByteArray then riscv_sextb
  else if name = "riscv.sexth".toByteArray then riscv_sexth
  else if name = "riscv.zexth".toByteArray then riscv_zexth
  else if name = "riscv.clz".toByteArray then riscv_clz
  else if name = "riscv.clzw".toByteArray then riscv_clzw
  else if name = "riscv.ctz".toByteArray then riscv_ctz
  else if name = "riscv.ctzw".toByteArray then riscv_ctzw
  else if name = "riscv.roriw".toByteArray then riscv_roriw
  else if name = "riscv.rori".toByteArray then riscv_rori
  else if name = "riscv.bclr".toByteArray then riscv_bclr
  else if name = "riscv.bext".toByteArray then riscv_bext
  else if name = "riscv.binv".toByteArray then riscv_binv
  else if name = "riscv.bset".toByteArray then riscv_bset
  else if name = "riscv.bclri".toByteArray then riscv_bclri
  else if name = "riscv.bexti".toByteArray then riscv_bexti
  else if name = "riscv.binvi".toByteArray then riscv_binvi
  else if name = "riscv.bseti".toByteArray then riscv_bseti
  else if name = "riscv.pack".toByteArray then riscv_pack
  else if name = "riscv.packh".toByteArray then riscv_packh
  else if name = "riscv.packw".toByteArray then riscv_packw
  else builtin_unregistered

/--
  Get the name of an operation as displayed in the IR textual format.
-/
def OpCode.name (opcode : OpCode) : ByteArray :=
  match opcode with
  | builtin_module => "builtin.module".toByteArray
  /- ARITH -/
  | arith_constant => "arith.constant".toByteArray
  | arith_addi     => "arith.addi".toByteArray
  | arith_subi     => "arith.subi".toByteArray
  | arith_muli     => "arith.muli".toByteArray
  | arith_andi     => "arith.andi".toByteArray
  /- FUNC -/
  | func_func      => "func.func".toByteArray
  | func_return    => "func.return".toByteArray
  /- TEST -/
  | test_test      => "test.test".toByteArray
  | builtin_unregistered   => "unregistered".toByteArray
  /- LLVM -/
  | llvm_constant  => "llvm.constant".toByteArray
  | llvm_and       => "llvm.and".toByteArray
  | llvm_or        => "llvm.or".toByteArray
  | llvm_xor       => "llvm.xor".toByteArray
  | llvm_add       => "llvm.add".toByteArray
  | llvm_sub       => "llvm.sub".toByteArray
  | llvm_shl       => "llvm.shl".toByteArray
  | llvm_lshr      => "llvm.lshr".toByteArray
  | llvm_ashr      => "llvm.ashr".toByteArray
  | llvm_mul       => "llvm.mul".toByteArray
  | llvm_sdiv      => "llvm.sdiv".toByteArray
  | llvm_udiv      => "llvm.udiv".toByteArray
  | llvm_srem      => "llvm.srem".toByteArray
  | llvm_urem      => "llvm.urem".toByteArray
  | llvm_icmp      => "llvm.icmp".toByteArray
  | llvm_select    => "llvm.select".toByteArray
  | llvm_trunc     => "llvm.trunc".toByteArray
  | llvm_sext      => "llvm.sext".toByteArray
  | llvm_zext      => "llvm.zext".toByteArray
  | llvm_return    => "llvm.return".toByteArray
  /- RISCV -/
  | riscv_li      => "riscv.li".toByteArray
  | riscv_lui      => "riscv.lui".toByteArray
  | riscv_auipc    => "riscv.auipc".toByteArray
  | riscv_addi     => "riscv.addi".toByteArray
  | riscv_slti     => "riscv.slti".toByteArray
  | riscv_sltiu    => "riscv.sltiu".toByteArray
  | riscv_andi     => "riscv.andi".toByteArray
  | riscv_ori      => "riscv.ori".toByteArray
  | riscv_xori     => "riscv.xori".toByteArray
  | riscv_addiw    => "riscv.addiw".toByteArray
  | riscv_slli     => "riscv.slli".toByteArray
  | riscv_srli     => "riscv.srli".toByteArray
  | riscv_srai     => "riscv.srai".toByteArray
  | riscv_add      => "riscv.add".toByteArray
  | riscv_sub      => "riscv.sub".toByteArray
  | riscv_sll      => "riscv.sll".toByteArray
  | riscv_slt      => "riscv.slt".toByteArray
  | riscv_sltu     => "riscv.sltu".toByteArray
  | riscv_xor      => "riscv.xor".toByteArray
  | riscv_srl      => "riscv.srl".toByteArray
  | riscv_sra      => "riscv.sra".toByteArray
  | riscv_or       => "riscv.or".toByteArray
  | riscv_and      => "riscv.and".toByteArray
  | riscv_slliw    => "riscv.slliw".toByteArray
  | riscv_srliw    => "riscv.srliw".toByteArray
  | riscv_sraiw    => "riscv.sraiw".toByteArray
  | riscv_addw     => "riscv.addw".toByteArray
  | riscv_subw     => "riscv.subw".toByteArray
  | riscv_sllw     => "riscv.sllw".toByteArray
  | riscv_srlw     => "riscv.srlw".toByteArray
  | riscv_sraw     => "riscv.sraw".toByteArray
  | riscv_rem      => "riscv.rem".toByteArray
  | riscv_remu     => "riscv.remu".toByteArray
  | riscv_remw     => "riscv.remw".toByteArray
  | riscv_remuw    => "riscv.remuw".toByteArray
  | riscv_mul      => "riscv.mul".toByteArray
  | riscv_mulh     => "riscv.mulh".toByteArray
  | riscv_mulhu    => "riscv.mulhu".toByteArray
  | riscv_mulhsu   => "riscv.mulhsu".toByteArray
  | riscv_mulw     => "riscv.mulw".toByteArray
  | riscv_div      => "riscv.div".toByteArray
  | riscv_divw     => "riscv.divw".toByteArray
  | riscv_divu     => "riscv.divu".toByteArray
  | riscv_divuw    => "riscv.divuw".toByteArray
  | riscv_adduw    => "riscv.adduw".toByteArray
  | riscv_sh1adduw => "riscv.sh1adduw".toByteArray
  | riscv_sh2adduw => "riscv.sh2adduw".toByteArray
  | riscv_sh3adduw => "riscv.sh3adduw".toByteArray
  | riscv_sh1add   => "riscv.sh1add".toByteArray
  | riscv_sh2add   => "riscv.sh2add".toByteArray
  | riscv_sh3add   => "riscv.sh3add".toByteArray
  | riscv_slliuw   => "riscv.slliuw".toByteArray
  | riscv_andn     => "riscv.andn".toByteArray
  | riscv_orn      => "riscv.orn".toByteArray
  | riscv_xnor     => "riscv.xnor".toByteArray
  | riscv_max      => "riscv.max".toByteArray
  | riscv_maxu     => "riscv.maxu".toByteArray
  | riscv_min      => "riscv.min".toByteArray
  | riscv_minu     => "riscv.minu".toByteArray
  | riscv_rol      => "riscv.rol".toByteArray
  | riscv_ror      => "riscv.ror".toByteArray
  | riscv_rolw     => "riscv.rolw".toByteArray
  | riscv_rorw     => "riscv.rorw".toByteArray
  | riscv_sextb    => "riscv.sextb".toByteArray
  | riscv_sexth    => "riscv.sexth".toByteArray
  | riscv_zexth    => "riscv.zexth".toByteArray
  | riscv_clz      => "riscv.clz".toByteArray
  | riscv_clzw     => "riscv.clzw".toByteArray
  | riscv_ctz      => "riscv.ctz".toByteArray
  | riscv_ctzw     => "riscv.ctzw".toByteArray
  | riscv_roriw    => "riscv.roriw".toByteArray
  | riscv_rori     => "riscv.rori".toByteArray
  | riscv_bclr     => "riscv.bclr".toByteArray
  | riscv_bext     => "riscv.bext".toByteArray
  | riscv_binv     => "riscv.binv".toByteArray
  | riscv_bset     => "riscv.bset".toByteArray
  | riscv_bclri    => "riscv.bclri".toByteArray
  | riscv_bexti    => "riscv.bexti".toByteArray
  | riscv_binvi    => "riscv.binvi".toByteArray
  | riscv_bseti    => "riscv.bseti".toByteArray
  | riscv_pack     => "riscv.pack".toByteArray
  | riscv_packh    => "riscv.packh".toByteArray
  | riscv_packw    => "riscv.packw".toByteArray
end
end Veir
