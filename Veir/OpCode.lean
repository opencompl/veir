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
  | arith_constant
  | arith_addi
  | arith_subi
  | arith_muli
  | arith_andi
  | builtin_unregistered
  | builtin_module
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
  | llvm_select
  | llvm_trunc
  | llvm_sext
  | llvm_zext
  | test_test
deriving Inhabited, Repr, Hashable, DecidableEq

/--
  Convert an operation name to its corresponding OpCode.
-/
def OpCode.fromName (name : ByteArray) : OpCode :=
  if name = "builtin.module".toByteArray then builtin_module
  else if name = "arith.constant".toByteArray then arith_constant
  else if name = "arith.addi".toByteArray then arith_addi
  else if name = "arith.subi".toByteArray then arith_subi
  else if name = "arith.muli".toByteArray then arith_muli
  else if name = "arith.andi".toByteArray then arith_andi
  else if name = "test.test".toByteArray then test_test
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
  else if name = "llvm.select".toByteArray then llvm_select
  else if name = "llvm.trunc".toByteArray then llvm_trunc
  else if name = "llvm.sext".toByteArray then llvm_sext
  else if name = "llvm.zext".toByteArray then llvm_zext
  else builtin_unregistered

/--
  Get the name of an operation as displayed in the IR textual format.
-/
def OpCode.name (opcode : OpCode) : ByteArray :=
  match opcode with
  | builtin_module => "builtin.module".toByteArray
  | arith_constant => "arith.constant".toByteArray
  | arith_addi     => "arith.addi".toByteArray
  | arith_subi     => "arith.subi".toByteArray
  | arith_muli     => "arith.muli".toByteArray
  | arith_andi     => "arith.andi".toByteArray
  | test_test      => "test.test".toByteArray
  | builtin_unregistered   => "unregistered".toByteArray
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
  | llvm_select    => "llvm.select".toByteArray
  | llvm_trunc     => "llvm.trunc".toByteArray
  | llvm_sext      => "llvm.sext".toByteArray
  | llvm_zext      => "llvm.zext".toByteArray

end
end Veir
