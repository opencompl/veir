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

end
end Veir
