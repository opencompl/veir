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
  | unregistered
  | arith.constant
  | arith.addi
  | arith.subi
  | arith.muli
  | arith.andi
  | builtin.module
  | test.test
deriving Inhabited, Repr, Hashable, DecidableEq

/--
  Convert an operation name to its corresponding OpCode.
-/
def OpCode.fromName (name : ByteArray) : OpCode :=
  if name = "builtin.module".toByteArray then OpCode.builtin.module
  else if name = "arith.constant".toByteArray then OpCode.arith.constant
  else if name = "arith.addi".toByteArray then OpCode.arith.addi
  else if name = "arith.subi".toByteArray then OpCode.arith.subi
  else if name = "arith.muli".toByteArray then OpCode.arith.muli
  else if name = "arith.andi".toByteArray then OpCode.arith.andi
  else if name = "test.test".toByteArray then OpCode.test.test
  else OpCode.unregistered

/--
  Get the name of an operation as displayed in the IR textual format.
-/
def OpCode.name (opcode : OpCode) : ByteArray :=
  match opcode with
  | OpCode.builtin.module => "builtin.module".toByteArray
  | OpCode.arith.constant => "arith.constant".toByteArray
  | OpCode.arith.addi     => "arith.addi".toByteArray
  | OpCode.arith.subi     => "arith.subi".toByteArray
  | OpCode.arith.muli     => "arith.muli".toByteArray
  | OpCode.arith.andi     => "arith.andi".toByteArray
  | OpCode.test.test      => "test.test".toByteArray
  | OpCode.unregistered   => "unregistered".toByteArray

end
end Veir
