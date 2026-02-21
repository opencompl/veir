module

/-
# Operation Codes

This file defines the `OpCode` inductive type, which represents the set of registered
operation codes in the Veir intermediate representation (IR). Each `OpCode` corresponds
to an operation definition.
-/

import Std.Data.HashMap
public import Veir.TC
import Veir.Meta.OpCode

open Std

namespace Veir

public section

@[opcodes]
inductive Arith where
| constant
| addi
| subi
| muli
| andi
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Builtin where
| unregistered
| module
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Func where
| func
| return
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Llvm where
| constant
| and
| or
| xor
| add
| sub
| shl
| lshr
| ashr
| mul
| sdiv
| udiv
| srem
| urem
| icmp
| select
| trunc
| sext
| zext
| return
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Riscv where
| li
| lui
| auipc
| addi
| slti
| sltiu
| andi
| ori
| xori
| addiw
| slli
| srli
| srai
| add
| sub
| sll
| slt
| sltu
| xor
| srl
| sra
| or
| and
| slliw
| srliw
| sraiw
| addw
| subw
| sllw
| srlw
| sraw
| rem
| remu
| remw
| remuw
| mul
| mulh
| mulhu
| mulhsu
| mulw
| div
| divw
| divu
| divuw
| adduw
| sh1adduw
| sh2adduw
| sh3adduw
| sh1add
| sh2add
| sh3add
| slliuw
| andn
| orn
| xnor
| max
| maxu
| min
| minu
| rol
| ror
| rolw
| rorw
| sextb
| sexth
| zexth
| clz
| clzw
| ctz
| ctzw
| roriw
| rori
| bclr
| bext
| binv
| bset
| bclri
| bexti
| binvi
| bseti
| pack
| packh
| packw
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Test where
| test
deriving Inhabited, Repr, Hashable, DecidableEq


/-
A type class that defines an MLIR dialect and translates from `DialectCode` to
the dialect type.
-/
/-
  An operation code (OpCode) identifies the type of an operation.
  Each OpCode corresponds to a specific operation.
-/
#generate_op_codes

def test : OpCode := .arith Veir.Arith.constant

def toType (code : DialectCode) : Type :=
  match code with
  | .arith => Arith
  | .builtin => Builtin
  | .func => Func
  | .llvm => Llvm
  | .riscv => Riscv
  | .test => Test

/-
Adapt `toType` to have a return value that is Hashable.
-/


theorem DialectCode.fromByteArray_toByteArray (d : DialectCode) :
    DialectCode.fromByteArray (DialectCode.toByteArray d) = d := by
  simp [DialectCode.toByteArray, DialectCode.fromByteArray]
  cases d <;> simp[String.toByteArray_inj]

theorem DialectCode.fromName_toByteArray (d : DialectCode) :
    DialectCode.fromName (DialectCode.toName d) = d := by
  simp [DialectCode.toName, DialectCode.fromName]
  cases d <;> simp

end
end Veir
