module

/-
# Operation Codes

This file defines the `OpCode` inductive type, which represents the set of registered
operation codes in the Veir intermediate representation (IR). Each `OpCode` corresponds
to an operation definition.
-/

import Std.Data.HashMap
import Veir.Meta.OpCode

open Std

namespace Veir

@[opcodes]
inductive Arith where
| constant
| addi
| subi
| muli
| andi

@[opcodes]
inductive Builtin where
| unregistered
| module

@[opcodes]
inductive Func where
| func
| return

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

@[opcodes]
inductive Test where
| test

public section

/-
  An operation code (OpCode) identifies the type of an operation.
  Each OpCode corresponds to a specific operation.
-/
#generate_op_codes

end
end Veir
