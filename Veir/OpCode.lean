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

public section

@[opcodes]
inductive Arith where
| addi
| addui_extended
| andi
| ceildivsi
| ceildivui
| cmpi
| constant
| divsi
| divui
| extsi
| extui
| floordivsi
| maxsi
| maxui
| minsi
| minui
| muli
| mulsi_extended
| mului_extended
| ori
| remsi
| remui
| select
| shli
| shrsi
| shrui
| subi
| trunci
| xori
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Builtin where
| unregistered
| module
| unrealized_conversion_cast
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Func where
| func
| return
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Cf where
| br
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
| cpop
| cpopw
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
/- pseudooperations -/
| mv
| not
| neg
| negw
| sextw
| zextb
| zextw
| seqz
| snez
| sltz
| sgtz
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Mod_Arith where
| add
| constant
| mul
| sub
deriving Inhabited, Repr, Hashable, DecidableEq

@[opcodes]
inductive Datapath where
| compress
| partial_product
| pos_partial_product
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
set_option maxRecDepth 100000
#generate_op_codes

end
end Veir
