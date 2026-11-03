module

public import Veir.Data.LLVM.Byte.Basic
public import Veir.Data.LLVM.Ptr
public import Veir.Data.RISCV.Reg.Basic
public import Veir.IR.Attribute
public import Veir.IR.Basic

public section

namespace Veir

/--
  The type-erased representation of a value used by interpretation and
  compile-time evaluation.
-/
inductive RuntimeValue where
| int (bitwidth : Nat) (value : Data.LLVM.Int bitwidth)
| byte (bitwidth : Nat) (value : Data.LLVM.Byte bitwidth)
| float (type : FloatType) (value : Data.Float.FloatValue type.format)
| addr (value : Data.LLVM.Ptr)
| reg (value : Data.RISCV.Reg)
/-- A canonical natural-number representative in the field identified by `fieldType`. -/
| felt (fieldType : FeltType) (value : Nat)
deriving Inhabited, BEq, DecidableEq

instance : ToString RuntimeValue where
  toString
    | .int _ val => ToString.toString val
    | .byte _ val => ToString.toString val
    | .float _ val => ToString.toString val
    | .addr val => ToString.toString val
    | .reg val => ToString.toString val
    | .felt fieldType val => s!"{val} : {fieldType}"

/--
  Whether a runtime value is wholly poison. A `byte` is wholly poison when
  every one of its bits is, matching the value that `getPoisonForType`
  constructs.
-/
def RuntimeValue.isPoison : RuntimeValue → Bool
  | .int _ .poison => true
  | .byte width value => value.poison == BitVec.allOnes width
  | .addr .poison => true
  | _ => false

/--
  The wholly-poisoned `RuntimeValue` of type `ty`, for the types that have one.
  Used to materialize a result for an operation whose evaluation triggers UB.
-/
def RuntimeValue.getPoisonForType (ty : TypeAttr) : Option RuntimeValue :=
  match ty.val with
  | .integerType intTy => some (.int intTy.bitwidth .poison)
  | .byteType byteTy => some (.byte byteTy.bitwidth Data.LLVM.Byte.allPoison)
  | .llvmPointerType _ => some (.addr .poison)
  | _ => none

/--
  How the control flow should proceed after interpreting a terminator.
  - `return` indicates that the current block should return with the given values.
  - `branch` indicates that the interpreter should jump to another block
-/
inductive ControlFlowAction where
  | return (vals : Array RuntimeValue)
  | branch (vals : Array RuntimeValue) (dest : BlockPtr)

end Veir
