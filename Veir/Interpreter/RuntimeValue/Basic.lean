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
/--
  A ranked tensor: static shape together with elements flattened in row-major
  order. Well-formed values satisfy `elems.size = shape.foldl Nat.mul 1`.
-/
| tensor (shape : Array Nat) (elems : Array RuntimeValue)
deriving Inhabited, BEq

def RuntimeValue.decEq (a b : RuntimeValue) : Decidable (a = b) := by
  cases a <;> cases b
  all_goals simp only [reduceCtorEq, RuntimeValue.int.injEq, RuntimeValue.byte.injEq,
    RuntimeValue.float.injEq, RuntimeValue.addr.injEq, RuntimeValue.reg.injEq,
    RuntimeValue.felt.injEq, RuntimeValue.tensor.injEq]
  case int.int w x w' y | byte.byte w x w' y | float.float w x w' y =>
    by_cases h : w = w'
    · subst w'; simp only [true_and, heq_eq_eq]; infer_instance
    · exact isFalse (by simp [h])
  case tensor.tensor s xs s' ys =>
    by_cases hs : s = s'
    · subst hs
      simp only [true_and]
      exact Array.instDecidabelEq' xs ys (fun x y _ _ => RuntimeValue.decEq x y)
    · exact isFalse (by simp [hs])
  all_goals infer_instance
termination_by a

instance : DecidableEq RuntimeValue := RuntimeValue.decEq

def RuntimeValue.toString : RuntimeValue → String
  | .int _ val => ToString.toString val
  | .byte _ val => ToString.toString val
  | .float _ val => ToString.toString val
  | .addr val => ToString.toString val
  | .reg val => ToString.toString val
  | .felt fieldType val => s!"{val} : {fieldType}"
  | .tensor shape elems =>
    let shapeStr := "x".intercalate (shape.toList.map Nat.repr)
    let elemsStr := ",".intercalate (elems.map RuntimeValue.toString).toList
    s!"tensor<{shapeStr}>[{elemsStr}]"
termination_by v => v

instance : ToString RuntimeValue where
  toString := RuntimeValue.toString

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
