module

public import Veir.Interpreter
public import Veir.Passes.InstructionSelection.RISCV64Branches
public import Veir.Data.Casting

import all Veir.Interpreter.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Passes.InstructionSelection.RISCV64Branches

public section

/-!
# Casting a value to a register and back

The branch lowering passes a value along a branch as a register. The value is
cast to a register in front of the branch and back to its type at the start of
the successor. This file gives the meaning of the two casts and shows that a
value of a type that `fitsRegister` is refined by its round trip.
-/

open Veir.Data

namespace Veir

/-- The register that `builtin.unrealized_conversion_cast` turns a value into. -/
@[expose]
def RuntimeValue.toReg? : RuntimeValue → Option RISCV.Reg
  | .int _ value => some (LLVM.Int.toReg value)
  | .byte _ value => some (LLVM.Byte.toReg value)
  | .addr value => some (LLVM.Int.toReg value.toInt)
  | _ => none

/-- The value of type `type` that `builtin.unrealized_conversion_cast` turns a register into. -/
@[expose]
def RuntimeValue.ofReg? (type : TypeAttr) (reg : RISCV.Reg) : Option RuntimeValue :=
  match type.val with
  | .integerType intType => some (.int intType.bitwidth (RISCV.Reg.toInt reg intType.bitwidth))
  | .byteType byteType => some (.byte byteType.bitwidth (RISCV.Reg.toByte reg byteType.bitwidth))
  | .llvmPointerType _ => some (.addr (.val ⟨reg.val⟩))
  | _ => none

/-- A cast to a register computes `toReg?`. -/
theorem interpretOp'_cast_toReg {value : RuntimeValue} {reg : RISCV.Reg}
    (hReg : value.toReg? = some reg)
    (properties : propertiesOf (OpCode.builtin .unrealized_conversion_cast))
    (successors : Array BlockPtr) (mem : MemoryState) :
    interpretOp' (.builtin .unrealized_conversion_cast) properties #[RegisterType.mk] #[value]
      successors mem = .ok (#[.reg reg], mem, none) := by
  cases value <;> simp_all [RuntimeValue.toReg?, interpretOp']

/-- A cast from a register computes `ofReg?`. -/
theorem interpretOp'_cast_ofReg {type : TypeAttr} {reg : RISCV.Reg} {value : RuntimeValue}
    (hValue : RuntimeValue.ofReg? type reg = some value)
    (properties : propertiesOf (OpCode.builtin .unrealized_conversion_cast))
    (successors : Array BlockPtr) (mem : MemoryState) :
    interpretOp' (.builtin .unrealized_conversion_cast) properties #[type] #[.reg reg]
      successors mem = .ok (#[value], mem, none) := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> simp only [RuntimeValue.ofReg?, Option.some.injEq, reduceCtorEq] at hValue
  all_goals subst hValue; rfl

/--
  A value of a type that fits a register is refined by its round trip through
  one, even when the value that is cast is only a refinement of it.
-/
theorem RuntimeValue.isRefinedBy_ofReg?_toReg? {type : TypeAttr} {source target : RuntimeValue}
    (hFits : fitsRegister type) (hConforms : source.Conforms type) (hRefined : source ⊒ target) :
    ∃ reg value, target.toReg? = some reg ∧ RuntimeValue.ofReg? type reg = some value ∧
      source ⊒ value ∧ value.Conforms type := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> simp only [fitsRegister, Bool.false_eq_true] at hFits
  case integerType intType =>
    obtain ⟨value, rfl⟩ := Conforms.integerType.mp hConforms
    obtain ⟨target, rfl, hRefined⟩ := RuntimeValue.int_of_isRefinedBy hRefined
    refine ⟨_, _, rfl, rfl, ?_, by simp [RuntimeValue.Conforms]⟩
    simp only [RuntimeValue.isRefinedBy, exists_true_left, LLVM.Int.cast_self] at hRefined ⊢
    have hWidth : intType.bitwidth ≤ 64 := by simp at hFits; omega
    rcases value with v | _
    · rcases target with t | _
      · have : v = t := by simpa [isRefinedBy_eq] using hRefined
        subst this
        simp only [LLVM.Int.toReg, RISCV.Reg.toInt, isRefinedBy_eq]
        ext i hi
        have : i < 64 := by omega
        simp [this, BitVec.getLsbD_eq_getElem hi]
      · simp [isRefinedBy_eq] at hRefined
    · simp [isRefinedBy_eq]
  case byteType byteType =>
    obtain ⟨value, rfl⟩ := Conforms.byteType hConforms
    obtain ⟨target, rfl, hRefined⟩ := RuntimeValue.byte_of_isRefinedBy hRefined
    refine ⟨_, _, rfl, rfl, ?_, by simp [RuntimeValue.Conforms]⟩
    have hWidth : byteType.bitwidth ≤ 64 := by simpa using hFits
    simp only [RuntimeValue.isRefinedBy, exists_true_left, LLVM.Byte.cast_self] at hRefined ⊢
    simp only [LLVM.Byte.isRefinedBy, LLVM.Byte.toReg, RISCV.Reg.toByte] at hRefined ⊢
    ext i hi
    have hBit := congrArg (·[i]) hRefined
    have : i < 64 := by omega
    simp [this] at hBit ⊢
    rcases hBit with h | ⟨h, _⟩
    · exact .inl h
    · exact .inr (by simp [h, BitVec.getLsbD_eq_getElem hi])
  case llvmPointerType =>
    cases source <;> simp only [RuntimeValue.Conforms] at hConforms
    case addr value =>
      cases target <;> simp only [RuntimeValue.isRefinedBy] at hRefined
      case addr target =>
        refine ⟨_, _, rfl, rfl, ?_, by simp [RuntimeValue.Conforms]⟩
        simp only [RuntimeValue.isRefinedBy]
        cases value
        case poison => simp [LLVM.Ptr.isRefinedBy]
        case val v =>
          cases target
          case poison => simp [LLVM.Ptr.isRefinedBy] at hRefined
          case val t =>
            have : v = t := by simpa [LLVM.Ptr.isRefinedBy] using hRefined
            subst this
            simp [LLVM.Ptr.isRefinedBy, LLVM.Int.toReg]

end Veir
