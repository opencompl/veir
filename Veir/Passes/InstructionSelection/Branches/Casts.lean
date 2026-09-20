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

/-! ## The two branches -/

/--
  `target` holds the registers that the values `source` are cast to, where
  the value that is cast may be a refinement of the source value.
-/
@[expose]
def RegistersOf (source target : Array RuntimeValue) : Prop :=
  source.size = target.size ∧
  ∀ i, i < source.size → ∃ value reg,
    source[i]! ⊒ value ∧ value.toReg? = some reg ∧ target[i]! = .reg reg

theorem RegistersOf.extract {source target : Array RuntimeValue}
    (h : RegistersOf source target) (start stop : Nat) :
    RegistersOf (source.extract start stop) (target.extract start stop) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  have hi' : i < (target.extract start stop).size := by simpa [h.1] using hi
  simp only [Array.size_extract] at hi hi'
  obtain ⟨value, reg, h₁, h₂, h₃⟩ := h.2 (start + i) (by omega)
  refine ⟨value, reg, ?_, h₂, ?_⟩
  · rw [getElem!_pos _ _ (by simp; omega)]
    rw [getElem!_pos _ _ (by omega)] at h₁
    simpa using h₁
  · rw [getElem!_pos _ _ (by simp; omega)]
    rw [getElem!_pos _ _ (by omega)] at h₃
    simpa using h₃

theorem RegistersOf.extract_from {source target : Array RuntimeValue}
    (h : RegistersOf source target) (start : Nat) :
    RegistersOf (source.extract start) (target.extract start) := by
  have := h.extract start source.size
  rwa [show target.extract start source.size = target.extract start by rw [h.1]] at this

/-- `riscv_cf.branch` on the registers of the operands of an `llvm.br` branches like it. -/
theorem interpretOp'_br_registers {properties resultTypes operands successors mem results mem' action}
    (h : interpretOp' (.llvm .br) properties resultTypes operands successors mem =
      .ok (results, mem', action))
    {registers : Array RuntimeValue} (hRegisters : RegistersOf operands registers)
    (properties' : propertiesOf (OpCode.riscv_cf .branch)) (resultTypes' : Array TypeAttr) :
    ∃ values values' dest, results = #[] ∧ mem' = mem ∧ action = some (.branch values dest) ∧
      interpretOp' (.riscv_cf .branch) properties' resultTypes' registers successors mem =
        .ok (#[], mem, some (.branch values' dest)) ∧
      RegistersOf values values' := by
  simp only [interpretOp', Llvm.interpretOp', Riscv_Cf.interpretOp', bind, pure] at h ⊢
  split at h
  next dest hDest =>
    simp only [Interp.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨operands, registers, dest, rfl, rfl, rfl, by simp, hRegisters⟩
  next => simp at h

/-- `riscv_cf.bnez` on the registers of the operands of an `llvm.cond_br` branches like it. -/
theorem interpretOp'_cond_br_registers
    {properties resultTypes operands successors mem results mem' action}
    (h : interpretOp' (.llvm .cond_br) properties resultTypes operands successors mem =
      .ok (results, mem', action))
    {registers : Array RuntimeValue} (hRegisters : RegistersOf operands registers)
    (properties' : propertiesOf (OpCode.riscv_cf .bnez)) (resultTypes' : Array TypeAttr)
    (hSizes : properties'.operandSegmentSizes = properties.operandSegmentSizes) :
    ∃ values values' dest, results = #[] ∧ mem' = mem ∧ action = some (.branch values dest) ∧
      interpretOp' (.riscv_cf .bnez) properties' resultTypes' registers successors mem =
        .ok (#[], mem, some (.branch values' dest)) ∧
      RegistersOf values values' := by
  simp only [interpretOp', Llvm.interpretOp', Riscv_Cf.interpretOp', bind, pure, hSizes] at h ⊢
  split at h
  next destTrue destFalse hDest =>
    split at h
    next condVal hCond =>
      split at h
      next trueSize hTrueSize =>
        split at h
        next cond =>
          have hSize : 0 < operands.size := by
            apply Classical.byContradiction; intro hNot
            rw [Array.getElem?_eq_none (by omega)] at hCond; simp at hCond
          obtain ⟨value, reg, hRefined, hReg, hRegister⟩ := hRegisters.2 0 hSize
          have hOperand : operands[0]! = .int 1 (.val cond) := by
            rw [getElem!_pos operands 0 hSize]; simpa [Array.getElem?_eq_getElem hSize] using hCond
          rw [hOperand] at hRefined
          obtain ⟨target, rfl, hRefined⟩ := RuntimeValue.int_of_isRefinedBy hRefined
          obtain rfl : target = .val cond := by
            rcases target with t | _ <;> simp_all [isRefinedBy_eq]
          have hRegVal : reg.val = cond.zeroExtend 64 := by
            simp only [RuntimeValue.toReg?, Option.some.injEq] at hReg
            rw [← hReg]; rfl
          have hRegister' : registers[0]? = some (.reg reg) := by
            rw [← hRegister, getElem!_pos _ _ (by rw [← hRegisters.1]; exact hSize)]
            exact Array.getElem?_eq_getElem _
          have hWidth : ∀ c : BitVec 1, c.zeroExtend 64 ≠ 0#64 ↔ c = 1#1 := by decide
          have hCondIff : reg.val ≠ 0#64 ↔ cond = 1#1 := by rw [hRegVal]; exact hWidth cond
          simp only [hRegister', hCondIff]
          split at h <;> rename_i hc
          all_goals
            simp only [Interp.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            simp only [hc, ↓reduceIte]
            first
              | exact ⟨_, _, _, trivial, trivial, rfl, rfl, hRegisters.extract _ _⟩
              | exact ⟨_, _, _, trivial, trivial, rfl, rfl, hRegisters.extract_from _⟩
        next => simp at h
        next => simp at h
      next => simp at h
    next => simp at h
  next => simp at h

end Veir
