module

public import Veir.Passes.InstructionSelection.RISCV64Branches

import Veir.Interpreter.Refinement.Lemmas
import Veir.Dialects.LLVM.Lemmas
import Veir.Dialects.RISCV_Cf.Lemmas

public section

/-!
# Casting a value to a register and back

The branch lowering passes a value along a branch as a register. The value is
cast to a register in front of the branch and back to its type at the start of
the successor. This file gives the meaning of the two casts, shows that a value
of a type that `roundTrips` is refined by its round trip, and shows that the
RISC-V branch on the registers takes the successor that the LLVM branch takes.

A pointer fits a register too, but it travels as its address and comes back as
the pointer that the memory decodes that address to, which refines it only when
the pointer's object owns its address. `roundTrips` leaves pointers out, so the
proof does not cover a branch that passes one.
-/

open Veir.Data

namespace Veir

/--
  Whether a value of type `type` is refined by its round trip through a register:
  an integer or a byte that fits one.
-/
def roundTrips (type : TypeAttr) : Bool :=
  match type.val with
  | .integerType _ | .byteType _ => fitsRegister type
  | _ => false

theorem fitsRegister_of_roundTrips {type : TypeAttr} (h : roundTrips type) :
    fitsRegister type := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> simp_all [roundTrips]

/--
  The register that `builtin.unrealized_conversion_cast` turns an integer or a
  byte into.
-/
def RuntimeValue.toReg? : RuntimeValue → Option RISCV.Reg
  | .int _ value => some (LLVM.Int.toReg value)
  | .byte _ value => some (LLVM.Byte.toReg value)
  | _ => none

/--
  The integer or byte of type `type` that `builtin.unrealized_conversion_cast`
  turns a register into.
-/
def RuntimeValue.ofReg? (type : TypeAttr) (reg : RISCV.Reg) : Option RuntimeValue :=
  match type.val with
  | .integerType intType => some (.int intType.bitwidth (RISCV.Reg.toInt reg intType.bitwidth))
  | .byteType byteType => some (.byte byteType.bitwidth (RISCV.Reg.toByte reg byteType.bitwidth))
  | _ => none

/-- A cast to a register computes `toReg?`. -/
theorem interpretOp'_cast_toReg {value : RuntimeValue} {reg : RISCV.Reg} {mem : MemoryState}
    (hReg : value.toReg? = some reg)
    (properties : propertiesOf (OpCode.builtin .unrealized_conversion_cast))
    (successors : Array BlockPtr) :
    interpretOp' (.builtin .unrealized_conversion_cast) properties #[RegisterType.mk] #[value]
      successors mem = .ok (#[.reg reg], mem, none) := by
  cases value <;> grind [RuntimeValue.toReg?, interpretOp']

/-- A cast from a register computes `ofReg?`. -/
theorem interpretOp'_cast_ofReg {type : TypeAttr} {reg : RISCV.Reg} {value : RuntimeValue}
    {mem : MemoryState} (hValue : RuntimeValue.ofReg? type reg = some value)
    (properties : propertiesOf (OpCode.builtin .unrealized_conversion_cast))
    (successors : Array BlockPtr) :
    interpretOp' (.builtin .unrealized_conversion_cast) properties #[type] #[.reg reg]
      successors mem = .ok (#[value], mem, none) := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> grind [RuntimeValue.ofReg?, interpretOp']

/-- A value of a type that `roundTrips` is cast to a register. -/
theorem RuntimeValue.toReg?_eq_some_of_roundTrips {type : TypeAttr} {value : RuntimeValue}
    (hRoundTrips : roundTrips type) (hConforms : value.Conforms type) :
    ∃ reg, value.toReg? = some reg := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> simp only [roundTrips, Bool.false_eq_true] at hRoundTrips
  all_goals cases value <;> simp only [Conforms] at hConforms <;> exact ⟨_, rfl⟩

/--
  A value of a type that `roundTrips` is refined by what comes back from the
  register it is cast to, and what comes back is of its type.
-/
theorem RuntimeValue.isRefinedBy_ofReg?_of_toReg? {type : TypeAttr} {value : RuntimeValue}
    {reg : RISCV.Reg} (hRoundTrips : roundTrips type) (hConforms : value.Conforms type)
    (hReg : value.toReg? = some reg) :
    ∃ value', RuntimeValue.ofReg? type reg = some value' ∧ value ⊒ value' ∧
      value'.Conforms type := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> simp [roundTrips] at hRoundTrips
  all_goals
    cases value <;> simp only [Conforms] at hConforms <;> subst hConforms
    simp only [toReg?, Option.some.injEq] at hReg
    subst hReg
    exact ⟨_, rfl, by grind [RuntimeValue.isRefinedBy], rfl⟩

/--
  A value of a type that `roundTrips` is refined by its round trip through a
  register, even when the value that is cast is only a refinement of it.
-/
theorem RuntimeValue.isRefinedBy_ofReg?_toReg? {type : TypeAttr} {source target : RuntimeValue}
    (hRoundTrips : roundTrips type) (hConforms : source.Conforms type)
    (hRefined : source ⊒ target) :
    ∃ reg value, target.toReg? = some reg ∧ RuntimeValue.ofReg? type reg = some value ∧
      source ⊒ value ∧ value.Conforms type := by
  have hTarget := hConforms.of_isRefinedBy hRefined
  obtain ⟨reg, hReg⟩ := toReg?_eq_some_of_roundTrips hRoundTrips hTarget
  obtain ⟨value, hValue, hRefined', hConforms'⟩ :=
    isRefinedBy_ofReg?_of_toReg? hRoundTrips hTarget hReg
  exact ⟨reg, value, hReg, hValue, RuntimeValue.isRefinedBy_trans hRefined hRefined',
    hConforms'⟩

/-! ## The two branches -/

/--
  `target` holds the registers that the values `source` are cast to, where the
  value that is cast may be a refinement of the source value.
-/
structure RegistersOf (source target : Array RuntimeValue) : Prop where
  /-- There is one register per value. -/
  size_eq : source.size = target.size
  /-- The register at `i` is the cast of a refinement of the value at `i`. -/
  get : ∀ i, i < source.size → ∃ value reg,
    source[i]! ⊒ value ∧ value.toReg? = some reg ∧ target[i]! = .reg reg

/-- No value has no register. -/
theorem RegistersOf.empty : RegistersOf #[] #[] := ⟨rfl, by simp⟩

/-- One more value and the register it is cast to. -/
theorem RegistersOf.push {source target : Array RuntimeValue} (h : RegistersOf source target)
    {s value : RuntimeValue} {reg : RISCV.Reg} (hRefined : s ⊒ value)
    (hReg : value.toReg? = some reg) :
    RegistersOf (source.push s) (target.push (.reg reg)) := by
  refine ⟨by simp [h.size_eq], fun i hi => ?_⟩
  grind [h.size_eq, h.get]

theorem RegistersOf.extract {source target : Array RuntimeValue}
    (h : RegistersOf source target) (start stop : Nat) :
    RegistersOf (source.extract start stop) (target.extract start stop) := by
  refine ⟨by simp [h.size_eq], fun i hi => ?_⟩
  have := h.get (start + i) (by simp at hi; omega)
  grind [h.size_eq]

theorem RegistersOf.extract_from {source target : Array RuntimeValue}
    (h : RegistersOf source target) (start : Nat) :
    RegistersOf (source.extract start) (target.extract start) :=
  h.size_eq ▸ h.extract start source.size

/-- `riscv_cf.branch` on the registers of the operands of an `llvm.br` branches like it. -/
theorem interpretOp'_br_registers
    {properties resultTypes operands successors mem results mem' action}
    (h : interpretOp' (.llvm .br) properties resultTypes operands successors mem =
      .ok (results, mem', action))
    {registers : Array RuntimeValue} (hRegisters : RegistersOf operands registers)
    (properties' : propertiesOf (OpCode.riscv_cf .branch)) (resultTypes' : Array TypeAttr) :
    ∃ values values' dest, results = #[] ∧ mem' = mem ∧
      action = some (.branch values dest) ∧
      interpretOp' (.riscv_cf .branch) properties' resultTypes' registers successors mem =
        .ok (#[], mem, some (.branch values' dest)) ∧
      RegistersOf values values' := by
  obtain ⟨dest, rfl, rfl, rfl, rfl⟩ := interpretOp'_llvm_br_eq_ok_iff.mp h
  exact ⟨operands, registers, dest, rfl, rfl, rfl, interpretOp'_riscv_cf_branch,
    hRegisters⟩

/--
  `riscv_cf.bnez` on the registers of the operands of an `llvm.cond_br` branches
  like it. A poison condition is undefined behaviour in the source, so there is
  nothing to show for it.
-/
theorem interpretOp'_cond_br_registers
    {properties resultTypes operands successors mem results mem' action}
    (h : interpretOp' (.llvm .cond_br) properties resultTypes operands successors mem =
      .ok (results, mem', action))
    {registers : Array RuntimeValue} (hRegisters : RegistersOf operands registers)
    (properties' : propertiesOf (OpCode.riscv_cf .bnez)) (resultTypes' : Array TypeAttr)
    (hSizes : properties'.operandSegmentSizes = properties.operandSegmentSizes) :
    ∃ values values' dest, results = #[] ∧ mem' = mem ∧
      action = some (.branch values dest) ∧
      interpretOp' (.riscv_cf .bnez) properties' resultTypes' registers successors mem =
        .ok (#[], mem, some (.branch values' dest)) ∧
      RegistersOf values values' := by
  obtain ⟨destTrue, destFalse, cond, n, rfl, hCond, hSize, rfl, rfl, rfl⟩ :=
    interpretOp'_llvm_cond_br_eq_ok_iff.mp h
  obtain ⟨hLt, hOperand⟩ := Array.getElem?_eq_some_iff.mp hCond
  obtain ⟨value, reg, hRefined, hReg, hRegister⟩ := hRegisters.get 0 hLt
  rw [getElem!_pos operands 0 hLt, hOperand, RuntimeValue.int_val_isRefinedBy_iff]
    at hRefined
  subst hRefined
  simp only [RuntimeValue.toReg?, Option.some.injEq] at hReg
  have hRegister' : registers[0]? = some (.reg reg) := by
    rw [← hRegister]; exact Array.getElem?_eq_some_getElem! _ _ (hRegisters.size_eq ▸ hLt)
  have hRegVal : reg.val = cond.zeroExtend 64 := by simp [← hReg, val_toReg]
  have hCondIff : reg.val ≠ 0#64 ↔ cond = 1#1 := by
    rw [hRegVal]; exact (by decide : ∀ c : BitVec 1, c.zeroExtend 64 ≠ 0#64 ↔ c = 1#1) cond
  rw [interpretOp'_riscv_cf_bnez hRegister' (hSizes ▸ hSize)]
  by_cases hc : cond = 1#1 <;> simp only [hCondIff, hc, ↓reduceIte]
  · exact ⟨_, _, destTrue, trivial, trivial, rfl, rfl, hRegisters.extract _ _⟩
  · exact ⟨_, _, destFalse, trivial, trivial, rfl, rfl, hRegisters.extract_from _⟩

end Veir
