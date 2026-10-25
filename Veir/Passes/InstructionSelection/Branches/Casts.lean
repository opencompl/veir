module

public import Veir.Passes.InstructionSelection.RISCV64Branches

import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Casting a value to a register and back

The branch lowering passes a value along a branch as a register. The value is
cast to a register in front of the branch and back to its type at the start of
the successor. This file gives the meaning of the two casts and shows that a
value of a type that `roundTrips` is refined by its round trip.

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

end Veir
