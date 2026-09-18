module

import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Memory
import all Veir.Data.Casting
import all Veir.RuntimeValue.Conforms
import all Veir.IR.Attribute
import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.Builtin.OpInfo
import Veir.PatternRewriter.Puddle.Validity
import Veir.Interpreter.Refinement.Lemmas
meta import Veir.PatternRewriter.Puddle.Definitions
meta import Veir.PatternRewriter.Puddle.Validity

/-!
  Validity proofs for the Puddle lowering patterns of the RISC-V 64 instruction selector.
-/

namespace Veir

open Veir.Data

/-- A single value conforms to a single type. -/
private theorem arrayConforms_singleton {v : RuntimeValue} {ty : TypeAttr} (h : v.Conforms ty) :
    RuntimeValue.ArrayConforms #[v] #[ty] := by
  refine ⟨rfl, fun i hi => ?_⟩
  have : i = 0 := by simp at hi; omega
  subst this
  exact h

/--
  `freeze_pattern` is valid: a frozen `i32`/`i64` value is refined by the value cast to a
  register and back. A register carries no poison, and a defined value survives the
  round trip since it fits in 64 bits.

  Freezing poison draws its value from the oracle, which advances the memory state, so the
  matcher's memory-preserving interpretation only covers defined operands.
-/
theorem freeze_pattern_valid : freeze_pattern.Valid := by
  simp only [freeze_pattern]
  provePuddleValid
  intro ty ht x hx _ result hr
  cases hc : ty.cast? IntegerType with
  | none => simp [hc] at ht
  | some t =>
  simp [hc] at ht
  have hty := (IsTypeAttr.cast?_eq_some_iff ty t).mp hc
  subst hty
  obtain ⟨v, rfl⟩ := RuntimeValue.Conforms.integerType hx
  cases v with
  | poison =>
    have h := hr.2 MemoryState.empty
    simp [interpretOp', Llvm.interpretOp', MemoryState.drawFreeze] at h
    exact absurd (congrArg MemoryState.freezes h.2) (by simp)
  | val b =>
    have h := hr.2 MemoryState.empty
    simp [interpretOp', Llvm.interpretOp'] at h
    subst h
    refine ⟨.reg (LLVM.Int.toReg (.val b)), ⟨arrayConforms_singleton trivial, fun _ => rfl⟩,
      .int t.bitwidth (RISCV.Reg.toInt (LLVM.Int.toReg (.val b)) t.bitwidth),
      ⟨arrayConforms_singleton rfl, fun _ => rfl⟩, ?_⟩
    simp [RuntimeValue.isRefinedBy, LLVM.Int.cast, isRefinedBy, RISCV.Reg.toInt, LLVM.Int.toReg]
    have hle : t.bitwidth ≤ 64 := by omega
    rw [BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq]

end Veir
