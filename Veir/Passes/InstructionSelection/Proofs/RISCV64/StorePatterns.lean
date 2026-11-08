module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Stores
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.StorePatternLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.StoreFoldedPatternLemmas

namespace Veir

open Puddle
attribute [local implicit_reducible] TypeAttr

/-- A register realization of an LLVM integer or pointer gives a refining raw store. -/
theorem storePrimitiveRefines (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) :
    StorePrimitiveRefines n := by
  intro memory p ty value reg width conforms href
  obtain (⟨sign, rfl⟩ | ⟨pointer, rfl, rfl⟩) := memAccessWidth_cases width
  · simp only [RuntimeValue.Conforms.integerType] at conforms
    obtain ⟨x, rfl⟩ := conforms
    exact llvmStoreInt_refines memory p n hn x reg.val href
  · simp only [RuntimeValue.Conforms.llvmPointerType] at conforms
    obtain ⟨x, rfl⟩ := conforms
    exact llvmStorePtr_refines memory p x reg.val href

theorem lowerStore_reg_sb_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 1 .sb) :=
  lowerStore_reg_sb_of (storePrimitiveRefines 1 (.inl rfl))

theorem lowerStore_reg_sh_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 2 .sh) :=
  lowerStore_reg_sh_of (storePrimitiveRefines 2 (.inr (.inl rfl)))

theorem lowerStore_reg_sw_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 4 .sw) :=
  lowerStore_reg_sw_of (storePrimitiveRefines 4 (.inr (.inr (.inl rfl))))

theorem lowerStore_reg_sd_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 8 .sd) :=
  lowerStore_reg_sd_of (storePrimitiveRefines 8 (.inr (.inr (.inr rfl))))

theorem lowerStore_gepConst_sb_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 1 .sb) :=
  lowerStore_gepConst_sb_of (storePrimitiveRefines 1 (.inl rfl))

theorem lowerStore_gepConst_sh_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 2 .sh) :=
  lowerStore_gepConst_sh_of (storePrimitiveRefines 2 (.inr (.inl rfl)))

theorem lowerStore_gepConst_sw_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 4 .sw) :=
  lowerStore_gepConst_sw_of (storePrimitiveRefines 4 (.inr (.inr (.inl rfl))))

theorem lowerStore_gepConst_sd_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 8 .sd) :=
  lowerStore_gepConst_sd_of (storePrimitiveRefines 8 (.inr (.inr (.inr rfl))))

theorem lowerStore_gepIndex_sb_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 1 .sb) :=
  lowerStore_gepIndex_sb_of (storePrimitiveRefines 1 (.inl rfl))

theorem lowerStore_gepIndex_sh_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 2 .sh) :=
  lowerStore_gepIndex_sh_of (storePrimitiveRefines 2 (.inr (.inl rfl)))

theorem lowerStore_gepIndex_sw_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 4 .sw) :=
  lowerStore_gepIndex_sw_of (storePrimitiveRefines 4 (.inr (.inr (.inl rfl))))

theorem lowerStore_gepIndex_sd_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 8 .sd) :=
  lowerStore_gepIndex_sd_of (storePrimitiveRefines 8 (.inr (.inr (.inr rfl))))

end Veir
