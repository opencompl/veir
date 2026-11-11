module

import all Veir.Passes.RISCVCombines.Validity.Common

/-! CTree validity proofs for the RISC-V combines that match a load below their root. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

set_option linter.unusedSimpArgs false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Rv64.interpretOp'

attribute [local implicit_reducible] TypeAttr

/-- `x` is a value a RISC-V load of `n` bytes at `p` can produce: the bits stored at `p`, with each
poison bit frozen to some concrete value. It is kept folded, so that the validity proofs treat the
loaded value as an arbitrary bitvector. -/
def LoadsBits (mem : MemoryState) (p : Data.Pointer) (n : Nat) (x : BitVec (8 * n)) : Prop :=
  ∃ b, mem.loadByte p (8 * n) = .ok b ∧ ∃ bits, x = b.val ||| (b.poison &&& bits)

/-- A RISC-V load CTree that succeeds returns the bits it read, extended to a register, and leaves
memory unchanged. -/
@[local simp] theorem riscvLoadCTree_canInterpretTo_ok {EIn : Type} {E : EIn → Type}
    [ErrorE -< E] [UBE -< E] {imm12 : BitVec 12} {addr : Data.RISCV.Reg}
    {mem mem' : MemoryState} {n : Nat} {ext : LoadExtension} {v : RuntimeValue} :
    PureOrErr.CanInterpretTo (E := E) (riscvLoadCTree imm12 #[.reg addr] mem n ext)
        (.ok (#[v], mem', none)) ↔
      ∃ x, LoadsBits mem (mem.decode (UInt64.ofBitVec (riscvEffectiveAddr addr.val imm12))) n x ∧
        v = .reg ⟨match ext with
          | .signExt => x.signExtend 64
          | .zeroExt => x.setWidth 64⟩ ∧
        mem' = mem := by
  simp [riscvLoadCTree, Bind.bind, PureOrErr.CanInterpretTo.bind_iff, LoadsBits]
  constructor
  · rintro ⟨b, hb, ⟨bits, rfl⟩, rfl⟩
    exact ⟨_, ⟨b, hb, bits, rfl⟩, by cases ext <;> simp, rfl⟩
  · rintro ⟨_, ⟨b, hb, bits, rfl⟩, rfl, rfl⟩
    exact ⟨b, hb, ⟨bits, by cases ext <;> simp⟩, rfl⟩

theorem zextb_lbu_valid : Puddle.CTree.Pattern.Valid (zextb_lbu_pattern) := by
  proveCombineValid using Data.RISCV.zextb_lbu

theorem andi_255_lbu_valid : Puddle.CTree.Pattern.Valid (andi_255_lbu_pattern) := by
  proveCombineValid using Data.RISCV.andi_255_lbu

theorem zextw_slliw_lbu_8_valid : Puddle.CTree.Pattern.Valid (zextw_slliw_lbu_pattern 8) := by
  proveCombineValid using Data.RISCV.zextw_slliw_lbu_8

theorem zextw_slliw_lbu_16_valid : Puddle.CTree.Pattern.Valid (zextw_slliw_lbu_pattern 16) := by
  proveCombineValid using Data.RISCV.zextw_slliw_lbu_16

theorem zextw_slliw_lbu_24_valid : Puddle.CTree.Pattern.Valid (zextw_slliw_lbu_pattern 24) := by
  proveCombineValid using Data.RISCV.zextw_slliw_lbu_24

theorem packh_low_bytes_valid : Puddle.CTree.Pattern.Valid (packh_low_bytes_pattern false) := by
  proveCombineValid using Data.RISCV.packh_low_bytes

theorem packh_low_bytes_commuted_valid : Puddle.CTree.Pattern.Valid (packh_low_bytes_pattern true) := by
  proveCombineValid using Data.RISCV.packh_low_bytes_commuted

theorem packh_high_bytes_valid : Puddle.CTree.Pattern.Valid (packh_high_bytes_pattern false) := by
  proveCombineValid using Data.RISCV.packh_high_bytes

theorem packh_high_bytes_commuted_valid : Puddle.CTree.Pattern.Valid (packh_high_bytes_pattern true) := by
  proveCombineValid using Data.RISCV.packh_high_bytes_commuted

theorem sextw_lw_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lw 1) := by
  proveCombineValid using Data.RISCV.sextw_lw

theorem sextw_lh_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lh 1) := by
  proveCombineValid using Data.RISCV.sextw_lh

theorem sextw_lb_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lb 1) := by
  proveCombineValid using Data.RISCV.sextw_lb

theorem sextw_lhu_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lhu 1) := by
  proveCombineValid using Data.RISCV.sextw_lhu

theorem sextw_lbu_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lbu 1) := by
  proveCombineValid using Data.RISCV.sextw_lbu

end Veir.RISCV.CTreeProofs
