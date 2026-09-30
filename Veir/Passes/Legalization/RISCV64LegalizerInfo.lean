module

public import Veir.Pass
public import Veir.Passes.Legalization.LegalizerInfo
import Veir.Passes.Legalization.Legalizer

/-!
# RISC-V 64 Legalization

This file implements the legalization pass for RISC-V 64.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVLegalizerInfo.cpp
-/

namespace Veir

public section

-- TODO: Add custom rules which help select the word variants of operations.
def riscv64LegalizerInfo : LegalizerInfo where
  rules
    | .g_add | .g_sub => [
      .legalFor [64],
      .minScalar 0 64,
    ]
    | .g_icmp => [
      .legalForTypePairs [(64, 64)],
      .minScalar 1 64,
      .minScalar 0 64,
    ]
    | .g_anyext => [
      .alwaysLegal,
    ]
    | .g_sext | .g_zext => [
      -- In LLVM, extensions from other widths never reach these rules: their operands are always
      -- the result of a  `g_trunc`, and the artifact combiner turns them into `g_sext_inreg`
      -- or `g_and`.
      -- TODO: Add `g_sext_inreg`, `g_and` and these folds. Until then, other widths are illegal.
      -- TODO: Extending from 16 -> 32 seems to be legal and selects sext.w / zext.w. Why?
      .legalForTypePairs [(32, 16), (64, 16), (64, 32)],
    ]
    | .g_trunc => [
      .alwaysLegal,
    ]

def LegalizeRISCV64Pass : Pass OpCode :=
  { name := "legalize-riscv64"
    description := "Legalize gMIR operations for RISC-V 64."
    run := fun _ ctx _ _ => riscv64LegalizerInfo.legalize ctx }

end

end Veir
