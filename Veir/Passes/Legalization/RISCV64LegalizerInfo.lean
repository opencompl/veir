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

-- TODO: Add custom rules with `sext_in_reg`, so that `addw` and `subw` can be selected later.
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
    | .g_anyext | .g_sext | .g_zext => [
      -- Widening creates extensions from any width, such as `i8` to `i64`. LLVM folds most of them
      -- away during legalization with its artifact combiner. We have none, so all extensions up to
      -- 64 bits are legal.
      .legalIf (·.sizeInBits 0 ≤ 64),
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
