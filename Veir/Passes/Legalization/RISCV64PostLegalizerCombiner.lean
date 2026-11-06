module

public import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Canonicalize
import Veir.Passes.Legalization.CombinerHelper
import Veir.Passes.Legalization.RISCV64LegalizerInfo
import Veir.PatternRewriter.Puddle.Execution

/-!
# RISC-V 64 Post-Legalizer Combiner

This file implements the combines that run on the legalized gMIR of RISC-V 64. They preserve
legality, so the result is still legal gMIR.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVPostLegalizerCombiner.cpp
-/

namespace Veir

open Puddle

/--
The RISC-V word operations, into which the legalizer turns an `i32` division. They divide and shift
the low 32 bits of their operands, so the division-by-power-of-two combines read the low 32 bits of
the divisor. LLVM runs those combines before legalization, on the `i32` division, and then selects
the `i32` shifts as `srliw`/`sraiw`/`addw`/`subw`, which is what these give.
-/
def DivByPow2Ops.riscvWord : DivByPow2Ops :=
  { width := some 32, sdiv := .gmir_riscv .g_divw, udiv := .gmir_riscv .g_divuw,
    ashr := .gmir_riscv .g_sraw, lshr := .gmir_riscv .g_srlw, add := .gmir_riscv .g_addw,
    sub := .gmir_riscv .g_subw }

/-- The division-by-power-of-two combines on the RISC-V word divisions. `g_divw` has no `exact`
    flag, so `sdiv exact` at `i32` gets the general sequence. -/
def riscvWordIntdivCombines : Array (CompiledPattern OpCode) :=
  #[sdiv_by_pow2_pattern false .riscvWord, sdiv_by_pow2_pattern true .riscvWord,
    udiv_by_pow2_pattern .riscvWord].map (·.compile)

public section

def PostLegalizerCombinerRISCV64Pass : Pass OpCode :=
  { name := "postlegalizer-combiner-riscv64"
    description := "Combine legalized gMIR operations for RISC-V 64."
    run := fun _ ctx op _ => do
      -- The combines come before `sub_to_add`, which would otherwise rewrite the subtractions
      -- some of them match.
      let pattern := RewritePattern.GreedyRewritePattern <|
        (combines ++ selectCombines riscv64LegalizerInfo ++ riscvWordIntdivCombines).map (·.run) ++
        #[(sub_to_add riscv64LegalizerInfo).run, redundant_and.run, commutativeConstantRHS]
      match RewritePattern.applyToFunctions pattern ctx op with
      | none => throw "Error while applying the post-legalizer combines"
      | some ctx => pure ctx }

end

end Veir
