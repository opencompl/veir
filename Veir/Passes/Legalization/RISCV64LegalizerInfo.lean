module

public import Veir.Pass
public import Veir.Passes.Legalization.LegalizerInfo
import Veir.Passes.Legalization.Legalizer
import Veir.Passes.Legalization.LegalizerHelper
import Veir.PatternRewriter.Puddle.Builders

/-!
# RISC-V 64 Legalization

This file implements the legalization pass for RISC-V 64.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVLegalizerInfo.cpp
-/

namespace Veir

open Puddle in
/--
Computes a 32-bit `opcode` operation on 64 bits and sign-extends the result from bit 31, so that
`addw` and `subw` can be selected. This is the `G_ADD`/`G_SUB` case of LLVM's `legalizeCustom`.
-/
def customLegalizeAddSub (opcode : GMIR) (noFlags : propertiesOf (OpCode.gmir opcode)) :
    Pattern OpCode :=
  Pattern.Builder
    (matchBinop opcode (·.bitwidth = 32))
    (fun (type, lhs, rhs) => do
      let wideType ← CreateProg.type (IntegerType.signless 64)
      let wide ← buildWideBinop opcode noFlags wideType lhs rhs
      let sextProps ← CreateProg.property (.gmir .g_sext_inreg) ⟨32⟩
      let sext ← CreateProg.operation (.gmir .g_sext_inreg) #[wide] #[wideType] sextProps
      buildTrunc sext.res[0]! type)
    (fun trunc => trunc)

/-- A pointer in address space 0, as LLVM's `p0`. -/
private def p0 : LLT := .pointer 0

public section

def riscv64LegalizerInfo : LegalizerInfo where
  rules
    | .g_add | .g_sub => [
      .legalFor [64],
      .customFor [32],
      .minScalar (.type 0) 64,
    ]
    | .g_icmp => [
      .legalForTypePairs [(64, 64), (64, p0)],
      .minScalar (.type 1) 64,
      .minScalar (.type 0) 64,
    ]
    | .g_anyext => [
      .alwaysLegal,
    ]
    | .g_sext | .g_zext => [
      -- In LLVM, extensions from other widths never reach these rules: their operands are always
      -- the result of a  `g_trunc`, and the artifact combiner turns them into `g_sext_inreg`
      -- or `g_and`.
      -- FIXME: Add `g_sext_inreg`, `g_and` and these folds. Until then, other widths always legal.
      .legalForTypePairs [(32, 16), (64, 16), (64, 32)],
      .alwaysLegal
    ]
    | .g_trunc => [
      .alwaysLegal,
    ]
    | .g_sext_inreg => [
      -- Sizes 8 and 16 need Zbb, which this backend already assumes.
      -- TODO: Lower other sizes to `g_shl` and `g_ashr`, as LLVM's `lower` does.
      .legalIf (.all [
        .typeIs (.type 0) 64,
        fun query => [8, 16, 32].contains query.properties.sz.toNat,
      ]),
    ]
  legalizeCustom
    | .g_add => customLegalizeAddSub .g_add ⟨false, false⟩
    | .g_sub => customLegalizeAddSub .g_sub ⟨false, false⟩
    | _ => none

def LegalizeRISCV64Pass : Pass OpCode :=
  { name := "legalize-riscv64"
    description := "Legalize gMIR operations for RISC-V 64."
    run := fun _ ctx _ _ => riscv64LegalizerInfo.legalize ctx }

end

end Veir
