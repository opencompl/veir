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
LLVM sign-extends in place with `G_SEXT_INREG`; here we use the equivalent `g_trunc` to `i32`
followed by `g_sext` back to `i64`.
-/
def customLegalizeAddSub (opcode : GMIR) (noFlags : propertiesOf (OpCode.gmir opcode)) :
    Pattern OpCode :=
  Pattern.Builder
    (matchBinop opcode (·.bitwidth = 32))
    (fun (type, lhs, rhs) => do
      let wideType ← CreateProg.type (IntegerType.signless 64)
      let wide ← buildWideBinop opcode noFlags wideType lhs rhs
      let low ← buildTrunc wide type
      let sext ← buildExt low.res[0]! wideType .g_sext ()
      buildTrunc sext type)
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
      -- FIXME: We do not have `g_sext_inreg` and `g_and` yet, so other widths are always legal.
      .legalForTypePairs [(32, 16), (64, 16), (64, 32)],
      .alwaysLegal
    ]
    | .g_trunc => [
      .alwaysLegal,
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
