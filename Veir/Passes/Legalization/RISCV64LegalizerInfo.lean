module

public import Veir.Pass
public import Veir.Passes.Legalization.LegalizerInfo
import Veir.Passes.Legalization.Legalizer
import Veir.PatternRewriter.Puddle.Builders

/-!
# RISC-V 64 Legalization

This file implements the legalization pass for RISC-V 64.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVLegalizerInfo.cpp
-/

namespace Veir

section
open Puddle in

/-- Custom legalization of an `i32` `opcode` to its word variant `riscvOp`. -/
def customLegalizeWordOp (opcode : GMIR) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 32)
      let lhs ← MatchProg.value opType
      let rhs ← MatchProg.value opType
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[opType]
      return (opType, lhs, rhs))
    (fun (opType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castProps ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let lcastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType] castProps
      let rcastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType] castProps
      let riscvOpProps ← CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← CreateProg.operation (.riscv riscvOp)
          #[lcastOp.res[0]!, rcastOp.res[0]!] #[regType] riscvOpProps
      CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[opType] castProps)
    (fun castBackOp => castBackOp)

end

public section

def riscv64LegalizerInfo : LegalizerInfo where
  rules
    | .g_add | .g_sub => [
      .legalFor [64],
      .customFor [32],
      .minScalar (.type 0) 64,
    ]
    | .g_shl | .g_lshr | .g_ashr => [
      .legalForTypePairs [(64, 64)],
      -- TODO: Widen shifts by a constant instead once shifts by an immediate are also selected.
      .customForTypePairs [(32, 32)],
      .minScalar (.type 1) 64,
      .minScalar (.type 0) 64,
    ]
    | .g_icmp => [
      .legalForTypePairs [(64, 64)],
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
    | _ => []
  legalizeCustom
    -- LLVM instead emits `G_ADD` + `G_SEXT_IN_REG` instead, and matches on this later during
    -- instruction selection. We omit the word-variant directly as a simplification.
    | .g_add => customLegalizeWordOp .g_add .addw ()
    | .g_sub => customLegalizeWordOp .g_sub .subw ()
    | .g_shl => customLegalizeWordOp .g_shl .sllw ()
    | .g_lshr => customLegalizeWordOp .g_lshr .srlw ()
    | .g_ashr => customLegalizeWordOp .g_ashr .sraw ()
    | _ => none

def LegalizeRISCV64Pass : Pass OpCode :=
  { name := "legalize-riscv64"
    description := "Legalize gMIR operations for RISC-V 64."
    run := fun _ ctx _ _ => riscv64LegalizerInfo.legalize ctx }

end

end Veir
