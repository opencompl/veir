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

/--
  Custom legalization of `i32` operations with `numOperands` operands into their RISC-V word
  variant (e.g. `g_add` -> `riscv.addw`, `g_sdiv` -> `riscv.divw`, `g_ctlz` -> `riscv.clzw`).
  For `g_add`/`g_sub`/`g_mul`, LLVM emits `G_SEXT_INREG` here instead, and selects the word variant
  later. For `g_sdiv`/`g_udiv`/`g_urem`/`g_ctlz`/`g_cttz`, LLVM custom-legalizes into
  `RISCV::G_DIVW`, `RISCV::G_CLZW` etc.
-/
def customLegalizeWord (opcode : GMIR) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) (numOperands : Nat := 2) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 32)
      let operands ← (Array.replicate numOperands ()).mapM fun _ => MatchProg.value opType
      let _ ← MatchProg.root (.gmir opcode) operands #[opType]
      return (opType, operands))
    (fun (opType, operands) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castProps ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let regOperands ← operands.mapM fun operand => do
        let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
            #[operand] #[regType] castProps
        return castOp.res[0]!
      let riscvOpProps ← CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← CreateProg.operation (.riscv riscvOp) regOperands #[regType] riscvOpProps
      CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[opType] castProps)
    (fun castBackOp => castBackOp)

end

private def s16 : LLT := .scalar 16
private def s32 : LLT := .scalar 32
private def s64 : LLT := .scalar 64
private def p0 : LLT := .pointer 0

public section

def riscv64LegalizerInfo : LegalizerInfo where
  rules
    | .g_add | .g_sub => [
      .legalFor [s64],
      .customFor [s32],
      .minScalar (.type 0) 64,
    ]
    | .g_icmp => [
      .legalForTypePairs [(s64, s64), (s64, p0)],
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
      .legalForTypePairs [(s32, s16), (s64, s16), (s64, s32)],
      .alwaysLegal
    ]
    | .g_trunc => [
      .alwaysLegal,
    ]
    | .g_and | .g_or | .g_xor =>
      [
        .legalFor [s64],
        .minScalar (.type 0) 64,
      ]
    | .g_mul => [
      .legalFor [s64],
      .customFor [s32],
      .minScalar (.type 0) 64,
    ]
    | .g_srem => [
      .legalFor [s64],
      .minScalar (.type 0) 64,
    ]
    | .g_sdiv | .g_udiv | .g_urem => [
      .legalFor [s64],
      .customFor [s32],
      .minScalar (.type 0) 32,
      .minScalar (.type 0) 64,
    ]
    | .g_constant => [
      -- LLVM's custom `i64` rule only decides on the constant pool, which we don't need.
      .legalFor [s64],
      .minScalar (.type 0) 64,
    ]
    | .g_bswap => sorry
    | .g_bitreverse => sorry
    -- The `Zbb` rules, which the RISC-V 64 instruction selection assumes.
    | .g_ctlz | .g_cttz => [
      .legalForTypePairs [(s64, s64)],
      .customIf (.all [.typeIs (.type 0) s32, .typeIs (.type 1) s32]),
      .minScalar (.type 0) 32,
      .minScalar (.type 1) 32,
      .minScalar (.type 0) 64,
      .minScalar (.type 1) 64,
    ]
    | .g_ctlz_zero_poison | .g_cttz_zero_poison => [
      .lower,
    ]
    | .g_ctpop => [
      .legalForTypePairs [(s64, s64)],
      .customIf (.all [.typeIs (.type 0) s32, .typeIs (.type 1) s32]),
      .minScalar (.type 0) 32,
      .minScalar (.type 1) 32,
      .minScalar (.type 0) 64,
      .minScalar (.type 1) 64,
    ]
    | _ => []
  legalizeCustom
    | .g_add => customLegalizeWord .g_add .addw ()
    | .g_sub => customLegalizeWord .g_sub .subw ()
    | .g_mul => customLegalizeWord .g_mul .mulw ()
    | .g_sdiv => customLegalizeWord .g_sdiv .divw ()
    | .g_udiv => customLegalizeWord .g_udiv .divuw ()
    | .g_urem => customLegalizeWord .g_urem .remuw ()
    | .g_ctlz => customLegalizeWord .g_ctlz .clzw () (numOperands := 1)
    | .g_cttz => customLegalizeWord .g_cttz .ctzw () (numOperands := 1)
    | .g_ctpop => customLegalizeWord .g_ctpop .cpopw () (numOperands := 1)
    | _ => none

def LegalizeRISCV64Pass : Pass OpCode :=
  { name := "legalize-riscv64"
    description := "Legalize gMIR operations for RISC-V 64."
    run := fun _ ctx _ _ => riscv64LegalizerInfo.legalize ctx }

end

end Veir
