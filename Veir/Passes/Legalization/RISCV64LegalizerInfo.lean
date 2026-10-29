module

public import Veir.Pass
public import Veir.Passes.Legalization.LegalizerInfo
import Veir.Passes.Legalization.Legalizer
import Veir.Passes.Legalization.LegalizerHelper
import Veir.Passes.InstructionSelection.Common

/-!
# RISC-V 64 Legalization

This file implements the legalization pass for RISC-V 64.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVLegalizerInfo.cpp
-/

namespace Veir

/--
  Custom-legalize an i32 binary operation to a RISC-V gMIR word operation. Its operands are
  any-extended to i64 and its any-extended i64 result is truncated back to i32. The word
  operation reads only the low 32 bits and keeps the original properties, including `exact`,
  for post-legalizer combines and instruction selection.
-/
def customLegalizeWord (opcode wordOpcode : GMIR)
    (h : propertiesOf (OpCode.gmir opcode) = propertiesOf (OpCode.gmir wordOpcode)) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := IntegerType) (·.bitwidth = 32)
      let lhs ← Puddle.MatchProg.value type
      let rhs ← Puddle.MatchProg.value type
      let root ← Puddle.MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
      return (type, lhs, rhs, root.properties))
    (fun (type, lhs, rhs, props) => do
      let wideType ← Puddle.CreateProg.type (IntegerType.signless 64)
      let lhs ← Puddle.CreateProg.operation (.gmir .g_anyext) #[lhs] #[wideType]
      let rhs ← Puddle.CreateProg.operation (.gmir .g_anyext) #[rhs] #[wideType]
      let wordProps ← Puddle.CreateProg.applyNative props (fun props => some (cast h props))
      let word ← Puddle.CreateProg.operation (.gmir wordOpcode)
          #[lhs.res[0]!, rhs.res[0]!] #[wideType] (.inr wordProps)
      Puddle.CreateProg.operation (.gmir .g_trunc) #[word.res[0]!] #[type])
    (fun trunc => trunc)

/--
  Custom legalization of `i32` unary operations into their RISC-V word variant
  (`g_ctlz` -> `riscv.clzw`, `g_cttz` -> `riscv.ctzw`, `g_ctpop` -> `riscv.cpopw`). For `g_ctlz`
  and `g_cttz`, LLVM custom-legalizes into `RISCV::G_CLZW` and `RISCV::G_CTZW`.
-/
def customLegalizeWordUnary (opcode : GMIR) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Puddle.Pattern OpCode :=
  lowerUnary (.gmir opcode) 32 riscvOp riscvProps

section
open Puddle in

/--
  Custom legalization of the `i8` `g_bitreverse` into `g_brev8`, which reverses the bits of each
  byte (Zbkb), as LLVM's `RISCVLegalizerInfo::legalizeBitreverse`.
-/
def customLegalizeBitreverse8 : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 8)
      let src ← MatchProg.value type
      let _ ← MatchProg.root (.gmir .g_bitreverse) #[src] #[type]
      return (type, src))
    (fun (type, src) => do
      let wideType ← CreateProg.type (IntegerType.signless 64)
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[wideType]
      let brev8 ← CreateProg.operation (.gmir .g_brev8) #[ext.res[0]!] #[wideType]
      CreateProg.operation (.gmir .g_trunc) #[brev8.res[0]!] #[type])
    (fun op => op)

open Puddle in
/--
  Custom legalization of the `i64` `g_abs` into `g_smax x (0 - x)` (Zbb), as LLVM's
  `LegalizerHelper::lowerAbsToMaxNeg`. The negation of the minimum value wraps back to it, which
  is then its own absolute value.
-/
def customLegalizeAbs : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let src ← MatchProg.value type
      let _ ← MatchProg.root (.gmir .g_abs) #[src] #[type]
      return (type, src))
    (fun (type, src) => do
      let zero ← createConstant type 0
      let neg ← CreateProg.operation (.gmir .g_sub) #[zero.res[0]!, src] #[type]
      CreateProg.operation (.gmir .g_smax) #[src, neg.res[0]!] #[type])
    (fun op => op)

end

private def s8 : LLT := .scalar 8
private def s16 : LLT := .scalar 16
private def s32 : LLT := .scalar 32
private def s64 : LLT := .scalar 64
private def p0 : LLT := .pointer 0

public section

def riscv64LegalizerInfo : LegalizerInfo where
  rules
    | .g_addw | .g_subw | .g_mulw | .g_sdivw | .g_udivw | .g_uremw
    | .g_shlw | .g_lshrw | .g_ashrw => [.legalFor [s64]]
    | .g_add | .g_sub => [
      .legalFor [s64],
      .customFor [s32],
      .minScalar (.type 0) 64,
    ]
    | .g_shl | .g_lshr | .g_ashr => [
      .legalForTypePairs [(s64, s64)],
      -- TODO: Widen shifts by a constant instead once shifts by an immediate are also selected.
      .customForTypePairs [(s32, s32)],
      .minScalar (.type 1) 64,
      .minScalar (.type 0) 64,
    ]
    | .g_icmp => [
      .legalForTypePairs [(s64, s64), (s64, p0)],
      .minScalar (.type 1) 64,
      .minScalar (.type 0) 64,
    ]
    -- LLVM is also legal for `s32`, for floating point, and for `p0`, which `g_select` does not
    -- accept yet.
    | .g_select => [
      .legalForTypePairs [(s64, s64)],
      .minScalar (.type 0) 64,
      .minScalar (.type 1) 64,
    ]
    | .g_anyext => [
      .alwaysLegal,
    ]
    | .g_sext => [
      .legalForTypePairs [(s32, s16), (s64, s16), (s64, s32)],
      -- In LLVM, other extensions never reach these rules: their operands are always the result
      -- of a `g_trunc`, and the artifact combiner turns them into `g_sext_inreg`. Here, the
      -- operands can also be e.g. block arguments, so we lower them to `g_sext_inreg` instead.
      .lowerIf fun query => match query.getLLT! (.type 0) with
        | .scalar dst => dst ≤ 64
        | _ => false,
    ]
    | .g_zext => [
      .legalForTypePairs [(s32, s16), (s64, s16), (s64, s32)],
      -- As for `g_sext`, we lower other extensions to what LLVM's artifact combiner turns them
      -- into, here a `g_and` with the mask of the source width.
      .lowerIf fun query => match query.getLLT! (.type 0) with
        | .scalar dst => dst ≤ 64
        | _ => false,
    ]
    | .g_sext_inreg => [
      .legalFor [s64],
      .minScalar (.type 0) 64,
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
    -- LLVM has no `s32` rule for `g_ctpop`: it widens it to a `g_ctpop` of a `g_zext`, and selects
    -- that into `cpopw` with a pattern. We custom-legalize it like `g_ctlz` and `g_cttz` instead.
    | .g_ctlz | .g_cttz | .g_ctpop => [
      .legalForTypePairs [(s64, s64)],
      .customForTypePairs [(s32, s32)],
      .minScalar (.type 0) 32,
      .widenScalarToNextPow2 (.type 0),
      .scalarSameSizeAs (.type 1) (.type 0),
    ]
    -- As in LLVM, these are lowered to `g_ctlz` and `g_cttz`.
    | .g_ctlz_zero_poison | .g_cttz_zero_poison => [
      .lower,
    ]
    | .g_bswap => [
      .legalFor [s64],
      .minScalar (.type 0) 64,
    ]
    | .g_bitreverse => [
      .customFor [s8],
      -- LLVM lowers the other widths into a `g_bswap` and shifts and masks that swap the bits
      -- within each byte. Like LLVM's SelectionDAG with Zbkb, we select `brev8` and `rev8`
      -- instead, which is what that lowering computes.
      .legalFor [s64],
      .minScalar (.type 0) 64,
    ]
    | .g_brev8 => [
      .legalFor [s64],
    ]
    | .g_smin | .g_smax | .g_umin | .g_umax => [
      .legalFor [s64],
      .minScalar (.type 0) 64,
    ]
    | .g_abs => [
      .customFor [s64],
      .minScalar (.type 0) 64,
    ]
    | .g_constant => [
      -- LLVM's custom `i64` rule only decides on the constant pool, which we don't need.
      .legalFor [s64],
      .minScalar (.type 0) 64,
    ]
    | .g_br => [
      .alwaysLegal,
    ]
    | .g_brcond => [
      .legalFor [s64],
      .minScalar (.type 0) 64,
    ]
    | _ => []
  legalizeCustom
    | .g_add => customLegalizeWord .g_add .g_addw rfl
    | .g_sub => customLegalizeWord .g_sub .g_subw rfl
    | .g_mul => customLegalizeWord .g_mul .g_mulw rfl
    | .g_sdiv => customLegalizeWord .g_sdiv .g_sdivw rfl
    | .g_udiv => customLegalizeWord .g_udiv .g_udivw rfl
    | .g_urem => customLegalizeWord .g_urem .g_uremw rfl
    | .g_shl => customLegalizeWord .g_shl .g_shlw rfl
    | .g_lshr => customLegalizeWord .g_lshr .g_lshrw rfl
    | .g_ashr => customLegalizeWord .g_ashr .g_ashrw rfl
    | .g_ctlz => customLegalizeWordUnary .g_ctlz .clzw ()
    | .g_cttz => customLegalizeWordUnary .g_cttz .ctzw ()
    | .g_ctpop => customLegalizeWordUnary .g_ctpop .cpopw ()
    | .g_bitreverse => customLegalizeBitreverse8
    | .g_abs => customLegalizeAbs
    | _ => none

def LegalizeRISCV64Pass : Pass OpCode :=
  { name := "legalize-riscv64"
    description := "Legalize gMIR operations for RISC-V 64."
    run := fun _ ctx _ _ => riscv64LegalizerInfo.legalize ctx }

end

end Veir
