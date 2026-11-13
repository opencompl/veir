module

public import Veir.Pass
public import Veir.Passes.Legalization.LegalizerInfo
import Veir.Passes.Legalization.Legalizer
import Veir.Passes.Legalization.LegalizerHelper

/-!
# RISC-V 64 Legalization

This file implements the legalization pass for RISC-V 64.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVLegalizerInfo.cpp
-/

namespace Veir

/--
  Custom legalization of an `i32` binary operation into the word operation `wordOpcode` (LLVM's
  `RISCV::G_*`).
-/
def customLegalizeWordBinary (wordOpcode : GMIR_RISCV) : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := IntegerType) (·.bitwidth = 32)
      let lhs ← Puddle.MatchProg.value type
      let rhs ← Puddle.MatchProg.value type
      let _ ← Puddle.MatchProg.root (.gmir wordOpcode.base) #[lhs, rhs] #[type]
      return (type, lhs, rhs))
    (fun (type, lhs, rhs) => do
      let wideType ← Puddle.CreateProg.type (IntegerType.signless 64)
      let lhs ← Puddle.CreateProg.operation (.gmir .g_anyext) #[lhs] #[wideType]
      let rhs ← Puddle.CreateProg.operation (.gmir .g_anyext) #[rhs] #[wideType]
      let word ← Puddle.CreateProg.operation (.gmir_riscv wordOpcode)
          #[lhs.res[0]!, rhs.res[0]!] #[wideType]
      Puddle.CreateProg.operation (.gmir .g_trunc) #[word.res[0]!] #[type])
    (fun trunc => trunc)

/--
  Custom legalization of an `i32` unary operation into the word operation `wordOpcode` (LLVM's
  `RISCV::G_CLZW`/`G_CTZW`).
-/
def customLegalizeWordUnary (wordOpcode : GMIR_RISCV) : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := IntegerType) (·.bitwidth = 32)
      let x ← Puddle.MatchProg.value type
      let _ ← Puddle.MatchProg.root (.gmir wordOpcode.base) #[x] #[type]
      return (type, x))
    (fun (type, x) => do
      let wideType ← Puddle.CreateProg.type (IntegerType.signless 64)
      let x ← Puddle.CreateProg.operation (.gmir .g_anyext) #[x] #[wideType]
      let word ← Puddle.CreateProg.operation (.gmir_riscv wordOpcode) #[x.res[0]!] #[wideType]
      Puddle.CreateProg.operation (.gmir .g_trunc) #[word.res[0]!] #[type])
    (fun trunc => trunc)

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
  -- LLVM also makes `s32` legal, to place 32-bit floats in 32-bit float registers. An integer
  -- `s32` is later placed in a 64-bit GPR by instruction selection, which leaves the upper bits
  -- unspecified as `g_anyext` does.
  blockArgumentRules := [
    .legalFor [p0, s64],
    .clampScalar (.type 0) 64 64,
  ]
  rules
    | .g_add | .g_sub => [
      .legalFor [s64],
      -- LLVM custom-legalizes `s32` into the `s64` operation and a `G_SEXT_INREG` of 32 bits, and
      -- selects `addw`/`subw` later (see `GMIR_RISCV`).
      .customFor [s32],
      .widenScalarToNextPow2 (.type 0),
      .clampScalar (.type 0) 64 64,
    ]
    | .g_uadde | .g_usube => [
      .lower,
    ]
    | .g_shl | .g_lshr | .g_ashr => [
      .legalForTypePairs [(s64, s64)],
      -- Unlike LLVM, which widens a shift by a constant, we also use a word shift for it.
      .customForTypePairs [(s32, s32)],
      .minScalar (.type 1) 64,
      .minScalar (.type 0) 64,
    ]
    | .g_icmp => [
      .legalForTypePairs [(s64, s64), (s64, p0)],
      .minScalar (.type 1) 64,
      .minScalar (.type 0) 64,
    ]
    -- As in LLVM's RISCVLegalizerInfo, lower to comparisons and boolean arithmetic.
    | .g_scmp | .g_ucmp => [
      .lower,
    ]
    -- LLVM is also legal for `s32` and for floating point.
    | .g_select => [
      .legalForTypePairs [(s64, s64), (p0, s64)],
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
      -- LLVM widens `s32` to `s64`, and selects `mulw` later (see `GMIR_RISCV`).
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
    | .g_ctlz | .g_cttz => [
      .legalForTypePairs [(s64, s64)],
      .customForTypePairs [(s32, s32)],
      .minScalar (.type 0) 32,
      .widenScalarToNextPow2 (.type 0),
      .scalarSameSizeAs (.type 1) (.type 0),
    ]
    -- As in LLVM, there is no word variant of `g_ctpop`: it is widened to a `g_ctpop` of a
    -- `g_zext`, which instruction selection selects into `cpopw`.
    | .g_ctpop => [
      .legalForTypePairs [(s64, s64)],
      .minScalar (.type 0) 64,
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
    -- min and max are legal only for `s64` (Zbb), and the other types are custom
    -- legalized with `lowerAddSubSatToAddoSubo`, as in LLVM
    | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat => [
      .lowerIf (.typeIs (.type 0) s64),
      .customIf fun _ => true,
    ]
    -- As in LLVM, these are always lowered.
    | .g_sshlsat | .g_ushlsat => [
      .lower,
    ]
    -- As in LLVM, these are lowered to the wrapping operation and comparisons.
    | .g_uaddo | .g_usubo => [
      .lower,
    ]
    -- As in LLVM, these are widened first, where the overflow is a comparison of the wide result,
    -- and lowered at `s64`.
    | .g_saddo | .g_ssubo => [
      .minScalar (.type 0) 64,
      .lower,
    ]
    -- As in LLVM, funnel shifts are lowered to shifts. The amount is widened first, so that the
    -- width of the shifted values fits in it.
    | .g_fshl | .g_fshr => [
      .scalarSameSizeAs (.type 1) (.type 0),
      .lowerIf (.scalarNarrowerThan (.type 0) 64),
    ]
    | .g_constant => [
      -- LLVM's custom `i64` rule only decides on the constant pool, which we don't need.
      .legalFor [s64],
      .minScalar (.type 0) 64,
    ]
    | .g_poison => [
      .legalFor [s64, p0],
      .minScalar (.type 0) 64,
    ]
    | .g_freeze => [
      .legalFor [s64],
      .minScalar (.type 0) 64,
    ]
    -- Loads must be naturally aligned, as in LLVM without `+unaligned-scalar-mem`. LLVM also makes
    -- `s16` and `s32` legal, for `flh`/`flw` We have no FPs, so we widen to `s64`.
    -- TODO: Split odd-sized and misaligned loads, as LLVM's `lowerIfMemSizeNotByteSizePow2` and
    -- `lower`.
    | .g_load => [
      .legalForTypesWithMemDesc [⟨s64, p0, 8, 8⟩, ⟨s64, p0, 16, 16⟩, ⟨s64, p0, 32, 32⟩,
        ⟨s64, p0, 64, 64⟩, ⟨p0, p0, 64, 64⟩],
      .widenScalarToNextPow2 (.type 0),
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
    | .g_add => customLegalizeWordBinary .g_addw
    | .g_sub => customLegalizeWordBinary .g_subw
    | .g_mul => customLegalizeWordBinary .g_mulw
    | .g_sdiv => customLegalizeWordBinary .g_divw
    | .g_udiv => customLegalizeWordBinary .g_divuw
    | .g_urem => customLegalizeWordBinary .g_remuw
    | .g_shl => customLegalizeWordBinary .g_sllw
    | .g_lshr => customLegalizeWordBinary .g_srlw
    | .g_ashr => customLegalizeWordBinary .g_sraw
    | .g_ctlz => customLegalizeWordUnary .g_clzw
    | .g_cttz => customLegalizeWordUnary .g_ctzw
    | .g_bitreverse => customLegalizeBitreverse8
    | .g_abs => customLegalizeAbs
    | .g_uaddsat => lowerAddSubSatToAddoSubo .g_uaddsat false true
    | .g_usubsat => lowerAddSubSatToAddoSubo .g_usubsat false false
    | .g_saddsat => lowerAddSubSatToAddoSubo .g_saddsat true true
    | .g_ssubsat => lowerAddSubSatToAddoSubo .g_ssubsat true false
    | _ => none

def LegalizeRISCV64Pass : Pass OpCode :=
  { name := "legalize-riscv64"
    description := "Legalize gMIR operations for RISC-V 64."
    run := fun _ ctx op _ => riscv64LegalizerInfo.legalize ctx op }

end

end Veir
