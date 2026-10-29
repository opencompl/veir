module

public import Veir.PatternRewriter.Puddle.Definitions
import Veir.PatternRewriter.Puddle.Builders

/-!
# Legalization Artifact Combiner

This file implements, as Puddle patterns, the combines that clean up artifacts such as `g_trunc` and
`g_[zsa]ext`, which legalization creates to make the types match.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/LegalizationArtifactCombiner.h
-/

namespace Veir

open Puddle

/--
Matches `g_anyext (g_trunc x)` where the type of `x` and the result type satisfy `relation`.
Returns `x` and the result type.
-/
def matchAnyExtOfTrunc (relation : IntegerType → IntegerType → Bool) :
    MatchProg.Builder (Handle OpCode .value × Handle OpCode .type) := do
  let srcType ← MatchProg.type (Attr := IntegerType)
  let x ← MatchProg.value srcType
  let narrowType ← MatchProg.type (Attr := IntegerType)
  let trunc ← MatchProg.operation (.gmir .g_trunc) #[x] #[narrowType]
  let type ← MatchProg.type (Attr := IntegerType)
  MatchProg.matchNative (srcType, type) fun (srcType, type) =>
    match srcType.val, type.val with
    | .integerType srcType, .integerType type => relation srcType type
    | _, _ => false
  let _ ← MatchProg.root (.gmir .g_anyext) #[trunc.res[0]!] #[type]
  return (x, type)

/-- Combines `g_anyext (g_trunc x)` to `x` when both have the same type. -/
def combineAnyExtOfTruncSame : Pattern OpCode :=
  Pattern.Builder (matchAnyExtOfTrunc (· = ·)) pure (fun (x, _) => x)

/--
Combines `g_anyext (g_trunc x)` to `castOpcode x` when the type of `x` and the result type satisfy
`relation`, as LLVM's `buildAnyExtOrTrunc`.
-/
def combineAnyExtOfTruncToCast (castOpcode : GMIR) (relation : IntegerType → IntegerType → Bool) :
    Pattern OpCode :=
  Pattern.Builder (matchAnyExtOfTrunc relation)
    (fun (x, type) => do
      let props ← CreateProg.property (.gmir castOpcode) default
      CreateProg.operation (.gmir castOpcode) #[x] #[type] props)
    (fun cast => cast)

/-- Combines `g_anyext (g_anyext x)` to `g_anyext x`, as LLVM's `tryCombineAnyExt` does. -/
def combineAnyExtOfAnyExt : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcType
      let midType ← MatchProg.type (Attr := IntegerType)
      let inner ← MatchProg.operation (.gmir .g_anyext) #[x] #[midType]
      let type ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.root (.gmir .g_anyext) #[inner.res[0]!] #[type]
      return (x, type))
    (fun (x, type) => CreateProg.operation (.gmir .g_anyext) #[x] #[type])
    (fun ext => ext)

/--
Combines `g_zext (g_trunc (g_icmp lhs rhs))` to the `g_icmp` when it has the type of the `g_zext`.
A `g_icmp` yields 0 or 1, so truncating it and zero-extending it back keeps its value. LLVM's
`tryCombineZExt` finds this with known bits, which we do not have.
-/
def combineZExtOfTruncOfICmp : Pattern OpCode :=
  Pattern.Builder
    (do
      let operandType ← MatchProg.type (Attr := TypeAttr)
      let lhs ← MatchProg.value operandType
      let rhs ← MatchProg.value operandType
      let wideType ← MatchProg.type (Attr := IntegerType)
      let icmp ← MatchProg.operation (.gmir .g_icmp) #[lhs, rhs] #[wideType]
      let narrowType ← MatchProg.type (Attr := IntegerType)
      let trunc ← MatchProg.operation (.gmir .g_trunc) #[icmp.res[0]!] #[narrowType]
      let type ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative (wideType, type) fun (wideType, type) =>
        match wideType.val, type.val with
        | .integerType wideType, .integerType type => wideType = type
        | _, _ => false
      let _ ← MatchProg.root (.gmir .g_zext) #[trunc.res[0]!] #[type]
      return icmp.res[0]!)
    pure (fun x => x)

/--
Combines `g_trunc (g_trunc x)` to `g_trunc x`. As in LLVM, the new `g_trunc` has no flags.
-/
def combineTruncOfTrunc : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcType
      let midType ← MatchProg.type (Attr := IntegerType)
      let inner ← MatchProg.operation (.gmir .g_trunc) #[x] #[midType]
      let type ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.root (.gmir .g_trunc) #[inner.res[0]!] #[type]
      return (x, type))
    (fun (x, type) => CreateProg.operation (.gmir .g_trunc) #[x] #[type])
    (fun trunc => trunc)

/--
Combines `ext (g_trunc c)` (when `throughTrunc` is set) or `ext c`, for `ext` ∈ {`g_sext`, `g_zext`}
and a `g_constant` `c`, to the `g_constant` of the extension: the value of the `g_trunc` (or of `c`)
read as a signed (`signed`) or unsigned integer. Legalization widens a narrow `g_constant` to a
wide one and a `g_trunc`, and the `g_sext`/`g_zext` of it remains where its high bits matter, e.g.
as a `g_icmp` operand. As the folds of constant sources in LLVM's `tryCombineSExt` and
`tryCombineZExt`. The folded constant refines the poison of a `g_trunc` or `g_zext` flag.
-/
def combineExtOfConstant (ext : GMIR) (signed throughTrunc : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let constType ← MatchProg.type (Attr := IntegerType)
      let c ← MatchProg.operation (.gmir .g_constant) #[] #[constType]
      let (src, srcType) ← if throughTrunc then do
          let narrowType ← MatchProg.type (Attr := IntegerType)
          let trunc ← MatchProg.operation (.gmir .g_trunc) #[c.res[0]!] #[narrowType]
          pure (trunc.res[0]!, narrowType)
        else pure (c.res[0]!, constType)
      let type ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.root (.gmir ext) #[src] #[type]
      return (type, srcType, c.properties))
    (fun (type, srcType, c) => do
      let props ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_constant)))
          (type, srcType, c) fun (type, srcType, c) => do
            let .integerType type := type.val | none
            let .integerType srcType := srcType.val | none
            let bits := BitVec.ofInt srcType.bitwidth c.value.value
            return { value := .ofInt (if signed then bits.toInt else bits.toNat) type }
      CreateProg.operation (.gmir .g_constant) #[] #[type] props)
    (fun c => c)

public section

/--
The patterns that combine an `opcode` artifact away, in the order they are tried, as in LLVM's
`LegalizationArtifactCombiner::tryCombineInstruction`.
-/
def tryCombineInstruction : GMIR → List (Pattern OpCode)
  | .g_anyext => [
      combineAnyExtOfTruncSame,
      combineAnyExtOfTruncToCast .g_trunc (·.bitwidth > ·.bitwidth),
      combineAnyExtOfTruncToCast .g_anyext (·.bitwidth < ·.bitwidth),
      combineAnyExtOfAnyExt]
  | .g_zext => [combineZExtOfTruncOfICmp,
      combineExtOfConstant .g_zext false true, combineExtOfConstant .g_zext false false]
  | .g_sext => [combineExtOfConstant .g_sext true true, combineExtOfConstant .g_sext true false]
  | .g_trunc => [combineTruncOfTrunc]
  | _ => []

end

end Veir
