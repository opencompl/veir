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
Combines `g_unmerge_values (g_merge_values lo hi)` to `lo` and `hi`, as LLVM's
`tryCombineUnmergeValues` does.
-/
def combineUnmergeOfMerge : Pattern OpCode :=
  Pattern.Builder
    (do
      let halfType ← MatchProg.type (Attr := IntegerType)
      let lo ← MatchProg.value halfType
      let hi ← MatchProg.value halfType
      let type ← MatchProg.type (Attr := IntegerType)
      let merge ← MatchProg.operation (.gmir .g_merge_values) #[lo, hi] #[type]
      let _ ← MatchProg.root (.gmir .g_unmerge_values) #[merge.res[0]!] #[halfType, halfType]
      return #[lo, hi])
    pure
    (fun halves => halves)

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
  | .g_trunc => [combineTruncOfTrunc]
  | .g_unmerge_values => [combineUnmergeOfMerge]
  | _ => []

end

end Veir
