module

public import Veir.Passes.Legalization.LegalizerInfo
public import Veir.PatternRewriter.Puddle.Execution
import Veir.PatternRewriter.Puddle.Builders

/-!
# Combines

This file implements the target-independent gMIR combines as Puddle patterns. The combines that
depend on the legality of operations take the `LegalizerInfo` of the target. LLVM's
`commute_constant_to_rhs` is the canonicalizer's `commutativeConstantRHS`.

TODO: Add the other combines of LLVM's `RISCVPostLegalizerCombiner` (`combines_for_extload`,
`redundant_and`, `identity_combines`, `shift_immed_chain` and `simplify_neg_minmax`).

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/CodeGen/GlobalISel/CombinerHelper.cpp
-/

namespace Veir

open Puddle

public section

/-! ### sub_to_add : (sub x, C) → (add x, -C) -/

/--
`g_sub x, C` becomes `g_add x, -C` if `g_add` and `g_constant` are legal for the type. As in LLVM,
the result drops `nuw`, and drops `nsw` when `C` is the minimum signed value.

https://github.com/llvm/llvm-project/blob/bcb89020f2953e414ff525cbf04e9c35be50ece4/llvm/include/llvm/Target/GlobalISel/Combine.td#L397-L403
https://github.com/llvm/llvm-project/blob/bcb89020f2953e414ff525cbf04e9c35be50ece4/llvm/lib/CodeGen/GlobalISel/CombinerHelper.cpp#L2209
-/
def sub_to_add_pattern (info : LegalizerInfo) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let constant ← MatchProg.operation (.gmir .g_constant) #[] #[type]
      let root ← MatchProg.root (.gmir .g_sub) #[x, constant.res[0]!] #[type]
      MatchProg.matchNative (type, constant.properties) fun (ty, props) =>
        info.isLegal .g_add #[ty] { nsw := false, nuw := false } &&
          info.isLegal .g_constant #[ty] props.neg
      return (type, x, constant.properties, root.properties))
    (fun (type, x, constantProps, subProps) => do
      let negProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.gmir .g_constant))) constantProps
          fun props => some props.neg
      let negOp ← CreateProg.operation (.gmir .g_constant) #[] #[type] negProps
      -- `x - C` and `x + -C` wrap as signed integers in the same cases, unless `C` is the
      -- minimum signed value, which is its own negation. As unsigned integers, a nonzero `C`
      -- negates to the large value `2^n - C`, so `x + -C` wraps whenever `x - C` does not, and
      -- `nuw` is dropped.
      let addProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.gmir .g_add))) (constantProps, subProps)
          fun (constant, sub) => some { nsw := sub.nsw && !constant.isMinSigned, nuw := false }
      CreateProg.operation (.gmir .g_add) #[x, negOp.res[0]!] #[type] addProps)
    (fun addOp => addOp)

def sub_to_add (info : LegalizerInfo) : CompiledPattern OpCode := (sub_to_add_pattern info).compile

/-! ### redundant_and of a comparison : (and (icmp p x y), 1) → (icmp p x y) -/

/--
`g_and (g_icmp p x y), 1` becomes `g_icmp p x y`: a comparison is zero or one, on a target whose
booleans are zero or one, so masking it with one changes nothing. This is the case of LLVM's
`redundant_and` that needs no known-bits analysis. Legalization creates it when it zero-extends
the `i1` condition of a `g_select` that a widened `g_icmp` computes.

https://github.com/llvm/llvm-project/blob/bcb89020f2953e414ff525cbf04e9c35be50ece4/llvm/include/llvm/Target/GlobalISel/Combine.td#L611-L615
-/
def redundant_and_icmp_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let operandType ← MatchProg.type (Attr := TypeAttr)
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value operandType
      let y ← MatchProg.value operandType
      let cmp ← MatchProg.operation (.gmir .g_icmp) #[x, y] #[type]
      let one ← MatchProg.operation (.gmir .g_constant) #[] #[type]
      MatchProg.matchNative one.properties fun props =>
        BitVec.ofInt props.value.type.bitwidth props.value.value = 1
      let _ ← MatchProg.root (.gmir .g_and) #[cmp.res[0]!, one.res[0]!] #[type]
      return cmp.res[0]!)
    pure
    (fun cmp => cmp)

def redundant_and_icmp : CompiledPattern OpCode := redundant_and_icmp_pattern.compile

end

end Veir
