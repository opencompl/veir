import Veir.PatternRewriter.Basic

namespace Veir.Transforms.ModArith

private def natBitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

def barretReduceRewriter : LocalRewritePattern := fun ctx op => do
  let .mod_arith_barrett_reduce := (op.get! ctx).opType
    | some (ctx, none)

  let input := op.getOperand! ctx 0
  let inputType := input.getType! ctx
  let .integerType inputIntType := inputType.val
    | some (ctx, none)

  let modulus := (op.getProperties! ctx .mod_arith_barrett_reduce).modulus.value
  if modulus <= 1 then
    return (ctx, none)

  -- Scalar integer-only lowering from HEIR's ConvertBarrettReduce.
  let bitWidth := natBitLength (Int.toNat (modulus - 1))
  if bitWidth = 0 then
    return (ctx, none)

  let interBitWidth := 3 * bitWidth
  let shiftAmount := 2 * bitWidth

  let modNat := Int.toNat modulus
  let bNat := (2 : Nat) ^ shiftAmount
  let ratioNat := bNat / modNat
  let modTruncNat := modNat % ((2 : Nat) ^ interBitWidth)

  let interType := IntegerType.mk interBitWidth
  let ratioProps := ArithConstantProperties.mk (IntegerAttr.mk (Int.ofNat ratioNat) interType)
  let shiftProps := ArithConstantProperties.mk (IntegerAttr.mk (Int.ofNat shiftAmount) interType)
  let modProps := ArithConstantProperties.mk (IntegerAttr.mk (Int.ofNat modTruncNat) interType)

  let (ctx, ratioOp) ← Rewriter.createOp ctx .arith_constant #[interType] #[] #[] #[] ratioProps none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  let (ctx, shiftOp) ← Rewriter.createOp ctx .arith_constant #[interType] #[] #[] #[] shiftProps none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  let (ctx, modOp) ← Rewriter.createOp ctx .arith_constant #[interType] #[] #[] #[] modProps none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)

  let (ctx, extOp) ← Rewriter.createOp ctx .arith_extui #[interType] #[input] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)

  let extRes := extOp.getResult 0
  let ratioRes := ratioOp.getResult 0
  let shiftRes := shiftOp.getResult 0
  let modRes := modOp.getResult 0

  let (ctx, mulRatioOp) ← Rewriter.createOp ctx .arith_muli #[interType] #[extRes, ratioRes] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  let (ctx, shiftedOp) ← Rewriter.createOp ctx .arith_shrui #[interType] #[mulRatioOp.getResult 0, shiftRes] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  let (ctx, mulModOp) ← Rewriter.createOp ctx .arith_muli #[interType] #[shiftedOp.getResult 0, modRes] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  let (ctx, subOp) ← Rewriter.createOp ctx .arith_subi #[interType] #[extRes, mulModOp.getResult 0] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  let (ctx, truncOp) ← Rewriter.createOp ctx .arith_trunci #[inputIntType] #[subOp.getResult 0] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)

  let newOps := #[
    ratioOp,
    shiftOp,
    modOp,
    extOp,
    mulRatioOp,
    shiftedOp,
    mulModOp,
    subOp,
    truncOp
  ]

  some (ctx, some (newOps, #[truncOp.getResult 0]))

def barretReduceRewriterPattern : RewritePattern := Veir.RewritePattern.fromLocalRewrite barretReduceRewriter

end Veir.Transforms.ModArith
