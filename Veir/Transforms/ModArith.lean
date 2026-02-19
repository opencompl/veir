import Veir.PatternRewriter.Basic
import Veir.PatternRewriter.Lemmas
open Veir.PatternRewriter

namespace Veir.Transforms.ModArith

private def natBitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

private def integerTypeOf? (type : TypeAttr) : Option IntegerType :=
  match type.val with
  | .integerType intType => some intType
  | _ => none

private def modArithTypeOf? (type : TypeAttr) : Option ModArithType :=
  match type.val with
  | .modArithType modType => some modType
  | _ => none

private def modulusFromReduceTypes? (inputType resultType : TypeAttr) : Option Int :=
  (modArithTypeOf? resultType).map (·.modulus) <|>
    (modArithTypeOf? inputType).map (·.modulus)

private def modulusTypeFromReduceTypes? (inputType resultType : TypeAttr) : Option IntegerType :=
  (modArithTypeOf? resultType).bind (·.modulusType) <|>
    (modArithTypeOf? inputType).bind (·.modulusType)

private def defaultIntTypeForModulus (modulus : Int) : IntegerType :=
  let bitWidth := natBitLength (Int.toNat (Int.natAbs modulus))
  IntegerType.mk (if bitWidth = 0 then 1 else bitWidth)

private def chooseReduceWorkType (inputType resultType : TypeAttr) (modulus : Int) : IntegerType :=
  match integerTypeOf? inputType with
  | some intType => intType
  | none =>
    match integerTypeOf? resultType with
    | some intType => intType
    | none => (modulusTypeFromReduceTypes? inputType resultType).getD (defaultIntTypeForModulus modulus)

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

def subIfGeRewriter : LocalRewritePattern := fun ctx op => do
  let .mod_arith_subifge := (op.get! ctx).opType
    | some (ctx, none)

  let lhs := op.getOperand! ctx 0
  let rhs := op.getOperand! ctx 1
  let lhsType := lhs.getType! ctx
  let rhsType := rhs.getType! ctx
  let resultType := (op.getResult 0 : ValuePtr).getType! ctx

  let .integerType intType := lhsType.val
    | some (ctx, none)
  if rhsType ≠ lhsType then
    return (ctx, none)
  if resultType ≠ lhsType then
    return (ctx, none)

  let cmpType := IntegerType.mk 1
  let (ctx, subOp) ← Rewriter.createOp ctx .arith_subi #[intType] #[lhs, rhs] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  let (ctx, cmpOp) ← Rewriter.createOp ctx .arith_cmpi #[cmpType] #[lhs, rhs] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  let (ctx, selectOp) ← Rewriter.createOp ctx .arith_select #[intType]
    #[cmpOp.getResult 0, subOp.getResult 0, lhs] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)

  let newOps := #[
    subOp,
    cmpOp,
    selectOp
  ]

  some (ctx, some (newOps, #[selectOp.getResult 0]))

def reduceRewriter : LocalRewritePattern := fun ctx op => do
  let .mod_arith_reduce := (op.get! ctx).opType
    | some (ctx, none)

  let input := op.getOperand! ctx 0
  let inputType := input.getType! ctx
  let resultType := (op.getResult 0 : ValuePtr).getType! ctx

  let some modulus := modulusFromReduceTypes? inputType resultType
    | return (ctx, none)
  if modulus <= 1 then
    return (ctx, none)

  let workIntType := chooseReduceWorkType inputType resultType modulus
  let modulusAttrType := (modulusTypeFromReduceTypes? inputType resultType).getD (IntegerType.mk 64)
  let modulusProps := ModArithBarrettReduceProperties.mk (IntegerAttr.mk modulus modulusAttrType)
  let modulusConstProps := ArithConstantProperties.mk (IntegerAttr.mk modulus workIntType)

  let mut ctx := ctx
  let mut newOps : Array OperationPtr := #[]
  let mut inputInt : ValuePtr := input

  match inputType.val with
  | .integerType _ =>
    pure ()
  | .modArithType _ =>
    let (ctx', extractOp) ← Rewriter.createOp ctx .mod_arith_extract #[workIntType] #[input] #[] #[] () none
      (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
    ctx := ctx'
    inputInt := extractOp.getResult 0
    newOps := newOps.push extractOp
  | _ =>
    return (ctx, none)

  let (ctx', barrettOp) ← Rewriter.createOp ctx .mod_arith_barrett_reduce #[workIntType] #[inputInt] #[] #[] modulusProps none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  ctx := ctx'
  newOps := newOps.push barrettOp

  let (ctx', modulusOp) ← Rewriter.createOp ctx .arith_constant #[workIntType] #[] #[] #[] modulusConstProps none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  ctx := ctx'
  newOps := newOps.push modulusOp

  let (ctx', subIfGeOp) ← Rewriter.createOp ctx .mod_arith_subifge #[workIntType]
    #[barrettOp.getResult 0, modulusOp.getResult 0] #[] #[] () none
    (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  ctx := ctx'
  newOps := newOps.push subIfGeOp

  let mut loweredValue : ValuePtr := subIfGeOp.getResult 0

  match resultType.val with
  | .integerType resultIntType =>
    if resultIntType = workIntType then
      pure ()
    else if resultIntType.bitwidth < workIntType.bitwidth then
      let (ctx', truncOp) ← Rewriter.createOp ctx .arith_trunci #[resultIntType] #[loweredValue] #[] #[] () none
        (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
      ctx := ctx'
      loweredValue := truncOp.getResult 0
      newOps := newOps.push truncOp
    else
      let (ctx', extOp) ← Rewriter.createOp ctx .arith_extui #[resultIntType] #[loweredValue] #[] #[] () none
        (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
      ctx := ctx'
      loweredValue := extOp.getResult 0
      newOps := newOps.push extOp
  | .modArithType _ =>
    let (ctx', encapsulateOp) ← Rewriter.createOp ctx .mod_arith_encapsulate #[resultType] #[loweredValue] #[] #[] () none
      (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
    ctx := ctx'
    loweredValue := encapsulateOp.getResult 0
    newOps := newOps.push encapsulateOp
  | _ =>
    return (ctx, none)

  some (ctx, some (newOps, #[loweredValue]))

def barretReduceRewriterPattern : RewritePattern := Veir.RewritePattern.fromLocalRewrite barretReduceRewriter
def subIfGeRewriterPattern : RewritePattern := Veir.RewritePattern.fromLocalRewrite subIfGeRewriter
def reduceRewriterPattern : RewritePattern := Veir.RewritePattern.fromLocalRewrite reduceRewriter

theorem barretReduceRewriterPreservesSemantics : LocalRewritePattern.PreservesSemantics barretReduceRewriter := by
  intro ctx op opIn newCtx newOps newValue hpattern
  intro state newState hinterp
  let oldValue := newState.variables[ValuePtr.opResult (op.getResult 0)]!
  simp [barretReduceRewriter] at hpattern
  split at hpattern; rotate_left; grind
  split at hpattern; rotate_left; grind
  split at hpattern; grind
  split at hpattern; grind
  simp only [Option.bind_eq_some_iff] at hpattern
  have ⟨firstOp, ⟨hfirst, hpattern⟩⟩ := hpattern

end Veir.Transforms.ModArith
