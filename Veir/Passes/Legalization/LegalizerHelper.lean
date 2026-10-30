module

public import Veir.PatternRewriter.Puddle.Definitions
public import Veir.PatternRewriter.Basic
public import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

/-!
# Legalization Actions

This file implements the legalization actions as Puddle patterns.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/LegalizerHelper.h
-/

namespace Veir

open Puddle

public section

/-- Create a `g_constant` of `type` whose value `value` computes from the metadata `inputs`. -/
def createConstantWith {Inputs : Type} [IsMetadataTuple OpCode Inputs]
    (type : Handle OpCode .type) (inputs : Inputs)
    (value : MetadataValues OpCode Inputs → Int) : CreateProg.Builder CreatedOpHandle := do
  let props ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_constant)))
      (type, inputs) fun (type, inputs) => do
        let .integerType type := type.val | none
        return { value := .ofInt (value inputs) type }
  CreateProg.operation (.gmir .g_constant) #[] #[type] props

/-- Create a `g_constant` of `type` with the value `value`. -/
def createConstant (type : Handle OpCode .type) (value : Int) :
    CreateProg.Builder CreatedOpHandle :=
  createConstantWith type () fun () => value

end

/--
Widens type group `typeIdx` of `opcode` to `width` bits. Its operands are extended with `extOpcode`
and its results are truncated back, as in LLVM's `LegalizerHelper::widenScalar`.
-/
def widenTypeGroup (opcode : GMIR) (typeIdx : TypeGroup) (extOpcode : GMIR) (width : Nat)
    (updateProps : propertiesOf (OpCode.gmir opcode) → propertiesOf (OpCode.gmir opcode) := id) :
    Pattern OpCode :=
  let info := opcode.genericOpInfo
  let matchType (group : TypeGroup) : MatchProg.Builder (Handle OpCode .type) :=
    if group = typeIdx then MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
    else MatchProg.type (Attr := TypeAttr)
  Pattern.Builder
    (do
      let operands ← info.inOperandList.mapM fun group => do MatchProg.value (← matchType group)
      let resultTypes ← info.outOperandList.mapM matchType
      let root ← MatchProg.root (.gmir opcode) operands resultTypes
      return (operands, resultTypes, root.properties))
    (fun (operands, resultTypes, props) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let wideOperands ← (info.inOperandList.zip operands).mapM fun (group, operand) => do
        if group ≠ typeIdx then return operand
        let ext ← CreateProg.operation (.gmir extOpcode) #[operand] #[wideType]
        return ext.res[0]!
      let wideResultTypes := (info.outOperandList.zip resultTypes).map fun (group, type) =>
        if group = typeIdx then wideType else type
      let wideProps ← CreateProg.applyNative props (some <| updateProps ·)
      let wide ← CreateProg.operation (.gmir opcode) wideOperands wideResultTypes (.inr wideProps)
      (info.outOperandList.zip (resultTypes.zip wide.res)).mapM fun (group, type, result) => do
        if group ≠ typeIdx then return result
        let trunc ← CreateProg.operation (.gmir .g_trunc) #[result] #[type]
        return trunc.res[0]!)
    (fun results => results)

/-- Clears the no-wrap flags, which no longer hold once the high bits are unconstrained. -/
-- NOTE: (for reviewers) we could also default construct to clear.
def clearNswNuwProperties (props : NswNuwProperties) : NswNuwProperties :=
  { props with nsw := false, nuw := false }

/-- Clears the disjoint flag, which no longer holds once the high bits are unconstrained. -/
def clearDisjointProperties (props : DisjointProperties) : DisjointProperties :=
  { props with disjoint := false }

/-- Widens `g_constant` to `width` bits and then truncates it back, extending the value as LLVM's
`LegalizerInfo::getExtOpcodeForWideningConstant` does. -/
def widenConstant (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let root ← MatchProg.root (.gmir .g_constant) #[] #[type]
      return (type, root))
    (fun (type, root) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let props ← CreateProg.applyNative root.properties fun ⟨⟨value, ⟨w, _⟩⟩⟩ =>
        let value := if w % 8 = 0 then value else (BitVec.ofInt w value).toNat
        some (GMIRConstantProperties.mk (.ofInt value (.signless width)))
      let wide ← CreateProg.operation (.gmir .g_constant) #[] #[wideType] (.inr props)
      CreateProg.operation (.gmir .g_trunc) #[wide.res[0]!] #[type])
    (fun trunc => trunc)

/-- Creates the `g_constant` `value srcWidth` of type `type`, where `srcWidth` is the width of the
integer type `srcType`. -/
private def widthConstant (srcType type : Handle OpCode .type) (value : Nat → Int) :
    CreateProg.Builder CreatedOpHandle :=
  createConstantWith type srcType fun srcType => value (srcType.cast? IntegerType).get!.bitwidth

/--
Widens the operand of `g_ctlz` to `width` bits. The operand is zero-extended, so the count is too
large by the number of added bits, which are subtracted from it, as in LLVM's
`LegalizerHelper::widenScalar`. The result must already be `width` bits wide, which the rules
ensure by widening it first.
-/
def widenCtlzSrc (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let resType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = width)
      let src ← MatchProg.value srcType
      let _ ← MatchProg.root (.gmir .g_ctlz) #[src] #[resType]
      return (srcType, resType, src))
    (fun (srcType, resType, src) => do
      let ext ← CreateProg.operation (.gmir .g_zext) #[src] #[resType]
      let ctlz ← CreateProg.operation (.gmir .g_ctlz) #[ext.res[0]!] #[resType]
      let diff ← widthConstant srcType resType (width - ·)
      -- The count of the wide operand is at least `diff`, so the subtraction does not wrap.
      let subProps ← CreateProg.property (.gmir .g_sub) (NswNuwProperties.mk false true)
      CreateProg.operation (.gmir .g_sub) #[ctlz.res[0]!, diff.res[0]!] #[resType] subProps)
    (fun op => op)

/--
Widens the operand of `g_cttz` to `width` bits. The bit just above the operand is set, so that
the count of a zero operand is still its width, as in LLVM's `LegalizerHelper::widenScalar`. The
wide operand is never zero, so it is counted with `g_cttz_zero_poison`, as in LLVM. The result
must already be `width` bits wide, which the rules ensure by widening it first.
-/
def widenCttzSrc (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let resType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = width)
      let src ← MatchProg.value srcType
      let _ ← MatchProg.root (.gmir .g_cttz) #[src] #[resType]
      return (srcType, resType, src))
    (fun (srcType, resType, src) => do
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[resType]
      let topBit ← widthConstant srcType resType (2 ^ ·)
      let wideSrc ← CreateProg.operation (.gmir .g_or) #[ext.res[0]!, topBit.res[0]!] #[resType]
      CreateProg.operation (.gmir .g_cttz_zero_poison) #[wideSrc.res[0]!] #[resType])
    (fun op => op)

/--
Widens `g_bswap` or `g_bitreverse` to `width` bits. The reversed operand ends up in the high
bits, so it is shifted back down before it is truncated, as in LLVM's `LegalizerHelper::widenScalar`.
-/
def widenReverse (opcode : GMIR) (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let src ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[src] #[type]
      return (type, src))
    (fun (type, src) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[wideType]
      let wide ← CreateProg.operation (.gmir opcode) #[ext.res[0]!] #[wideType]
      let diff ← widthConstant type wideType (width - ·)
      let shift ← CreateProg.operation (.gmir .g_lshr) #[wide.res[0]!, diff.res[0]!] #[wideType]
      CreateProg.operation (.gmir .g_trunc) #[shift.res[0]!] #[type])
    (fun op => op)

/-- Lowers the count `opcode`, whose zero input is poison, to the count `defined`, which is defined
at zero and refines it, as in LLVM's `LegalizerHelper::lowerBitCount`. -/
def lowerZeroPoisonCount (opcode defined : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType)
      let src ← MatchProg.value srcType
      let _ ← MatchProg.root (.gmir opcode) #[src] #[resType]
      return (resType, src))
    (fun (resType, src) => CreateProg.operation (.gmir defined) #[src] #[resType])
    (fun op => op)

/-- Lowers `g_sext` to a `g_anyext` followed by a `g_sext_inreg` of the source width, which is what
LLVM's artifact combiner makes of a `g_sext` of a `g_trunc`. -/
def lowerSext : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType)
      let src ← MatchProg.value srcType
      let _ ← MatchProg.root (.gmir .g_sext) #[src] #[resType]
      return (srcType, resType, src))
    (fun (srcType, resType, src) => do
      let extProps ← CreateProg.property (.gmir .g_anyext) default
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[resType] extProps
      let props ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_sext_inreg)))
          srcType fun type => match type.val with
            | .integerType type => some (SextInRegProperties.mk (BitVec.ofNat 64 type.bitwidth))
            | _ => none
      CreateProg.operation (.gmir .g_sext_inreg) #[ext.res[0]!] #[resType] props)
    (fun op => op)

/-- Lowers `g_zext` to a `g_anyext` followed by a `g_and` with the mask of the source width, which
is what LLVM's artifact combiner makes of a `g_zext` of a `g_trunc`. -/
def lowerZext : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType)
      let src ← MatchProg.value srcType
      let _ ← MatchProg.root (.gmir .g_zext) #[src] #[resType]
      return (srcType, resType, src))
    (fun (srcType, resType, src) => do
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[resType]
      let mask ← widthConstant srcType resType (2 ^ · - 1)
      CreateProg.operation (.gmir .g_and) #[ext.res[0]!, mask.res[0]!] #[resType])
    (fun op => op)

/--
Widens the condition of `g_brcond` to `width` bits with a `g_zext`, which is what LLVM's
`LegalizerHelper::widenScalar` extends it with on a target whose booleans are 0 or 1, as on RISC-V.
`g_brcond` forwards a variable number of operands to its successors, which a Puddle pattern cannot
match, so this is a local rewrite.
-/
def widenBrcondCondition (width : Nat) : LocalRewritePattern OpCode := fun ctx op => do
  -- Read `ctx` before creating operations: any later read makes the first one copy the context.
  let operands := op.getOperands! ctx.raw
  let successors := op.getSuccessors! ctx.raw
  let props := op.getProperties! ctx.raw GMIR.g_brcond
  let .integerType type := (operands[0]!.getType! ctx.raw).val | return (ctx, none)
  if width ≤ type.bitwidth then return (ctx, none)
  let (ctx, ext) ← WfRewriter.createOp! ctx GMIR.g_zext #[IntegerType.signless width]
    #[operands[0]!] #[] #[] (NnegProperties.mk false) none
  let (ctx, branch) ← WfRewriter.createOp! ctx GMIR.g_brcond #[]
    (#[ValuePtr.opResult (ext.getResult 0)] ++ operands.extract 1) successors #[] props none
  return (ctx, some (#[ext, branch], #[]))

/-- The constant amount `c` of a funnel shift or rotate, read as an unsigned integer, modulo the
width of the shifted values of type `type`. -/
public def constantAmountModWidth (type : TypeAttr) (c : GMIRConstantProperties) : Nat :=
  c.bits.toNat % (type.cast? IntegerType).get!.bitwidth

/--
Lowers `g_fshl x, y, z` (`left`) or `g_fshr x, y, z` to shifts, as LLVM's
`LegalizerHelper::lowerFunnelShiftAsShifts` does for a constant amount `C = z % w` that is not zero,
where `w` is the width of `x`:

    fshl x, y, z = (x << C) | (y >> (w - C))
    fshr x, y, z = (x << (w - C)) | (y >> C)

LLVM builds `C` and `w - C` with a `g_urem` and a `g_sub`, which its builder constant-folds; they are
constants here directly. The `g_or` is disjoint, as both shifts are by less than `w`.
-/
def lowerFunnelShiftConstant (left : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let amtType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let c ← MatchProg.operation (.gmir .g_constant) #[] #[amtType]
      let _ ← MatchProg.root (.gmir (if left then .g_fshl else .g_fshr)) #[x, y, c.res[0]!] #[type]
      MatchProg.matchNative (type, c.properties) fun (type, c) => constantAmountModWidth type c ≠ 0
      return (type, amtType, x, y, c.properties))
    (fun (type, amtType, x, y, c) => do
      let shAmt ← createConstantWith amtType (type, c) fun (type, c) => constantAmountModWidth type c
      let invShAmt ← createConstantWith amtType (type, c) fun (type, c) =>
        (type.cast? IntegerType).get!.bitwidth - constantAmountModWidth type c
      let shX ← CreateProg.operation (.gmir .g_shl)
        #[x, (if left then shAmt else invShAmt).res[0]!] #[type]
      let shY ← CreateProg.operation (.gmir .g_lshr)
        #[y, (if left then invShAmt else shAmt).res[0]!] #[type]
      let orProps ← CreateProg.property (.gmir .g_or) { disjoint := true }
      CreateProg.operation (.gmir .g_or) #[shX.res[0]!, shY.res[0]!] #[type] orProps)
    (fun op => op)

/--
Lowers `g_fshl x, y, z` (`left`) or `g_fshr x, y, z` to shifts, as LLVM's
`LegalizerHelper::lowerFunnelShiftAsShifts` does for an amount that may be zero modulo the width `w`
of `x`. An extra shift by one keeps every shift amount below `w`:

    fshl x, y, z = (x << (z % w)) | ((y >> 1) >> (w - 1 - (z % w)))
    fshr x, y, z = ((x << 1) << (w - 1 - (z % w))) | (y >> (z % w))

For a power-of-two `w` (`pow2`), `z % w` is `z & (w - 1)` and `w - 1 - (z % w)` is `~z & (w - 1)`;
otherwise, they are computed with a `g_urem` and a `g_sub`. The `g_or` is disjoint, as the first
shift clears the bits that the second one sets. The shift by one is out of range for `w = 1`, which
`lowerFunnelShiftWidthOne` lowers instead.
-/
def lowerFunnelShiftGeneral (left pow2 : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) fun t =>
        2 ≤ t.bitwidth ∧ (t.bitwidth.nextPowerOfTwo = t.bitwidth) = pow2
      let amtType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let z ← MatchProg.value amtType
      let _ ← MatchProg.root (.gmir (if left then .g_fshl else .g_fshr)) #[x, y, z] #[type]
      return (type, amtType, x, y, z))
    (fun (type, amtType, x, y, z) => do
      let mask ← widthConstant type amtType fun w => (w : Int) - 1
      let (shAmt, invShAmt) ← if pow2 then do
          let shAmt ← CreateProg.operation (.gmir .g_and) #[z, mask.res[0]!] #[amtType]
          let allOnes ← createConstant amtType (-1)
          let notZ ← CreateProg.operation (.gmir .g_xor) #[z, allOnes.res[0]!] #[amtType]
          let invShAmt ← CreateProg.operation (.gmir .g_and) #[notZ.res[0]!, mask.res[0]!] #[amtType]
          pure (shAmt, invShAmt)
        else do
          let width ← widthConstant type amtType fun w => (w : Int)
          let shAmt ← CreateProg.operation (.gmir .g_urem) #[z, width.res[0]!] #[amtType]
          let invShAmt ← CreateProg.operation (.gmir .g_sub) #[mask.res[0]!, shAmt.res[0]!]
            #[amtType]
          pure (shAmt, invShAmt)
      let one ← createConstant amtType 1
      let (shX, shY) ← if left then do
          let shX ← CreateProg.operation (.gmir .g_shl) #[x, shAmt.res[0]!] #[type]
          let shY1 ← CreateProg.operation (.gmir .g_lshr) #[y, one.res[0]!] #[type]
          let shY ← CreateProg.operation (.gmir .g_lshr) #[shY1.res[0]!, invShAmt.res[0]!] #[type]
          pure (shX, shY)
        else do
          let shX1 ← CreateProg.operation (.gmir .g_shl) #[x, one.res[0]!] #[type]
          let shX ← CreateProg.operation (.gmir .g_shl) #[shX1.res[0]!, invShAmt.res[0]!] #[type]
          let shY ← CreateProg.operation (.gmir .g_lshr) #[y, shAmt.res[0]!] #[type]
          pure (shX, shY)
      let orProps ← CreateProg.property (.gmir .g_or) { disjoint := true }
      CreateProg.operation (.gmir .g_or) #[shX.res[0]!, shY.res[0]!] #[type] orProps)
    (fun op => op)

/--
Lowers the `i1` `g_fshl x, y, z` (`left`) to `x` and the `i1` `g_fshr x, y, z` to `y`: the amount
modulo 1 is always zero. (LLVM's `lowerFunnelShiftAsShifts` emits a shift by one here, which is out
of range.)
-/
def lowerFunnelShiftWidthOne (left : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 1)
      let amtType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let z ← MatchProg.value amtType
      let _ ← MatchProg.root (.gmir (if left then .g_fshl else .g_fshr)) #[x, y, z] #[type]
      return if left then x else y)
    pure (fun x => x)

/--
Lowers `g_rotl x, z` (`left`) or `g_rotr x, z` to shifts, as LLVM's `LegalizerHelper::lowerRotate`
does when no rotate or funnel shift is legal, for `w` the width of `x`. For a power-of-two `w`
(`pow2`):

    rotl x, z = (x << (z & (w - 1))) | (x >> (-z & (w - 1)))
    rotr x, z = (x >> (z & (w - 1))) | (x << (-z & (w - 1)))

and otherwise, with an extra shift by one that keeps every shift amount below `w`:

    rotl x, z = (x << (z % w)) | ((x >> 1) >> (w - 1 - (z % w)))
    rotr x, z = (x >> (z % w)) | ((x << 1) << (w - 1 - (z % w)))

Unlike in LLVM, the `g_or` of the power-of-two case is not disjoint: both shifts are by zero, and so
overlap, if `z % w` is zero.
-/
def lowerRotateGeneral (left pow2 : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) fun t =>
        (t.bitwidth.nextPowerOfTwo = t.bitwidth) = pow2
      let amtType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let z ← MatchProg.value amtType
      let _ ← MatchProg.root (.gmir (if left then .g_rotl else .g_rotr)) #[x, z] #[type]
      return (type, amtType, x, z))
    (fun (type, amtType, x, z) => do
      let shOpcode : GMIR := if left then .g_shl else .g_lshr
      let revShOpcode : GMIR := if left then .g_lshr else .g_shl
      let mask ← widthConstant type amtType fun w => (w : Int) - 1
      if pow2 then do
        let zero ← createConstant amtType 0
        let negZ ← CreateProg.operation (.gmir .g_sub) #[zero.res[0]!, z] #[amtType]
        let shAmt ← CreateProg.operation (.gmir .g_and) #[z, mask.res[0]!] #[amtType]
        let shVal ← CreateProg.operation (.gmir shOpcode) #[x, shAmt.res[0]!] #[type]
        let revAmt ← CreateProg.operation (.gmir .g_and) #[negZ.res[0]!, mask.res[0]!] #[amtType]
        let revVal ← CreateProg.operation (.gmir revShOpcode) #[x, revAmt.res[0]!] #[type]
        CreateProg.operation (.gmir .g_or) #[shVal.res[0]!, revVal.res[0]!] #[type]
      else do
        let width ← widthConstant type amtType fun w => (w : Int)
        let shAmt ← CreateProg.operation (.gmir .g_urem) #[z, width.res[0]!] #[amtType]
        let shVal ← CreateProg.operation (.gmir shOpcode) #[x, shAmt.res[0]!] #[type]
        let revAmt ← CreateProg.operation (.gmir .g_sub) #[mask.res[0]!, shAmt.res[0]!] #[amtType]
        let one ← createConstant amtType 1
        let inner ← CreateProg.operation (.gmir revShOpcode) #[x, one.res[0]!] #[type]
        let revVal ← CreateProg.operation (.gmir revShOpcode) #[inner.res[0]!, revAmt.res[0]!]
          #[type]
        let orProps ← CreateProg.property (.gmir .g_or) { disjoint := true }
        CreateProg.operation (.gmir .g_or) #[shVal.res[0]!, revVal.res[0]!] #[type] orProps)
    (fun op => op)

/--
The patterns that lower a funnel shift (`left` for `g_fshl`) or a rotate (`rotate`), in the order
they are tried: a funnel shift by a constant first, then any amount. They compute the shift amounts in the
type of the amount, so it must be at least as wide as the shifted values, which the legalization
rules ensure first (in LLVM IR, both types are the same).
-/
private def funnelShiftLowerings (left rotate : Bool) : Array (Pattern OpCode) :=
  if rotate then
    #[lowerRotateGeneral left true, lowerRotateGeneral left false]
  else
    #[lowerFunnelShiftConstant left, lowerFunnelShiftWidthOne left,
      lowerFunnelShiftGeneral left true, lowerFunnelShiftGeneral left false]

public section

/-- The patterns that lower `opcode`, in the order they are tried. -/
def lowerings : GMIR → Array (Pattern OpCode)
  | .g_sext => #[lowerSext]
  | .g_zext => #[lowerZext]
  | .g_ctlz_zero_poison => #[lowerZeroPoisonCount .g_ctlz_zero_poison .g_ctlz]
  | .g_cttz_zero_poison => #[lowerZeroPoisonCount .g_cttz_zero_poison .g_cttz]
  | .g_fshl => funnelShiftLowerings true false
  | .g_fshr => funnelShiftLowerings false false
  | .g_rotl => funnelShiftLowerings true true
  | .g_rotr => funnelShiftLowerings false true
  | _ => #[]

/-- Widens type group `typeIdx` of `opcode` to `width` bits. -/
def widenScalar? : GMIR → (typeIdx : TypeGroup) → (width : Nat) →
    Option (LocalRewritePattern OpCode)
  | .g_brcond, .type 0, width => widenBrcondCondition width
  | opcode, typeIdx, width => Option.map Puddle.Pattern.interpret <|
  match opcode, typeIdx, width with
  -- The high bits of the operands never reach the low bits of the result, so any extension is
  -- fine.
  | .g_add, .type 0, width => widenTypeGroup .g_add (.type 0) .g_anyext width clearNswNuwProperties
  | .g_sub, .type 0, width => widenTypeGroup .g_sub (.type 0) .g_anyext width clearNswNuwProperties
  -- The result has no operands in its group, so `g_anyext` is not used.
  | .g_icmp, .type 0, width => widenTypeGroup .g_icmp (.type 0) .g_anyext width
  -- The high bits matter for the comparison, and sign extension preserves both the signed and
  -- the unsigned order.
  | .g_icmp, .type 1, width => widenTypeGroup .g_icmp (.type 1) .g_sext width
  -- The high bits of the selected values never reach the low bits of the result.
  | .g_select, .type 0, width => widenTypeGroup .g_select (.type 0) .g_anyext width
  -- The condition is true when it is nonzero, so its high bits must be zero, as with LLVM's
  -- `getBoolExtOp` on a target whose booleans are zero or one.
  | .g_select, .type 1, width => widenTypeGroup .g_select (.type 1) .g_zext width
  -- As for `g_add`, the high bits of the shifted value never reach the low bits of the result.
  | .g_shl, .type 0, width => widenTypeGroup .g_shl (.type 0) .g_anyext width clearNswNuwProperties
  -- `ashr` shifts copies of the sign bit into the result, so the high bits must be sign bits.
  | .g_ashr, .type 0, width => widenTypeGroup .g_ashr (.type 0) .g_sext width
  -- `lshr` shifts zeros into the result, so the high bits must be zero.
  | .g_lshr, .type 0, width => widenTypeGroup .g_lshr (.type 0) .g_zext width
  -- The amount is an unsigned number of bits, so its value must be kept as such.
  | .g_shl, .type 1, width => widenTypeGroup .g_shl (.type 1) .g_zext width
  | .g_ashr, .type 1, width => widenTypeGroup .g_ashr (.type 1) .g_zext width
  | .g_lshr, .type 1, width => widenTypeGroup .g_lshr (.type 1) .g_zext width
  | .g_and, .type 0, width => widenTypeGroup .g_and (.type 0) .g_anyext width
  | .g_or, .type 0, width => widenTypeGroup .g_or (.type 0) .g_anyext width clearDisjointProperties
  | .g_xor, .type 0, width => widenTypeGroup .g_xor (.type 0) .g_anyext width
  | .g_mul, .type 0, width => widenTypeGroup .g_mul (.type 0) .g_anyext width clearNswNuwProperties
  -- The high bits matter for division and remainder, so the operands are extended according to
  -- the signedness of the operation. Exactness is preserved by both extensions.
  | .g_sdiv, .type 0, width => widenTypeGroup .g_sdiv (.type 0) .g_sext width
  | .g_srem, .type 0, width => widenTypeGroup .g_srem (.type 0) .g_sext width
  | .g_udiv, .type 0, width => widenTypeGroup .g_udiv (.type 0) .g_zext width
  | .g_urem, .type 0, width => widenTypeGroup .g_urem (.type 0) .g_zext width
  | .g_constant, .type 0, width => widenConstant width
  -- `g_sext_inreg` only reads the low `sz` bits, so any extension is fine.
  | .g_sext_inreg, .type 0, width => widenTypeGroup .g_sext_inreg (.type 0) .g_anyext width
  -- The count fits in the wide result, so the result is just truncated back.
  | .g_ctlz, .type 0, width => widenTypeGroup .g_ctlz (.type 0) .g_anyext width
  | .g_cttz, .type 0, width => widenTypeGroup .g_cttz (.type 0) .g_anyext width
  | .g_ctpop, .type 0, width => widenTypeGroup .g_ctpop (.type 0) .g_anyext width
  | .g_ctlz, .type 1, width => widenCtlzSrc width
  | .g_cttz, .type 1, width => widenCttzSrc width
  -- Zero bits do not add to the count.
  | .g_ctpop, .type 1, width => widenTypeGroup .g_ctpop (.type 1) .g_zext width
  | .g_bswap, .type 0, width => widenReverse .g_bswap width
  | .g_bitreverse, .type 0, width => widenReverse .g_bitreverse width
  -- Sign extension preserves the signed order, and also the unsigned order. For `g_umin` and
  -- `g_umax`, LLVM only sign-extends where it is cheaper than zero-extending (from `i32` on
  -- RISC-V), but both are correct.
  | .g_smin, .type 0, width => widenTypeGroup .g_smin (.type 0) .g_sext width
  | .g_smax, .type 0, width => widenTypeGroup .g_smax (.type 0) .g_sext width
  | .g_umin, .type 0, width => widenTypeGroup .g_umin (.type 0) .g_sext width
  | .g_umax, .type 0, width => widenTypeGroup .g_umax (.type 0) .g_sext width
  | .g_abs, .type 0, width => widenTypeGroup .g_abs (.type 0) .g_sext width
  -- The amount of a funnel shift or rotate is unsigned, so it is zero-extended.
  | .g_fshl, .type 1, width => widenTypeGroup .g_fshl (.type 1) .g_zext width
  | .g_fshr, .type 1, width => widenTypeGroup .g_fshr (.type 1) .g_zext width
  | .g_rotl, .type 1, width => widenTypeGroup .g_rotl (.type 1) .g_zext width
  | .g_rotr, .type 1, width => widenTypeGroup .g_rotr (.type 1) .g_zext width
  | _, _, _ => none

end

end Veir
