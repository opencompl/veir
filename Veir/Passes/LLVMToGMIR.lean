module

public import Veir.Pass
import Veir.Passes.Legalization.LegalizerInfo
import Veir.Passes.Matching
import Veir.Passes.CastsReconciliation.Reconciliation
import Veir.Passes.DCE.dce
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

namespace Veir

/-!
  # LLVMToGMIR pass

  This file replicates LLVM's GlobalISel IRTranslator pass.

  All properties on LLVM IR operations are carried over to gMIR, similar to
  upstream's `MachineInstr::copyFlagsFromInstruction`

  This lowering differs from the upstream implementation in the following ways:
  - Upstream converts all poison values to undef values; we only have poison but no undef.
  - Some information represented as operation properties (e.g. the icmp condition code) is
    represented as special operands in upstream gMIR. This includes all operands with type `immediate`
    or `unknown` in upstream's llvm/include/llvm/Target/GenericOpcodes.td.
  - GEP indices are normalized here, but GEP address arithmetic remains in the LLVM dialect
    until instruction selection. The currently supported pointer index width is 64 bits.
-/

/-! ## Lowering Patterns -/

/--
  GMIR lowerings with Puddle for binary operations on values that gMIR can represent, i.e. whose
  types have an `LLT`. (This is intended to guard against matching byte type operands.)
-/
def lowerBinop (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let lhsType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let rhsType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let lhs ← Puddle.MatchProg.value lhsType
      let rhs ← Puddle.MatchProg.value rhsType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[lhs, rhs] #[resultType]
      return (resultType, lhs, rhs, root))
    (fun (resultType, lhs, rhs, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties
                    (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[lhs, rhs] #[resultType] (.inr props)
      return newOp)
    (fun newOp => newOp)

def g_add := (lowerBinop .add .g_add).compile

def g_sub := (lowerBinop .sub .g_sub).compile

def g_icmp := (lowerBinop .icmp  .g_icmp).compile

def g_and := (lowerBinop .and .g_and).compile

def g_or := (lowerBinop .or .g_or).compile

def g_xor := (lowerBinop .xor .g_xor).compile

def g_shl := (lowerBinop .shl .g_shl).compile

def g_lshr := (lowerBinop .lshr .g_lshr).compile

def g_ashr := (lowerBinop .ashr .g_ashr).compile

def g_mul := (lowerBinop .mul .g_mul).compile

def g_sdiv := (lowerBinop .sdiv .g_sdiv).compile

def g_udiv := (lowerBinop .udiv .g_udiv).compile

def g_srem := (lowerBinop .srem .g_srem).compile

def g_urem := (lowerBinop .urem .g_urem).compile

/--
  GMIR lowerings with Puddle for unary operations on values that gMIR can represent, whose
  properties are converted with `convert`.
-/
def lowerUnop (lOp : Llvm) (gOp : GMIR)
    (convert : propertiesOf (OpCode.llvm lOp) → propertiesOf (OpCode.gmir gOp)) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let operandType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let operand ← Puddle.MatchProg.value operandType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[operand] #[resultType]
      return (resultType, operand, root))
    (fun (resultType, operand, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties (fun p => some (convert p))
      Puddle.CreateProg.operation (.gmir gOp) #[operand] #[resultType] (.inr props))
    (fun newOp => newOp)

/-
  LLVM translates a `ctlz`/`cttz` whose zero input is poison to `G_CTLZ_ZERO_POISON`/
  `G_CTTZ_ZERO_POISON`. We do not have these opcodes yet, and `g_ctlz`/`g_cttz`, which are
  defined at zero, refine them.
-/
def g_ctlz := (lowerUnop .intr__ctlz .g_ctlz fun _ => ()).compile

def g_cttz := (lowerUnop .intr__cttz .g_cttz fun _ => ()).compile

def g_ctpop := (lowerUnop .intr__ctpop .g_ctpop id).compile

def g_bswap := (lowerUnop .intr__bswap .g_bswap id).compile

def g_bitreverse := (lowerUnop .intr__bitreverse .g_bitreverse id).compile

/--
  `llvm.select` -> `g_select`, as in LLVM's `IRTranslator::translateSelect`. The `i1` condition
  selects as `g_select` does, see `GMIR.selectNonzero_one`.
  TODO: Also translate selects of pointers, once `g_select` accepts them.
-/
def lowerSelect : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let condType ← Puddle.MatchProg.type (Attr := IntegerType) (·.bitwidth = 1)
      let type ← Puddle.MatchProg.type (Attr := IntegerType)
      let cond ← Puddle.MatchProg.value condType
      let tval ← Puddle.MatchProg.value type
      let fval ← Puddle.MatchProg.value type
      let _ ← Puddle.MatchProg.root (.llvm .select) #[cond, tval, fval] #[type]
      return (type, cond, tval, fval))
    (fun (type, cond, tval, fval) =>
      Puddle.CreateProg.operation (.gmir .g_select) #[cond, tval, fval] #[type])
    (fun newOp => newOp)

def g_select := lowerSelect.compile

/--
  GMIR lowerings with Puddle for integer casts.
-/
def lowerIntegerCast (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let operandType ← Puddle.MatchProg.type (Attr := IntegerType)
      let resultType ← Puddle.MatchProg.type (Attr := IntegerType)
      let operand ← Puddle.MatchProg.value operandType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[operand] #[resultType]
      return (resultType, operand, root))
    (fun (resultType, operand, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties
                    (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[operand] #[resultType] (.inr props)
      return newOp)
    (fun newOp => newOp)

def g_sext := (lowerIntegerCast .sext .g_sext).compile

def g_zext := (lowerIntegerCast .zext .g_zext).compile

def g_trunc := (lowerIntegerCast .trunc .g_trunc).compile

/--
  Normalize dynamic GEP indices to the current 64-bit pointer index type, as in
  LLVM's `IRTranslator::translateGetElementPtr`: sign-extend narrower indices
  and truncate wider ones before scaling them. Rewrite a dynamic index that is a
  constant as an `i64` constant instead. Preserve constant indices and GEP flags. Plain truncation may refine poison from a violated GEP no-wrap flag.
-/
private def normalizeGEPIndices : LocalRewritePattern OpCode := fun ctx op => do
  let some (ptr, indices, props) := matchGetelementptrIndices op ctx.raw | return (ctx, none)
  let mut ctx := ctx
  let mut ops := #[]
  let mut operands := #[ptr]
  for index in indices do
    if let .integerType type := (index.getType! ctx.raw).val then
      if type.bitwidth ≠ 0 && type.bitwidth ≠ 64 then
        /- Fold a constant index into an `i64` `g_constant`, so that load/store selection can
           still fold it into the access's immediate offset. -/
        let constant := matchConstantIntVal index ctx.raw <|> matchGConstantIntVal index ctx.raw
        let (ctx', castOp) ← if let some value := constant then
            WfRewriter.createOp! ctx GMIR.g_constant #[IntegerType.signless 64] #[] #[] #[]
                (GMIRConstantProperties.mk (.ofInt (BitVec.ofInt 64 value).toInt (.signless 64)))
                none
          else if type.bitwidth < 64 then
            WfRewriter.createOp! ctx GMIR.g_sext #[IntegerType.signless 64]
                #[index] #[] #[] () none
          else
            WfRewriter.createOp! ctx GMIR.g_trunc #[IntegerType.signless 64]
                #[index] #[] #[] (NswNuwProperties.mk false false) none
        ctx := ctx'
        ops := ops.push castOp
        operands := operands.push (castOp.getResult 0)
        continue
    operands := operands.push index
  if ops.isEmpty then return (ctx, none)
  let (ctx', gep) ← WfRewriter.createOp! ctx Llvm.getelementptr (op.getResultTypes! ctx.raw)
      operands #[] #[] props none
  return (ctx', some (ops.push gep, #[gep.getResult 0]))

private def lowerBranch : LocalRewritePattern OpCode := fun ctx op => do
  let opType := op.getOpType! ctx.raw
  if opType != OpCode.llvm .br && opType != OpCode.llvm .cond_br then return (ctx, none)
  let operands := op.getOperands! ctx.raw
  let successors := op.getSuccessors! ctx.raw
  let (ctx', branch) ← if opType = OpCode.llvm .br then
      WfRewriter.createOp! ctx GMIR.g_br #[] operands successors #[] () none
    else
      let props : LLVMCondBrProperties := op.getProperties! ctx.raw (OpCode.llvm .cond_br)
      WfRewriter.createOp! ctx GMIR.g_brcond #[] operands successors #[]
        (GMIRBrCondProperties.mk props.operandSegmentSizes) none
  return (ctx', some (#[branch], #[]))

/-- `llvm.mlir.constant` (integer) -> `gmir.g_constant`. -/
def lowerIntegerConstant : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let resultType ← Puddle.MatchProg.type (Attr := IntegerType)
      let root ← Puddle.MatchProg.root (.llvm .mlir__constant) #[] #[resultType]
          (fun props => props.value matches .integer _)
      return (resultType, root))
    (fun (resultType, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties fun props =>
        match props.value with
        | .integer value => some (GMIRConstantProperties.mk value)
        | _ => none
      Puddle.CreateProg.operation (.gmir .g_constant) #[] #[resultType] (.inr props))
    (fun newOp => newOp)

def g_constant := lowerIntegerConstant.compile

/--
  The integer type with the same width as the byte type `type`.
  Returns `none` if `type` is not a byte type.
-/
def TypeAttr.intOfByte? (type : TypeAttr) : Option TypeAttr := do
  let type ← type.cast? LLVM.ByteType
  return IntegerType.signless type.bitwidth

/--
  `lOp` on bytes -> `gOp` on integers of the same widths, between `builtin.unrealized_conversion_cast`s.
  LLVM converts all byte types to integer types of the same width when translating to gMIR
  (see `getLLTForType`); this mirrors that conversion.
-/
def lowerUnaryByteOp (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let operandType ← Puddle.MatchProg.type (Attr := LLVM.ByteType)
      let resultType ← Puddle.MatchProg.type (Attr := LLVM.ByteType)
      let operand ← Puddle.MatchProg.value operandType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[operand] #[resultType]
      return (operandType, resultType, operand, root))
    (fun (operandType, resultType, operand, root) => do
      let intOperandType ← Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode .type)
          operandType TypeAttr.intOfByte?
      let intResultType ← Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode .type)
          resultType TypeAttr.intOfByte?
      let castOp ← Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[operand] #[intOperandType]
      let props ← Puddle.CreateProg.applyNative root.properties (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[castOp.res[0]!]
          #[intResultType] (.inr props)
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast) #[newOp.res[0]!]
          #[resultType])
    (fun castBackOp => castBackOp)

def g_truncByte := (lowerUnaryByteOp .trunc .g_trunc).compile

/--
  A shift of a byte by an integer amount -> `gOp` on the integer of the same width, between
  `builtin.unrealized_conversion_cast`s, as in `lowerUnaryByteOp`.
-/
def lowerByteShift (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let byteType ← Puddle.MatchProg.type (Attr := LLVM.ByteType)
      let amountType ← Puddle.MatchProg.type (Attr := IntegerType)
      let value ← Puddle.MatchProg.value byteType
      let amount ← Puddle.MatchProg.value amountType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[value, amount] #[byteType]
      return (byteType, value, amount, root))
    (fun (byteType, value, amount, root) => do
      let intType ← Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode .type)
          byteType TypeAttr.intOfByte?
      let castOp ← Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[value] #[intType]
      let props ← Puddle.CreateProg.applyNative root.properties (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[castOp.res[0]!, amount]
          #[intType] (.inr props)
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast) #[newOp.res[0]!]
          #[byteType])
    (fun castBackOp => castBackOp)

def g_shlByte := (lowerByteShift .shl .g_shl).compile

def g_lshrByte := (lowerByteShift .lshr .g_lshr).compile

/-- Whether `opType` and `resType` are a byte and an integer type of the same width. -/
def isByteIntBitcast (opType resType : TypeAttr) : Bool :=
  match opType.val, resType.val with
  | .byteType b, .integerType i | .integerType i, .byteType b => b.bitwidth = i.bitwidth
  | _, _ => false

/--
  `llvm.bitcast` between a byte and an integer of the same width -> `builtin.unrealized_conversion_cast`.
  LLVM reuses the source register for these (see `translateBitCast`).
-/
def lowerByteIntBitcast : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let operandType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let operand ← Puddle.MatchProg.value operandType
      let _ ← Puddle.MatchProg.root (.llvm .bitcast) #[operand] #[resultType]
      Puddle.MatchProg.matchNative (operandType, resultType)
          fun (operandType, resultType) => isByteIntBitcast operandType resultType
      return (resultType, operand))
    (fun (resultType, operand) => do
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast) #[operand] #[resultType])
    (fun castOp => castOp)

def byteIntBitcast := lowerByteIntBitcast.compile

/--
  Whether `iN -> !llvm.byte<N> -> iN` is the identity (see `LLVM.Byte.toFrozenInt_fromInt`).
  The round trip from a byte freezes its poison bits, so it is not folded.
-/
def isIntToByteRoundTrip (inputType interType : TypeAttr) : Bool :=
  match inputType.val, interType.val with
  | .integerType i, .byteType b => i.bitwidth = b.bitwidth && 0 < i.bitwidth
  | _, _ => false

/-! ## Pass implementation -/

def LLVMToGMIRPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    g_add.run, g_sub.run, g_icmp.run, g_select.run, g_sext.run, g_zext.run, g_trunc.run,
    g_and.run, g_or.run, g_xor.run, g_shl.run, g_lshr.run, g_ashr.run,
    g_mul.run, g_sdiv.run, g_udiv.run, g_srem.run, g_urem.run,
    g_ctlz.run, g_cttz.run, g_ctpop.run, g_bswap.run, g_bitreverse.run,
    g_constant.run, g_truncByte.run, g_shlByte.run, g_lshrByte.run, byteIntBitcast.run,
    .fromLocalRewrite normalizeGEPIndices, .fromLocalRewrite lowerBranch,
    .fromLocalRewrite (reconcilePairingCastLocal isIntToByteRoundTrip)
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying llvm-to-gmir translation"
  | some ctx =>
    -- A local rewrite may only erase the matched cast, so the folded first cast is left dead.
    match RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern #[eliminateDeadOp]) ctx with
    | none => throw "Error while applying DCE after llvm-to-gmir translation"
    | some ctx => pure ctx

public def LLVMToGMIRPass : Pass OpCode :=
  { name := "llvm-to-gmir"
    description := "Lower llvm dialect operations to the gmir dialect."
    run := fun _ => LLVMToGMIRPass.impl }

end Veir
