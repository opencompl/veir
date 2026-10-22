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
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[lhs, rhs] #[resultType] props
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
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[operand] #[resultType] props
      return newOp)
    (fun newOp => newOp)

def g_sext := (lowerIntegerCast .sext .g_sext).compile

def g_zext := (lowerIntegerCast .zext .g_zext).compile

def g_trunc := (lowerIntegerCast .trunc .g_trunc).compile

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
      Puddle.CreateProg.operation (.gmir .g_constant) #[] #[resultType] props)
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
  `lOp` on a byte, followed by `numIntOperands` integer operands -> `gOp` on integers of the same
  widths, between `builtin.unrealized_conversion_cast`s.
  LLVM converts all byte types to integer types of the same width when translating to gMIR
  (see `getLLTForType`); this mirrors that conversion.
-/
def lowerByteOp (lOp : Llvm) (gOp : GMIR) (numIntOperands : Nat := 0)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let operandType ← Puddle.MatchProg.type (Attr := LLVM.ByteType)
      let resultType ← Puddle.MatchProg.type (Attr := LLVM.ByteType)
      let operand ← Puddle.MatchProg.value operandType
      let intOperands ← (Array.range numIntOperands).mapM fun _ => do
        Puddle.MatchProg.value (← Puddle.MatchProg.type (Attr := IntegerType))
      let root ← Puddle.MatchProg.root (.llvm lOp) (#[operand] ++ intOperands) #[resultType]
      return (operandType, resultType, operand, intOperands, root))
    (fun (operandType, resultType, operand, intOperands, root) => do
      let intOperandType ← Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode .type)
          operandType TypeAttr.intOfByte?
      let intResultType ← Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode .type)
          resultType TypeAttr.intOfByte?
      let castProps ← Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castOp ← Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[operand] #[intOperandType] castProps
      let props ← Puddle.CreateProg.applyNative root.properties (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) (#[castOp.res[0]!] ++ intOperands)
          #[intResultType] props
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast) #[newOp.res[0]!]
          #[resultType] castProps)
    (fun castBackOp => castBackOp)

def g_truncByte := (lowerByteOp .trunc .g_trunc).compile

def g_shlByte := (lowerByteOp .shl .g_shl (numIntOperands := 1)).compile

def g_lshrByte := (lowerByteOp .lshr .g_lshr (numIntOperands := 1)).compile

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
      let castProps ← Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast) #[operand] #[resultType]
          castProps)
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
    g_add.run, g_sub.run, g_icmp.run, g_sext.run, g_zext.run, g_trunc.run,
    g_and.run, g_or.run, g_xor.run, g_shl.run, g_lshr.run, g_ashr.run,
    g_mul.run, g_sdiv.run, g_udiv.run, g_srem.run, g_urem.run,
    g_constant.run, g_truncByte.run, g_shlByte.run, g_lshrByte.run, byteIntBitcast.run,
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
