module

public import Veir.Pass
import Veir.Passes.Matching
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
  GMIR lowerings with Puddle for binary operations.
-/
def lowerBinop (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let lhsType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let rhsType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr)
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

def g_mul := (lowerBinop .mul .g_mul).compile

def g_sdiv := (lowerBinop .sdiv .g_sdiv).compile

def g_udiv := (lowerBinop .udiv .g_udiv).compile

def g_srem := (lowerBinop .srem .g_srem).compile

def g_urem := (lowerBinop .urem .g_urem).compile

def g_smax := (lowerBinop .intr__smax .g_smax).compile

def g_smin := (lowerBinop .intr__smin .g_smin).compile

def g_umax := (lowerBinop .intr__umax .g_umax).compile

def g_umin := (lowerBinop .intr__umin .g_umin).compile

/--
  `llvm.intr.abs` -> `gmir.g_abs`. As in upstream's IRTranslator, `is_int_min_poison` is dropped:
  `g_abs` of the minimum value is the minimum value, which refines poison.
-/
def g_abs := (Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := TypeAttr)
      let operand ← Puddle.MatchProg.value type
      let _ ← Puddle.MatchProg.root (.llvm .intr__abs) #[operand] #[type]
      return (type, operand))
    (fun (type, operand) => do
      let props ← Puddle.CreateProg.property (.gmir .g_abs) ()
      Puddle.CreateProg.operation (.gmir .g_abs) #[operand] #[type] props)
    (fun newOp => newOp)).compile

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

/-! ## Pass implementation -/

def LLVMToGMIRPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    g_add.run, g_sub.run, g_icmp.run, g_sext.run, g_zext.run, g_trunc.run,
    g_and.run, g_or.run, g_xor.run,
    g_mul.run, g_sdiv.run, g_udiv.run, g_srem.run, g_urem.run,
    g_smax.run, g_smin.run, g_umax.run, g_umin.run, g_abs.run
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying llvm-to-gmir translation"
  | some ctx => pure ctx

public def LLVMToGMIRPass : Pass OpCode :=
  { name := "llvm-to-gmir"
    description := "Lower llvm dialect operations to the gmir dialect."
    run := fun _ => LLVMToGMIRPass.impl }

end Veir
