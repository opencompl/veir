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
  - Some informations represented as operation properties (e.g. the icmp condition code) are
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

/-! ## Pass implementation -/

def LLVMToGMIRPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    g_add.run, g_sub.run, g_icmp.run
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying llvm-to-gmir translation"
  | some ctx => pure ctx

public def LLVMToGMIRPass : Pass OpCode :=
  { name := "llvm-to-gmir"
    description := "Lower llvm dialect operations to the gmir dialect."
    run := fun _ => LLVMToGMIRPass.impl }

end Veir
