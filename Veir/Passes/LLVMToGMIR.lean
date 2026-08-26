module

public import Veir.Pass
import Veir.Passes.Matching
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

namespace Veir

/-!
  This file replicates LLVM's GlobalISel IRTranslator pass.
  This pass is responsible for translating LLVM IR into gMIR.

  The all properties on LLVM-IR operations are carried over into gMIR
  (see upstreams `MachineInstr::copyFlagsFromInstruction`).
-/

/-! # Lowering Patterns -/

/--
  gMIR 1:1 lowerings with Puddle for binary integer operations.

  This should mirror ArithToLLVM's lower1to1. To support variable result/operand counts, we would need
  a Puddle equivalent of `pdl.results` and `pdl.operands`.
-/
def lowerIntegerBinop (lOp : Llvm) (gOp : Gmir)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let returnType ← Puddle.MatchProg.type (Attr := IntegerType)
      let lhs ← Puddle.MatchProg.value returnType
      let rhs ← Puddle.MatchProg.value returnType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[lhs, rhs] #[returnType]
      return (returnType, lhs, rhs, root))
    (fun (returnType, lhs, rhs, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties
                    (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[lhs, rhs] #[returnType] props
      return newOp)
    (fun newOp => newOp)

def g_add_pattern := lowerIntegerBinop .add .g_add

def g_sub_pattern := lowerIntegerBinop .sub .g_sub

def g_icmp_pattern := lowerIntegerBinop .icmp  .g_icmp

def g_add (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite g_add_pattern.compile rewriter op opInBounds

def g_sub (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite g_sub_pattern.compile rewriter op opInBounds

def g_icmp (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite g_icmp_pattern.compile rewriter op opInBounds

/-! # Pass implementation -/

def LLVMToGMIRPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    g_add, g_sub, g_icmp
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying llvm-to-gmir translation"
  | some ctx => pure ctx

public def LLVMToGMIRPass : Pass OpCode :=
  { name := "llvm-to-gmir"
    description := "Translate llvm dialect operations to gmir generic instructions."
    run := fun _ => LLVMToGMIRPass.impl }

end Veir
