module

public import Veir.PatternRewriter.Basic
public import Veir.GlobalOpInfo

namespace Veir

/-- Global initializer regions describe link-time constants. Machine lowering
    must leave them in LLVM form for the global-data emitter. -/
public def RewritePattern.preserveLLVMGlobalInitializers (pattern : RewritePattern OpCode) :
    RewritePattern OpCode := fun rewriter op hin => do
  let mut parent := op.getParentOp! rewriter.ctx.raw
  while let some ancestor := parent do
    if ancestor.getOpType! rewriter.ctx.raw == .llvm .mlir__global then
      return rewriter
    parent := ancestor.getParentOp! rewriter.ctx.raw
  pattern rewriter op hin

end Veir
