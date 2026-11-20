module

public import Veir.Interpreter.Refinement.Basic
public import Veir.Interfaces.DeadCodeInterfaces
public import Veir.Rewriter.WfRewriter.Basic
public import Veir.Verifier

public section

namespace Veir

/--
Verified dead-code erasure, excluding allocation effects because allocation addresses
are observable in the current memory model.
-/
def VerifiedDeadCodeErasure : Prop :=
  ∀ {ctx : WfIRContext OpCode} {moduleOp op : OperationPtr},
    (verified : ctx.Verified moduleOp) →
    (moduleCode : moduleOp.getOpType! ctx.raw = .builtin .module) →
    (moduleNoParent : moduleOp.getParent! ctx.raw = none) →
    (opIn : op.InBounds ctx.raw) →
    (dead : op.isTriviallyDead ctx.raw) →
    (noAllocation : (op.getEffects ctx.raw).allocates = false) →
    let result := WfRewriter.eraseOp ctx op dead.1 dead.2.1 opIn
    result.Verified moduleOp ∧ moduleOp.isModuleRefinedByCTree ctx moduleOp result

/--
Erasing a verified, trivially dead, nonallocating operation preserves verification
and module refinement.
-/
axiom verifiedDeadCodeErasure : VerifiedDeadCodeErasure

end Veir
