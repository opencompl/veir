module

public import Veir.Passes.SimplifyCFG
public import Veir.Interpreter.Refinement.Basic
public import Veir.Interfaces.FunctionInterfaces

namespace Veir.SimplifyCFG

/--
A successful `simplifycfg` run on verified IR satisfying SSA dominance preserves
the semantics of every function under the pass root, including the root itself
when it is a function. Function pointers survive the transformation.

For the same arguments and initial memory, every defined source execution is
matched by a target execution with equal final memory and pointwise-refined
return values. As in `Interp.isRefinedBy`, source UB and interpreter failure
(including unsupported operations) impose no obligation on the target.

This states correctness of the pure implementation used by `SimplifyCFGPass`.
It uses the function interface so that LLVM functions are covered as well as
`func.func`. The proof is intentionally left for future work.
-/
public theorem preservesSemantics
    {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    (rootIn : root.InBounds ctx.raw)
    (ctxDom : ctx.Dom) (ctxVerified : ctx.Verified root)
    (hRun : run ctx root = .ok newCtx) :
    ∀ (func : OperationPtr) (funcIn : func.InBounds ctx.raw),
      func.isFunctionLike ctx.raw →
      (IRNode.operation root).Ancestor (.operation func) ctx →
      ∃ funcIn' : func.InBounds newCtx.raw,
        ∀ (args : Array RuntimeValue) (mem : MemoryState),
          Interp.isRefinedBy FunctionResult.isRefinedBy
            (interpretFunction func args mem (ctx := ctx) funcIn)
            (interpretFunction func args mem (ctx := newCtx) funcIn') := by
  sorry

end Veir.SimplifyCFG
