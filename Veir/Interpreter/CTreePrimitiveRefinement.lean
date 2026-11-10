module

public import Veir.Interpreter.Refinement.Basic
public import Veir.Verifier

public section

namespace Veir

/--
The monotonicity obligation for a CTree-based interpreter of a given opcode.
It asserts that refined operands and memory implies simulation of the resulting
operation CTree-based semantics.
-/
@[expose]
def OpCode.interpretCTree_monotone (opType : OpCode) : Prop :=
  ∀ (ctx : WfIRContext OpCode) (op : OperationPtr) (opIn : op.InBounds ctx.raw),
    op.getOpType ctx.raw opIn = opType →
    op.Verified ctx opIn →
    ∀ (sourceValues targetValues : Array RuntimeValue)
      (sourceMemory targetMemory : MemoryState),
      RuntimeValue.ArrayConforms sourceValues (op.getOperandTypes! ctx.raw) →
      RuntimeValue.arrayIsRefinedBy sourceValues targetValues →
      sourceMemory.isRefinedBy targetMemory →
      _root_.CTree.Sim
        (fun target source => OperationResult.isRefinedBy source target ∧
          RuntimeValue.ArrayConforms target.1 (op.getResultTypes! ctx.raw))
        (op.interpretCTree opIn targetValues targetMemory)
        (op.interpretCTree opIn sourceValues sourceMemory)

/--
Assumed CTree monotonicity and result typing for verified operations outside LLVM.
Operands and stored bytes may refine; object layout and global bindings stay fixed.
-/
axiom OpCode.interpretCTree_monotone_assumed (opType : OpCode) (h : ∀ op, opType ≠ .llvm op) :
    interpretCTree_monotone opType

end Veir
