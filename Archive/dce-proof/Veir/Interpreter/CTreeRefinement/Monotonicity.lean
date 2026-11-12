module

public import Veir.Interpreter.CTreeRefinement.Program

public section

/-!
# Monotonicity assumption for CTree opcode semantics

The interpreter's opcode implementations are assumed to respect refinement of
runtime operands and memory. This is the operation-level semantic assumption used
when lifting local transformations to programs. The assumption relates the same
opcode, properties, result types, and successor block pointers on both sides;
it does not assert correctness of a rewrite or a pass.

Memory refinement retains the allocated objects and global-symbol table, and may
replace poison memory bits by defined bits. Successful results refine in values,
memory, and optional control-flow actions. UB and interpreter failure follow
`Tree.Refines`'s outcome convention, and choices follow its reversed `CTree.Sim`.
-/

namespace Veir.Tree.Refinement

/--
Semantic monotonicity of opcode interpretation with respect to related operands
and initial memories. This is an explicit assumption about the opcode semantics.
-/
axiom operation_monotonicity (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr)
    (valuesSource valuesTarget : Array RuntimeValue)
    (memorySource memoryTarget : Veir.MemoryState)
    (hvalues : RuntimeValue.arrayIsRefinedBy valuesSource valuesTarget)
    (hmemory : MemoryState.isRefinedBy memorySource memoryTarget) :
    Tree.Refines OperationResult.isRefinedBy
      (CTree.interpretOpTree opType properties resultTypes valuesSource blockOperands memorySource)
      (CTree.interpretOpTree opType properties resultTypes valuesTarget blockOperands memoryTarget)

/-- The usual shared-initial-memory instance of opcode monotonicity. -/
theorem operation_monotonicity_same_memory (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr)
    (valuesSource valuesTarget : Array RuntimeValue) (memory : Veir.MemoryState)
    (hvalues : RuntimeValue.arrayIsRefinedBy valuesSource valuesTarget) :
    Tree.Refines OperationResult.isRefinedBy
      (CTree.interpretOpTree opType properties resultTypes valuesSource blockOperands memory)
      (CTree.interpretOpTree opType properties resultTypes valuesTarget blockOperands memory) := by
  exact operation_monotonicity opType properties resultTypes blockOperands
    valuesSource valuesTarget memory memory hvalues (MemoryState.isRefinedBy_refl memory)

end Veir.Tree.Refinement
