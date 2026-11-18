module

public import Veir.Interpreter.CTreePrimitiveRefinement

public section

/-!
# Monotonicity of the dialects

Every opcode is monotone in CTrees, in its operands and its memory: the opcodes that have a proof
through their own `InterpretOpMonotone` instance, the rest by assumption. The split is per
opcode, so a dialect can prove the ones it can and leave the rest. Importing this module is what
gives `OpCode.interpretCTree_monotone_of_opCode` an opcode it knows nothing about.
-/

namespace Veir

instance (priority := low) (opType : OpCode) : InterpretOpMonotone opType := by
  cases opType <;> rename_i op <;> cases op <;>
    first
      | infer_instance
      | exact ⟨OpCode.interpretCTree_monotone_assumed _⟩

/-- Every opcode is monotone in CTrees, with the results of the target typed. -/
theorem OpCode.interpretCTree_monotone_of_opCode (opType : OpCode) :
    OpCode.interpretCTree_monotone opType :=
  InterpretOpMonotone.monotone

end Veir

/--
info: 'Veir.OpCode.interpretCTree_monotone_of_opCode' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 Veir.OpCode.interpretCTree_monotone_assumed]
-/
#guard_msgs in
#print axioms Veir.OpCode.interpretCTree_monotone_of_opCode

end
