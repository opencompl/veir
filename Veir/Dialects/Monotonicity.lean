module

public import Veir.Dialects.LLVM.Monotonicity
public import Veir.Dialects.RISCV.Monotonicity
public import Veir.Dialects.LLVM.CTreeMonotonicity
public import Veir.Interpreter.CTreePrimitiveRefinement

public section

/-!
# Monotonicity of the dialects

Every opcode is monotone in its operands, and in CTrees in its operands and its memory: the
opcodes that have a proof through their own instance, the rest by assumption. The split is per
opcode, so a dialect can prove the ones it can and leave the rest. Importing this module is what
gives `interpretOp'_monotone` and `OpCode.interpretCTree_monotone_of_opCode` an opcode they know
nothing about.
-/

namespace Veir

instance (priority := low) (opType : OpCode) : InterpretOp'Monotone opType := by
  cases opType <;> rename_i op <;> cases op <;>
    first
      | infer_instance
      | exact interpretOp'_monotone_assumed _

instance (priority := low) (opType : OpCode) : InterpretCTreeMonotone opType := by
  cases opType <;> rename_i op <;> cases op <;>
    first
      | infer_instance
      | exact ⟨OpCode.interpretCTree_monotone_assumed _⟩

/-- Every opcode is monotone in CTrees, with the results of the target typed. -/
theorem OpCode.interpretCTree_monotone_of_opCode (opType : OpCode) :
    OpCode.interpretCTree_monotone opType :=
  InterpretCTreeMonotone.monotone

end Veir

/--
info: 'Veir.OpCode.interpretCTree_monotone_of_opCode' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub,
 Veir.OpCode.interpretCTree_monotone_assumed]
-/
#guard_msgs in
#print axioms Veir.OpCode.interpretCTree_monotone_of_opCode

end
