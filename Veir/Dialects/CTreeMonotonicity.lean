module

public import Veir.Dialects.LLVM.CTreeMonotonicity

public section

/-!
# Monotonicity of the opcodes in CTrees

Every opcode meets the CTree monotonicity obligation `OpCode.interpretCTree_monotone`: the opcodes
that have a proof through their own instance, the rest by assumption. The split is per opcode, so
a dialect can prove the ones it can and leave the rest.
-/

namespace Veir

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
