module

public import Veir.Dialects.LLVM.CTreeMonotonicity

public section

/-!
# Monotonicity of the opcodes in CTrees

Every opcode meets the CTree monotonicity obligation `OpCode.interpretCTree_monotone`: the LLVM
opcodes by proof, the rest by assumption.
-/

namespace Veir

/-- Every opcode is monotone in CTrees, with the results of the target typed. -/
theorem OpCode.interpretCTree_monotone_of_opCode (opType : OpCode) :
    OpCode.interpretCTree_monotone opType := by
  by_cases h : ∃ op, opType = .llvm op
  · obtain ⟨op, rfl⟩ := h
    exact OpCode.interpretCTree_monotone_llvm op
  · exact OpCode.interpretCTree_monotone_assumed opType fun op hop => h ⟨op, hop⟩

end Veir

/--
info: 'Veir.OpCode.interpretCTree_monotone_llvm' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 Veir.interpretOp'_results_conform,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms Veir.OpCode.interpretCTree_monotone_llvm

/--
info: 'Veir.OpCode.interpretCTree_monotone_of_opCode' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 Veir.interpretOp'_results_conform,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub,
 Veir.OpCode.interpretCTree_monotone_assumed]
-/
#guard_msgs in
#print axioms Veir.OpCode.interpretCTree_monotone_of_opCode

end
