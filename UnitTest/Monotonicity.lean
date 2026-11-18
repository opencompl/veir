import Veir.Dialects.Monotonicity

/-!
Test which axioms the monotonicity of the dialects depends on: an opcode proved monotone in
CTrees depends on the `Sim` axioms only, and the rest on `OpCode.interpretCTree_monotone_assumed`.
-/

namespace Veir

/-- Every LLVM opcode but `freeze` is monotone in `Interp`, without the `Sim` axioms. -/
theorem llvm_interpretOp'ContextuallyMonotone_not_assumed (op : Llvm) (h : op ≠ .freeze) :
    InterpretOp'ContextuallyMonotone (.llvm op) :=
  llvm_interpretOp'ContextuallyMonotone h

/--
info: 'Veir.llvm_interpretOp'ContextuallyMonotone_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms llvm_interpretOp'ContextuallyMonotone_not_assumed

/--
Instance resolution proves, rather than assumes, the monotonicity in CTrees of every LLVM
opcode: the catch-all instance that falls back to `OpCode.interpretCTree_monotone_assumed` is
in scope here, and loses to the proof.
-/
theorem llvm_interpretCTreeMonotone_not_assumed (op : Llvm) : InterpretCTreeMonotone (.llvm op) :=
  inferInstance

/--
info: 'Veir.llvm_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms llvm_interpretCTreeMonotone_not_assumed

/--
info: 'Veir.OpCode.interpretCTree_monotone_of_opCode' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub,
 OpCode.interpretCTree_monotone_assumed]
-/
#guard_msgs in
#print axioms OpCode.interpretCTree_monotone_of_opCode

end Veir
