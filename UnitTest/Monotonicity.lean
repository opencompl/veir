import Veir.Dialects.Monotonicity

/-! Test that an opcode proved monotone in CTrees depends on the `Sim` axioms only. -/

namespace Veir

/--
Instance resolution proves, rather than assumes, `llvm.load` monotone in CTrees, with the types
of its results proved as well.
-/
theorem llvm_load_interpretCTreeMonotone_not_assumed : InterpretCTreeMonotone (.llvm .load) :=
  inferInstance

/--
info: 'Veir.llvm_load_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms llvm_load_interpretCTreeMonotone_not_assumed

end Veir
