import Veir.Dialects.Monotonicity

/-! Test that an opcode proved monotone in CTrees depends on the `Sim` axioms only. -/

namespace Veir

/--
Instance resolution proves, rather than assumes, every LLVM opcode monotone in CTrees, with the
types of its results proved as well.
-/
theorem llvm_interpretCTreeMonotone_not_assumed (op : Llvm) : InterpretCTreeMonotone (.llvm op) := by
  cases op <;> exact inferInstance

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
Instance resolution proves, rather than assumes, every gMIR opcode monotone in CTrees, with the
types of its results proved as well.
-/
theorem gmir_interpretCTreeMonotone_not_assumed (op : GMIR) : InterpretCTreeMonotone (.gmir op) := by
  cases op <;> exact inferInstance

/--
info: 'Veir.gmir_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms gmir_interpretCTreeMonotone_not_assumed

end Veir
