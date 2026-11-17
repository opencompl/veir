import Veir.Dialects.ResultsConform

/-! Test that a given dialect's conformance depends only on Lean's standard axioms. -/

namespace Veir

theorem cf_resultsConform_not_assumed (op : Cf) : ResultsConform (.cf op) :=
  inferInstance

/--
info: 'Veir.cf_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cf_resultsConform_not_assumed

/--
Instance resolution proves, rather than assumes, the conformance of the results of the CTree of
every LLVM opcode: the proof of each opcode wins over the assumption.
-/
theorem llvm_resultsConform_not_assumed (op : Llvm) : ResultsConform (.llvm op) := by
  cases op <;> exact inferInstance

/--
info: 'Veir.llvm_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms llvm_resultsConform_not_assumed

/--
info: 'Veir.Llvm.interpretCTree_results_conform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Llvm.interpretCTree_results_conform

theorem gmir_resultsConform_not_assumed (op : GMIR) : ResultsConform (.gmir op) :=
  inferInstance

/--
info: 'Veir.gmir_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms gmir_resultsConform_not_assumed

theorem riscv_resultsConform_not_assumed (op : Riscv) : ResultsConform (.riscv op) :=
  inferInstance

/--
info: 'Veir.riscv_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms riscv_resultsConform_not_assumed

end Veir
