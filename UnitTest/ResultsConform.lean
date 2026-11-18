import Veir.Dialects.ResultsConform

/-! Test that a given dialect's conformance depends only on Lean's standard axioms. -/

namespace Veir

theorem builtin_resultsConform_not_assumed (op : Builtin) : ResultsConform (.builtin op) :=
  inferInstance

/--
info: 'Veir.builtin_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms builtin_resultsConform_not_assumed

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

theorem riscv_cf_resultsConform_not_assumed (op : Riscv_Cf) : ResultsConform (.riscv_cf op) :=
  inferInstance

/--
info: 'Veir.riscv_cf_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms riscv_cf_resultsConform_not_assumed

theorem gmir_riscv_resultsConform_not_assumed (op : GMIR_RISCV) : ResultsConform (.gmir_riscv op) :=
  inferInstance

/--
info: 'Veir.gmir_riscv_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms gmir_riscv_resultsConform_not_assumed

theorem riscv_stack_resultsConform_not_assumed (op : Riscv_Stack) : ResultsConform (.riscv_stack op) :=
  inferInstance

/--
info: 'Veir.riscv_stack_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms riscv_stack_resultsConform_not_assumed

theorem func_resultsConform_not_assumed (op : Func) : ResultsConform (.func op) :=
  inferInstance

/--
info: 'Veir.func_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms func_resultsConform_not_assumed

theorem test_resultsConform_not_assumed (op : Test) : ResultsConform (.test op) :=
  inferInstance

/--
info: 'Veir.test_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test_resultsConform_not_assumed

end Veir
