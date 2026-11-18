import Veir.Dialects.Monotonicity

/-!
Test that an opcode proved monotone in CTrees depends on the `Sim` axioms only, and one proved
monotone in `Interp` on the standard axioms only.
-/

namespace Veir

/--
Instance resolution proves, rather than assumes, every builtin opcode monotone in CTrees, with the
types of its results proved as well.
-/
theorem builtin_interpretCTreeMonotone_not_assumed (op : Builtin) :
    InterpretCTreeMonotone (.builtin op) :=
  inferInstance

/--
info: 'Veir.builtin_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms builtin_interpretCTreeMonotone_not_assumed

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

/--
Instance resolution proves, rather than assumes, every RISC-V opcode monotone in CTrees, with
the types of its results proved as well.
-/
theorem riscv_interpretCTreeMonotone_not_assumed (op : Riscv) :
    InterpretCTreeMonotone (.riscv op) := by
  cases op <;> exact inferInstance

/--
info: 'Veir.riscv_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms riscv_interpretCTreeMonotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `cf` opcode monotone in CTrees, with the
types of its results proved as well.
-/
theorem cf_interpretCTreeMonotone_not_assumed (op : Cf) :
    InterpretCTreeMonotone (.cf op) :=
  inferInstance

/--
info: 'Veir.cf_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms cf_interpretCTreeMonotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `riscv_cf` opcode monotone in CTrees, with the
types of its results proved as well.
-/
theorem riscv_cf_interpretCTreeMonotone_not_assumed (op : Riscv_Cf) :
    InterpretCTreeMonotone (.riscv_cf op) :=
  inferInstance

/--
info: 'Veir.riscv_cf_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms riscv_cf_interpretCTreeMonotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `gmir_riscv` opcode monotone in CTrees, with the
types of its results proved as well.
-/
theorem gmirRiscv_interpretCTreeMonotone_not_assumed (op : GMIR_RISCV) :
    InterpretCTreeMonotone (.gmir_riscv op) :=
  inferInstance

/--
info: 'Veir.gmirRiscv_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms gmirRiscv_interpretCTreeMonotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `riscv_stack` opcode monotone in CTrees, with the
types of its results proved as well.
-/
theorem riscvStack_interpretCTreeMonotone_not_assumed (op : Riscv_Stack) :
    InterpretCTreeMonotone (.riscv_stack op) :=
  inferInstance

/--
info: 'Veir.riscvStack_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms riscvStack_interpretCTreeMonotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `func` opcode monotone in CTrees, with the
types of its results proved as well.
-/
theorem func_interpretCTreeMonotone_not_assumed (op : Func) :
    InterpretCTreeMonotone (.func op) :=
  inferInstance

/--
info: 'Veir.func_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms func_interpretCTreeMonotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `test` opcode monotone in CTrees, with the
types of its results proved as well.
-/
theorem test_interpretCTreeMonotone_not_assumed (op : Test) :
    InterpretCTreeMonotone (.test op) :=
  inferInstance

/--
info: 'Veir.test_interpretCTreeMonotone_not_assumed' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.ret,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms test_interpretCTreeMonotone_not_assumed

/-! ## In `Interp` -/

/--
Instance resolution proves, rather than assumes, every `cf` opcode monotone in `Interp`, in its
operands and its memory.
-/
theorem cf_interpretOp'Monotone_not_assumed (op : Cf) :
    InterpretOp'Monotone (.cf op) :=
  inferInstance

/--
info: 'Veir.cf_interpretOp'Monotone_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cf_interpretOp'Monotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `riscv_cf` opcode monotone in `Interp`, in its
operands and its memory.
-/
theorem riscv_cf_interpretOp'Monotone_not_assumed (op : Riscv_Cf) :
    InterpretOp'Monotone (.riscv_cf op) :=
  inferInstance

/--
info: 'Veir.riscv_cf_interpretOp'Monotone_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms riscv_cf_interpretOp'Monotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `gmir_riscv` opcode monotone in `Interp`, in its
operands and its memory.
-/
theorem gmirRiscv_interpretOp'Monotone_not_assumed (op : GMIR_RISCV) :
    InterpretOp'Monotone (.gmir_riscv op) :=
  inferInstance

/--
info: 'Veir.gmirRiscv_interpretOp'Monotone_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms gmirRiscv_interpretOp'Monotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `riscv_stack` opcode monotone in `Interp`, in its
operands and its memory.
-/
theorem riscvStack_interpretOp'Monotone_not_assumed (op : Riscv_Stack) :
    InterpretOp'Monotone (.riscv_stack op) :=
  inferInstance

/--
info: 'Veir.riscvStack_interpretOp'Monotone_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms riscvStack_interpretOp'Monotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `func` opcode monotone in `Interp`, in its
operands and its memory.
-/
theorem func_interpretOp'Monotone_not_assumed (op : Func) :
    InterpretOp'Monotone (.func op) :=
  inferInstance

/--
info: 'Veir.func_interpretOp'Monotone_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms func_interpretOp'Monotone_not_assumed

/--
Instance resolution proves, rather than assumes, every `test` opcode monotone in `Interp`, in its
operands and its memory.
-/
theorem test_interpretOp'Monotone_not_assumed (op : Test) :
    InterpretOp'Monotone (.test op) :=
  inferInstance

/--
info: 'Veir.test_interpretOp'Monotone_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test_interpretOp'Monotone_not_assumed

/--
Instance resolution proves, rather than assumes, `builtin.module` monotone in `Interp`. The casts
are monotone only in CTrees, which `builtin_interpretCTreeMonotone_not_assumed` pins.
-/
theorem builtin_module_interpretOp'Monotone_not_assumed :
    InterpretOp'Monotone (.builtin .module) :=
  inferInstance

/--
info: 'Veir.builtin_module_interpretOp'Monotone_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms builtin_module_interpretOp'Monotone_not_assumed

end Veir
