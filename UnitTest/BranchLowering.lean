import Veir.Passes.InstructionSelection.Branches.Pass

/-!
## Axioms of the refinement theorems

Pinned so that a change to the axioms the proofs rest on shows up here: those of the refinement
proofs of a `BranchLowering`, and those of the theorems about the pass and about it as
registered. The CTree theorems rest on the axioms of `CTree.Sim`, and all on the three facts that
`bv_decide` checks natively for `compareBranch_holds`. The CTree theorems that do not ask for the
opcodes of the module to be proved monotone assume that the others are
(`OpCode.interpretCTree_monotone_assumed`), and compose simulations (`CTree.Sim.trans_rel`) to
see what the source of an operation with `Interp` semantics returns; none assumes anything else
about the interpreter.
-/

/--
info: 'Veir.BranchLowering.isModuleRefinedByCTree' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub,
 Veir.compareBranch_holds._native.bv_decide.ax_1_15✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_20✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_25✝]
-/
#guard_msgs in
#print axioms Veir.BranchLowering.isModuleRefinedByCTree

/--
info: 'Veir.BranchLowering.isModuleRefinedBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Veir.compareBranch_holds._native.bv_decide.ax_1_15✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_20✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_25✝]
-/
#guard_msgs in
#print axioms Veir.BranchLowering.isModuleRefinedBy

/--
info: 'Veir.convertModule_isModuleRefinedByCTree' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.trans_rel,
 CTree.Sim.ub,
 Veir.OpCode.interpretCTree_monotone_assumed,
 Veir.compareBranch_holds._native.bv_decide.ax_1_15✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_20✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_25✝]
-/
#guard_msgs in
#print axioms Veir.convertModule_isModuleRefinedByCTree

/--
info: 'Veir.convertModule_isModuleRefinedByCTree_of_treeMonotoneProved' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub,
 Veir.compareBranch_holds._native.bv_decide.ax_1_15✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_20✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_25✝]
-/
#guard_msgs in
#print axioms Veir.convertModule_isModuleRefinedByCTree_of_treeMonotoneProved

/--
info: 'Veir.convertModule_isModuleRefinedBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Veir.compareBranch_holds._native.bv_decide.ax_1_15✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_20✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_25✝]
-/
#guard_msgs in
#print axioms Veir.convertModule_isModuleRefinedBy

/--
info: 'Veir.ISelBrPass.run_isModuleRefinedByCTree' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.trans_rel,
 CTree.Sim.ub,
 Veir.OpCode.interpretCTree_monotone_assumed,
 Veir.compareBranch_holds._native.bv_decide.ax_1_15✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_20✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_25✝]
-/
#guard_msgs in
#print axioms Veir.ISelBrPass.run_isModuleRefinedByCTree

/--
info: 'Veir.ISelBrPass.run_isModuleRefinedBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Veir.compareBranch_holds._native.bv_decide.ax_1_15✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_20✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_25✝]
-/
#guard_msgs in
#print axioms Veir.ISelBrPass.run_isModuleRefinedBy

/--
info: 'Veir.ISelBrPass.run_strict_isModuleRefinedByCTree' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub,
 Veir.compareBranch_holds._native.bv_decide.ax_1_15✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_20✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_25✝]
-/
#guard_msgs in
#print axioms Veir.ISelBrPass.run_strict_isModuleRefinedByCTree

/--
info: 'Veir.ISelBrPass.run_strict_isModuleRefinedBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Veir.compareBranch_holds._native.bv_decide.ax_1_15✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_20✝,
 Veir.compareBranch_holds._native.bv_decide.ax_1_25✝]
-/
#guard_msgs in
#print axioms Veir.ISelBrPass.run_strict_isModuleRefinedBy
