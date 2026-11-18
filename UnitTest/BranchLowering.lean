import Veir.Passes.InstructionSelection.Branches.Pass

/-!
## Axioms of the refinement theorem

Pinned so that a change to the axioms the proof rests on shows up here. The theorem rests on the
axioms of `CTree.Sim` and on the three facts that `bv_decide` checks natively for
`compareBranch_holds`; it assumes nothing about the interpreter.
-/

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
