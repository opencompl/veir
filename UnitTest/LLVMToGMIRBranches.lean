import Veir.Passes.LLVMToGMIR.BranchPass

/-!
## Axioms of the refinement theorems

Pinned so that a change to the axioms the proofs rest on shows up here. The
theorems rest on the axioms of `CTree.Sim`, but not on `CTree.Sim.trans_rel`: the
simulation relates refined states directly. The theorem for a module that verifies
assumes that the opcodes without a proof are monotone in CTrees
(`OpCode.interpretCTree_monotone_assumed`); the one for opcodes proved monotone
assumes nothing about the interpreter.
-/

/--
info: 'Veir.LLVMBranchTranslation.isModuleRefinedByCTree' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms Veir.LLVMBranchTranslation.isModuleRefinedByCTree

/--
info: 'Veir.convertLLVMBranches_translation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Veir.convertLLVMBranches_translation

/--
info: 'Veir.convertLLVMBranches_isModuleRefinedByCTree_of_treeMonotoneProved' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms Veir.convertLLVMBranches_isModuleRefinedByCTree_of_treeMonotoneProved

/--
info: 'Veir.convertLLVMBranches_isModuleRefinedByCTree' depends on axioms: [propext,
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
 Veir.OpCode.interpretCTree_monotone_assumed]
-/
#guard_msgs in
#print axioms Veir.convertLLVMBranches_isModuleRefinedByCTree
