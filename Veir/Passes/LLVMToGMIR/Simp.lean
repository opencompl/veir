module

import Lean
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.Simproc
public meta import Lean.Meta.Tactic.Simp.Attr

public section

/-- Simp set reducing an `llvm-to-gmir` validity goal, after `simpPuddleValid`, to a goal over the
values of the matched operations. -/
register_simp_attr llvm_to_gmir

/- Simp set unfolding the `llvm-to-gmir` patterns. -/
register_simp_attr llvm_to_gmir_pattern

/-- The `Pattern.Valid` proof of each `llvm-to-gmir` pattern, looked up by
`llvmToGMIRPatternList_valid`. -/
register_simp_attr llvm_to_gmir_valid
