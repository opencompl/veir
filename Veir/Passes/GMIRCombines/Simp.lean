module

import Lean
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.Simproc
public meta import Lean.Meta.Tactic.Simp.Attr

public section

/-- Simp set reducing a gMIR combine validity goal, after `simpPuddleValid`, to a goal over the
values of the matched operations. -/
register_simp_attr gmir_combine

/- Simp set unfolding the gMIR combine patterns and the builders they use. -/
register_simp_attr gmir_pattern

/-- The `Pattern.Valid` proof of each gMIR combine, looked up by the theorems of
`Veir.Passes.GMIRCombines.Validity.Pass` that every combine of the combiner passes is valid. -/
register_simp_attr combine_valid
