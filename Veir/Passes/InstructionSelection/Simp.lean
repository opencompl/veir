module

import Lean
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.Simproc
public meta import Lean.Meta.Tactic.Simp.Attr

public section

/- Simp set unfolding the instruction-selection patterns and the builders they use. -/
register_simp_attr isel_pattern
