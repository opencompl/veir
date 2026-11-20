module

import Lean
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.Simproc
public meta import Lean.Meta.Tactic.Simp.Attr

public section

/-- Simp set for Puddle constraints, operation interpreters, and simulations. -/
register_simp_attr puddle
