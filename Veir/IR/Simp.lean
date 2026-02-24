module

import Lean
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.Simproc
public meta import Lean.Meta.Tactic.Simp.Attr

public section

/- Simp set converting safe operations to their unsafe (!) counterparts. -/
register_simp_attr eq_bang
