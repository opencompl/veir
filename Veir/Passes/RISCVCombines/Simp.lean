module

import Lean
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.Simproc
public meta import Lean.Meta.Tactic.Simp.Attr

public section

/-- Simp set reducing a normalized RISC-V combine validity goal to register equalities. -/
register_simp_attr riscv_combine

/- Simp set unfolding the RISC-V combine patterns. -/
register_simp_attr riscv_pattern
