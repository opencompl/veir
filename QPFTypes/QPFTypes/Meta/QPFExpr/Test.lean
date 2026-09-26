module

import Lean

import QPFTypes.Meta.QPFExpr.Basic

/-!
# QPFExpr Unit Tests

Test that the QPFExpr meta helpers generate well-typed expressions.
-/

namespace QPFTypes.QPFExpr
open Lean

/-- Check that all compoments of a QPFExpr all well-typed, or throw an error if not. -/
def check (e : QPFExpr u n) : MetaM Unit := do
  Meta.check e.typefun
  Meta.check e.qpf

namespace Test

meta def u : Level := 0
meta abbrev n : Nat := 3

/-- `F₀ #v[α, β, γ].get = α` -/
meta def F₀ : QPFExpr u n :=
  mkProj _ 0

run_meta F₀.check

/-- `F₂ #v[α, β, γ].get = γ` -/
meta def F₂ : QPFExpr u n :=
  mkProj _ 2

run_meta F₂.check
