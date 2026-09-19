module

public meta import Lean

public import QPFTypes.Theory.QPF.Basic
public import QPFTypes.Theory.QPF.Cofix
public import QPFTypes.Theory.QPF.Fix

/-!
# QPFExpr

This file defines a `QPFExpr` type, which stores a Lean expression of an
`n`-ary type function, with a correponding QPF instance.

Morally, this can be thought of as a specialization of QQ's `Q(...)` type,
with additional helpers specifically for manipulating QPFs in meta-code.
-/
public section
namespace QPFTypes
open Lean (Level Expr)

/--
A `QPFExpr u n` represents an `n`-ary type function,
with corresponding QPF instance, on the meta-level.
-/
meta structure QPFExpr (u : Level) (n : Nat) where
  /--
  `QPFExpr.typefun` is the `n`-ary type function itself, as a Lean expression of type
    `TypeVec.{u} n → Type u`
  -/
  typefun : Expr
  /--
  `QPFExpr.qpf` is the corresponding `QPF` instance, i.e., a Lean expression of
  type `QPF.{$u, $u} $n $typefun`.
  -/
  qpf : Expr


/-!
NOTE: In future, `QPFExpr` may be replaced by an inductive, with a special case
for polynomial functors (i.e., type functors defined as `PFunctor.Obj P` for
some polynomial functor `P`), so that helpers like `mkCofix` preserve the fact
this is a polynomical functor. The projections `QPFExpr.F` and `QPFExpr.qpf`

This is desirable because, e.g., the cofixpoint construction of a polynomial
functor has better def-eqs than the cofixpoint construction for general QPFs.
-/

namespace QPFExpr


/-!
## Meta Helpers
-/
namespace QPFExpr
open Lean

/--
Create the least/inductive fixpoint of a qpf, i.e., an application of `QPF.Fix`.
-/
meta def mkFix (e : QPFExpr u (n + 1)) : QPFExpr u n where
  typefun := mkApp3 (mkConst ``QPF.Fix [u]) (toExpr n) e.typefun e.qpf
  qpf     := mkApp3 (mkConst ``QPF.qpfFix [u]) (toExpr n) e.typefun e.qpf

/--
Create the greates/coinductive fixpoint of a qpf,
i.e., an application of `QPF.Cofix`.
-/
meta def mkCofix (e : QPFExpr u (n + 1)) : QPFExpr u n where
  typefun := mkApp3 (mkConst ``QPF.Cofix [u]) (toExpr n) e.typefun e.qpf
  qpf     := mkApp3 (mkConst ``QPF.qpfCofix [u]) (toExpr n) e.typefun e.qpf

-- TODO: composition, projection and sigma-types.
--       These are currently all blocked on the relevant QPF construction not
--       yet being ported from Mathlib.
-- /--
-- Compose an `n`-ary QPF `F` with `n` `m`-ary QPFs `Gs`, i.e.,
-- create an application of `QPF.Comp
-- -/
-- meta def mkComp (F : Raw u n) (Gs : Vector (Raw u m) n) : Raw u m :=
--   sorry
