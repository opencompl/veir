module

public meta import Lean

public import QPFTypes.Theory.TypeFun
public import QPFTypes.Theory.QPF

/-!
# QPFExpr

This file defines a `QPFExpr` type, which stores a Lean expression of an
`n`-ary type function, with a correponding QPF instance.

Morally, this can be thought of as a specialization of QQ's `Q(...)` type,
with additional helpers specifically for manipulating QPFs in meta-code.
-/
namespace QPFTypes
open Lean (Level Expr)

/--
A `QPFExpr u n` represents an `n`-ary type function,
with corresponding QPF instance, on the meta-level.

The given universe level `u` indicates the type universe of the QPF.
Note that while the theory permits QPFs where the arguments live in a different
universe from the resulting type, `QPFExpr` only represent those QPFs for which
both universe levels coincide (and are the given level `u`).
-/
public meta structure QPFExpr (u : Level) (n : Nat) where
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

/-!
## Meta Helpers
-/
namespace QPFExpr
open Lean

/--
Create the least/inductive fixpoint of a qpf, i.e., an application of `QPF.Fix`.
-/
public meta def mkFix (e : QPFExpr u (n + 1)) : QPFExpr u n where
  typefun := mkApp3 (mkConst ``QPF.Fix [u]) (toExpr n) e.typefun e.qpf
  qpf     := mkApp3 (mkConst ``QPF.qpfFix [u]) (toExpr n) e.typefun e.qpf

/--
Create the greates/coinductive fixpoint of a qpf,
i.e., an application of `QPF.Cofix`.
-/
public meta def mkCofix (e : QPFExpr u (n + 1)) : QPFExpr u n where
  typefun := mkApp3 (mkConst ``QPF.Cofix [u]) (toExpr n) e.typefun e.qpf
  qpf     := mkApp3 (mkConst ``QPF.qpfCofix [u]) (toExpr n) e.typefun e.qpf
