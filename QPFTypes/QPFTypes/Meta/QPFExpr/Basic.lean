module

public meta import Lean

public import QPFTypes.Theory.TypeFun

public import QPFTypes.Theory.QPF.Basic
public import QPFTypes.Theory.QPF.Cofix
public import QPFTypes.Theory.QPF.Fix
public import QPFTypes.Theory.QPF.Comp
public import QPFTypes.Theory.QPF.Prj
public import QPFTypes.Theory.QPF.Sigma

public meta import QPFTypes.Meta.QPFExpr.FinTuple
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

/--
Create the `i`-th `n`-ary projection QPF, i.e., the `n`-ary type function
`fun αs => αs i`, as an application of `QPF.Prj`.
-/
public meta def mkProj (u : Level) {n : Nat} (i : Fin n) : QPFExpr u n where
  typefun := mkApp2 (mkConst ``QPF.Prj [u]) (toExpr n) (toExpr i)
  qpf     := mkApp2 (mkConst ``QPF.Prj.qpf [u]) (toExpr n) (toExpr i)

/--
Create the dependent sum of a family of `n`-ary QPFs,
i.e., an application of `QPF.Sigma`.

The family is described by `A`, an expression of type `Type $u`, together with
`family`, which is given a free variable `a : $A` and is expected to return the
`n`-ary QPF `$F a`. Both components of the result are then lambdas abstracting
over this variable, so that the sum ranges over all of `$A`.

Note that the index type `$A` must live in the *same* universe `$u` as the
QPFs in the family.
-/
public meta def mkSigma (u : Level) (n : Nat) (A : Expr /- : Type $u -/)
    (family : Expr → MetaM (QPFExpr u n)) : MetaM (QPFExpr u n) :=
  Meta.withLocalDeclD `a A fun a => do
    let Fa ← family a
    -- `fun (a : $A) => $(Fa.typefun) : $A → TypeFun.{$u} $n`
    let Ftypefun ← Meta.mkLambdaFVars #[a] Fa.typefun
    -- `fun (a : $A) => $(Fa.qpf) : (a : $A) → QPF.{$u, $u} $n ($Ftypefun a)`
    let Fqpf ← Meta.mkLambdaFVars #[a] Fa.qpf
    return {
      typefun := mkApp3 (mkConst ``QPF.Sigma [u]) (toExpr n) A Ftypefun
      qpf := mkApp4 (mkConst ``QPF.Sigma.qpf [u]) (toExpr n) A Ftypefun Fqpf
    }

/--
Compose an `n`-ary QPF `F` with `n` `m`-ary QPFs `Gs`, i.e.,
create an application of `QPF.Comp
-/
public meta def mkComp (F : QPFExpr u n) (Gs : Vector (QPFExpr u m) n) :
    MetaM (QPFExpr u m) := do
  let n := toExpr n
  let m := toExpr m


  let Gtypefun ← do
    let typefun := mkApp (mkConst ``TypeFun [u, u]) m
    Fin.mkTuple typefun (Gs.map (·.typefun))
  let Gqpf ← do
    let qpfType := -- `fun (i : Fin $n) => @QPF.{$u, $u} $m ($Gtypefun i)`
      .lam `i (mkApp (mkConst ``Fin) n)
        (mkApp2 (mkConst ``QPF [u, u]) m (mkApp Gtypefun (.bvar 0)))
        .default
    Fin.mkDTuple qpfType (Gs.map (·.qpf))

  return {
    typefun := mkApp4 (mkConst ``QPF.Comp [u, u]) n m F.typefun Gtypefun
    qpf := mkApp6 (mkConst ``QPF.Comp.inst [u, u]) n m F.typefun Gtypefun F.qpf Gqpf
  }
