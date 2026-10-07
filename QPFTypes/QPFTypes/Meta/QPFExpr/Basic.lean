module

public meta import Lean

public import QPFTypes.Theory.TypeFun
public import QPFTypes.Theory.QPF

public meta import QPFTypes.Meta.QPFExpr.FinTuple

/-!
# QPFExpr

This file defines a `QPFExpr` type, which stores a Lean expression of an
`n`-ary type function, with a correponding QPF instance.

Morally, this can be thought of as a specialization of QQ's `Q(...)` type,
with additional helpers specifically for manipulating QPFs in meta-code.
-/
meta section
namespace QPFTypes
open Lean (Level Expr)

/--
A `QPFExpr u n` represents an `n`-ary type function,
with corresponding QPF instance, on the meta-level.

The given universe level `u` indicates the type universe of the QPF.
Note that while the theory permits QPFs where the arguments live in a different
universe from the resulting type, `QPFExpr` only represent those QPFs for which
both universe levels coincide (and are the given level `u`).

See also `QPFTupleExpr`.
-/
public meta structure QPFExpr (u : Level) (n : Nat) where
  /--
  `QPFExpr.typefun` is the `n`-ary type function itself, as a Lean expression of type
    `TypeFun.{$u, $u} $n → Type $u`
  -/
  typefun : Expr
  /--
  `QPFExpr.qpf` is the corresponding `QPF` instance, i.e., a Lean expression of
  type `QPF.{$u, $u} $typefun`.
  -/
  qpf : Expr
  /--
  `QPFExpr.isPolynomial?` contains a corresponding `IsPolynomial` instance
  (i.e., an expression of type `IsPolynomial.{$u} $typefun`),
  if the typefunction is indeed (isomorphic to) a polynomial functor.
  -/
  isPolynomial? : Option Expr

/--
A `QPFTupleExpr u n m` represents `m`-tuple of `n`-ary type functions,
with corresponding QPF instances, on the meta-level.

Note: this is an object-level tuple, meaning that each component is a single
Lean expression, of type `Fin $m → …`, rather than being a tuple of Lean
expressions.

See `QPFExpr` for the analogue of a single type function.
-/
public meta structure QPFTupleExpr (u : Level) (n m : Nat) where
  /--
  `typefun` is the `m`-tuple `n`-ary type function itself, as a Lean expression
  of type `Fin $m → TypeFun.{$u, $u} $n → Type $u`
  -/
  typefun : Expr
  /--
  `qpf` is the tuple of QPF instances corresponding to `typefun`, i.e., an
  expression of type `(i : Fin $m) → QPF.{$u, $u} ($typefun i)`
  -/
  qpf : Expr
  /--
  `isPolynomial?` optionally has the tuple of corresponding `QPF.IsPolynomial`
  instances, meaning an expression of type:
    `(i : Fin $m) → QPF.IsPolynomial.{$u} ($typefun i)`

  NOTE: this is `some _` only if *all* QPFs in the tuple are polynomial.
  -/
  isPolynomial? : Option Expr

/-!
## QPFTupleExpr API
-/
namespace QPFTupleExpr
open Lean

/--
Construct an `QPFTupleExpr` given a vector of `QPFExpr`s.

This intuitively translate each component from the meta-level vector of
expressions to a single expression of an object-level tuple.
-/
public meta def ofVector (Gs : Vector (QPFExpr u m) n) : MetaM (QPFTupleExpr u m n) := do
  let n := toExpr n
  let m := toExpr m

  let typefun ← do
    let typefun := mkApp (mkConst ``TypeFun [u, u]) m
    Fin.mkTuple typefun (Gs.map (·.typefun))
  let qpf ← do
    let qpfType := -- `fun (i : Fin $n) => @QPF.{$u, $u} $m ($typefun i)`
      .lam `i (mkApp (mkConst ``Fin) n)
        (mkApp2 (mkConst ``QPF [u, u]) m (mkApp typefun (.bvar 0)))
        .default
    Fin.mkDTuple qpfType (Gs.map (·.qpf))
  let isPolynomial? ← (Gs.mapM (QPFExpr.isPolynomial? ·)).mapM fun GsPoly => do
    let polyType := -- `fun (i : Fin $n) => @IsPolynomial.{$u} $m ($typefun i) ($qpf i)`
      .lam `i (mkApp (mkConst ``Fin) n)
        (mkApp3 (mkConst ``QPF.IsPolynomial [u]) m
          (mkApp typefun (.bvar 0)) (mkApp qpf (.bvar 0)))
        .default
    Fin.mkDPropTuple polyType GsPoly
  return { typefun, qpf, isPolynomial? }

end QPFTupleExpr

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
  isPolynomial? := e.isPolynomial?.map fun isPoly =>
    mkApp4 (mkConst ``QPF.Fix.instIsPolynomial [u]) (toExpr n) e.typefun e.qpf isPoly

/--
Create the greates/coinductive fixpoint of a qpf,
i.e., an application of `QPF.Cofix`.
-/
public meta def mkCofix (e : QPFExpr u (n + 1)) : QPFExpr u n where
  typefun := mkApp3 (mkConst ``QPF.Cofix [u]) (toExpr n) e.typefun e.qpf
  qpf     := mkApp3 (mkConst ``QPF.qpfCofix [u]) (toExpr n) e.typefun e.qpf
  isPolynomial? := e.isPolynomial?.map fun isPoly =>
    mkApp4 (mkConst ``QPF.Cofix.instIsPolynomial [u]) (toExpr n) e.typefun e.qpf isPoly

/--
Create the `i`-th `n`-ary projection QPF, i.e., the `n`-ary type function
`fun αs => αs i`, as an application of `QPF.Prj`.
-/
public meta def mkProj (u : Level) {n : Nat} (i : Fin n) : QPFExpr u n where
  typefun := mkApp2 (mkConst ``QPF.Prj [u]) (toExpr n) (toExpr i)
  qpf     := mkApp2 (mkConst ``QPF.Prj.qpf [u]) (toExpr n) (toExpr i)
  isPolynomial? := some <|
    mkApp2 (mkConst ``QPF.Prj.instIsPolynomial [u]) (toExpr n) (toExpr i)

/--
Create the constant `n`-ary QPF on `A`, i.e., the `n`-ary type function
`fun _ => A`, as an application of `QPF.Const`.

Note that this is called `mkConstant`, rather than `mkConst`, to avoid shadowing
`Lean.mkConst`.
-/
public meta def mkConstant (u : Level) (n : Nat) (A : Expr /- : Type $u -/) : QPFExpr u n where
  typefun := mkApp2 (mkConst ``QPF.Const [u]) (toExpr n) A
  qpf     := mkApp2 (mkConst ``QPF.Const.qpf [u]) (toExpr n) A
  isPolynomial? := some <|
    mkApp2 (mkConst ``QPF.Const.instIsPolynomial [u]) (toExpr n) A

/--
Create a dependent sum or product of a family of `n`-ary QPFs, depending on
which triple of `QPF.Sigma`/`QPF.Sigma.qpf`/`QPF.Sigma.instIsPolynomial` or
`QPF.Pi`/`QPF.Pi.qpf`/`QPF.Pi.instIsPolynomial` is passed in.

Private auxiliary definition for `mkSigma` and `mkPi`.
-/
private meta def mkDepFamily (typefunConst qpfConst isPolyConst : Name)
    (u : Level) (n : Nat) (A : Expr /- : Type $u -/)
    (family : Expr → MetaM (QPFExpr u n)) : MetaM (QPFExpr u n) :=
  Meta.withLocalDeclD `a A fun a => do
    let Fa ← family a
    -- `fun (a : $A) => $(Fa.typefun) : $A → TypeFun.{$u} $n`
    let Ftypefun ← Meta.mkLambdaFVars #[a] Fa.typefun
    -- `fun (a : $A) => $(Fa.qpf) : (a : $A) → QPF.{$u, $u} $n ($Ftypefun a)`
    let Fqpf ← Meta.mkLambdaFVars #[a] Fa.qpf
    return {
      typefun := mkApp3 (mkConst typefunConst [u]) (toExpr n) A Ftypefun
      qpf := mkApp4 (mkConst qpfConst [u]) (toExpr n) A Ftypefun Fqpf
      isPolynomial? := ← Fa.isPolynomial?.mapM fun FisPoly => do
        let FisPoly ← Meta.mkLambdaFVars #[a] FisPoly
        return mkApp5 (mkConst isPolyConst [u]) (toExpr n) A Ftypefun Fqpf FisPoly
    }

/--
Create the dependent sum of a family of `n`-ary QPFs,
i.e., an application of `QPF.Sigma`.

The family is described by `A`, an expression of type `Type $u`, together with
the monadic function `family`, which is given a free variable `a : $A` and is
expected to return the `n`-ary QPF `$F a` as a QPFExpr.

Note that the index type `$A` must live in the *same* universe `$u` as the
QPFs in the family.
-/
public meta def mkSigma (u : Level) (n : Nat) (A : Expr /- : Type $u -/)
    (family : Expr → MetaM (QPFExpr u n)) : MetaM (QPFExpr u n) :=
  mkDepFamily ``QPF.Sigma ``QPF.Sigma.qpf ``QPF.Sigma.instIsPolynomial u n A family

/--
Create the dependent product of a family of `n`-ary QPFs,
i.e., an application of `QPF.Pi`.

The family is described by `A`, an expression of type `Type $u`, together with
the monadic function `family`, which is given a free variable `a : $A` and is
expected to return the `n`-ary QPF `$F a` as a QPFExpr.

Since a non-dependent function type `$A → $B` is just a trivial/degenerate
dependent product, this is also how function types (which are functorial in
their codomain, but not in their domain) are represented.
-/
public meta def mkPi (u : Level) (n : Nat) (A : Expr /- : Type $u -/)
    (family : Expr → MetaM (QPFExpr u n)) : MetaM (QPFExpr u n) :=
  mkDepFamily ``QPF.Pi ``QPF.Pi.qpf ``QPF.Pi.instIsPolynomial u n A family

/--
Compose an `n`-ary QPF `F` with `n` `m`-ary QPFs `Gs`, i.e.,
create an application of `QPF.Comp
-/
public meta def mkComp (F : QPFExpr u n) (Gs : Vector (QPFExpr u m) n) :
    MetaM (QPFExpr u m) := do
  let G ← QPFTupleExpr.ofVector Gs
  let n := toExpr n
  let m := toExpr m
  return {
    typefun := mkApp4 (mkConst ``QPF.Comp [u, u]) n m F.typefun G.typefun
    qpf     := mkApp6 (mkConst ``QPF.Comp.inst [u, u]) n m F.typefun G.typefun F.qpf G.qpf
    isPolynomial? := do
      let FisPoly ← F.isPolynomial?
      let GisPoly ← G.isPolynomial?
      return mkApp8 (mkConst ``QPF.Comp.instIsPolynomial [u])
        n m F.typefun G.typefun F.qpf G.qpf FisPoly GisPoly
  }
