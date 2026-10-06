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
A `QPFExpr n` represents an `n`-ary type function,
with corresponding QPF instance, on the meta-level.

See also `QPFTupleExpr`.
-/
public meta structure QPFExpr (n : Nat) where
  /--
  `QPFExpr.domLevel` is the type universe of the arguments of the QPF.
  -/
  domLevel : Level
  /--
  `QPFExpr.codLevel` is the type universe of the resulting type of the QPF.
  -/
  codLevel : Level
  /--
  `QPFExpr.typefun` is the `n`-ary type function itself, as a Lean expression of type
    `TypeFun.{$domLevel, $codLevel} $n`
  -/
  typefun : Expr
  /--
  `QPFExpr.qpf` is the corresponding `QPF` instance, i.e., a Lean expression of
  type `QPF.{$domLevel, $codLevel} $typefun`.
  -/
  qpf : Expr
  /--
  `QPFExpr.isPolynomial?` contains a corresponding `IsPolynomial` instance
  (i.e., an expression of type `IsPolynomial.{$domLevel, $codLevel} $typefun`),
  if the typefunction is indeed (isomorphic to) a polynomial functor.
  -/
  isPolynomial? : Option Expr

/--
A `QPFTupleExpr n m` represents `m`-tuple of `n`-ary type functions,
with corresponding QPF instances, on the meta-level.

Note: this is an object-level tuple, meaning that each component is a single
Lean expression, of type `Fin $m → …`, rather than being a tuple of Lean
expressions.

See `QPFExpr` for the analogue of a single type function.
-/
public meta structure QPFTupleExpr (n m : Nat) where
  /--
  `domLevel` is the argument universe shared by all QPFs in the tuple.
  -/
  domLevel : Level
  /--
  `codLevel` is the result universe shared by all QPFs in the tuple.
  -/
  codLevel : Level
  /--
  `typefun` is the `m`-tuple `n`-ary type function itself, as a Lean expression
  of type `Fin $m → TypeFun.{$domLevel, $codLevel} $n`
  -/
  typefun : Expr
  /--
  `qpf` is the tuple of QPF instances corresponding to `typefun`, i.e., an
  expression of type `(i : Fin $m) → QPF.{$domLevel, $codLevel} ($typefun i)`
  -/
  qpf : Expr
  /--
  `isPolynomial?` optionally has the tuple of corresponding `QPF.IsPolynomial`
  instances, meaning an expression of type:
    `(i : Fin $m) → QPF.IsPolynomial.{$domLevel, $codLevel} ($typefun i)`

  NOTE: this is `some _` only if *all* QPFs in the tuple are polynomial.
  -/
  isPolynomial? : Option Expr

/-!
## SetLevelM
-/

namespace QPFExpr
open Lean

private def throwUniverseMismatchErr (q : QPFExpr n) (kind : MessageData)
    (actual expected : Level) : MetaM α := do
  throwError "Universe level mismatch: expected a QPF with {kind} in universe \
      level{indentD expected}\n\
      but the QPF{indentExpr q.typefun}\nhas {kind} in universe level{indentD actual}"

/--
Set the codomain level of a QPF to another (definitially equal) level `v`.

If `v` is not def-eq to the original codomain level, an error is thrown.

Note: this does not change the contained expressions, only the `codLevel` field.

For now, this only works for def-eq levels, but in future this may coerce the
QPF into a higher universe via a `ULift`-like construction.
-/
public def setCodLevelM (q : QPFExpr n) (v : Level) : MetaM (QPFExpr n) := do
  if ← Meta.isLevelDefEq q.codLevel v then
    let codLevel ← instantiateLevelMVars v
    return { q with codLevel }
  else
    q.throwUniverseMismatchErr "result type" q.codLevel v

/--
Throw an error if the (live) argument to `q` are not of type (def-eq to) `Type $u`.
-/
public def assertDomLevelDefEq (q : QPFExpr n) (u : Level) : MetaM Unit := do
  if ← Meta.isLevelDefEq q.domLevel u then
    return ()
  else
    q.throwUniverseMismatchErr "arguments" q.domLevel u

/--
Unify the domain and codomain levels of a QPF to be the same level,
by potentially lifting the latter via `setCodLevelM`.
-/
public def unifyLevels (q : QPFExpr n) : MetaM (QPFExpr n) := do
  q.setCodLevelM q.domLevel

end QPFExpr

/-!
## QPFTupleExpr API
-/
namespace QPFTupleExpr
open Lean

/--
Construct an `QPFTupleExpr` given a vector of `QPFExpr`s.

This intuitively translate each component from the meta-level vector of
expressions to a single expression of an object-level tuple.

All `QPFExpr` are expected to have the same domain level, and the same
codomain level. If this is not the case, an error is thrown.

Note that if `Gs` is empty, the resulting levels are unassigned level
metavariables.
-/
public meta def ofVector (Gs : Vector (QPFExpr m) n) :
    MetaM (QPFTupleExpr m n) := do
  -- assert all `G`s have the same domain level
  let u ← Meta.mkFreshLevelMVar
  let _ ← Gs.mapM (·.assertDomLevelDefEq u)
  let u ← instantiateLevelMVars u
  -- lift the codomain of each `G` into the max level
  let vs := Gs.map (·.codLevel)
  let v ← match _ : n with
    | 0 => Meta.mkFreshLevelMVar
    | _+1 => pure <| vs.tail.foldl mkLevelMax' vs[0]
  let Gs ← Gs.mapM (·.setCodLevelM v)
  let v ← instantiateLevelMVars v
  let n := toExpr n
  let m := toExpr m

  let typefun ← do
    let typefun := mkApp (mkConst ``TypeFun [u, v]) m
    Fin.mkTuple typefun (Gs.map (·.typefun))
  let qpf ← do
    let qpfType := -- `fun (i : Fin $n) => @QPF.{$u, $v} $m ($typefun i)`
      .lam `i (mkApp (mkConst ``Fin) n)
        (mkApp2 (mkConst ``QPF [u, v]) m (mkApp typefun (.bvar 0)))
        .default
    Fin.mkDTuple qpfType (Gs.map (·.qpf))
  let isPolynomial? ← (Gs.mapM (QPFExpr.isPolynomial? ·)).mapM fun GsPoly => do
    let polyType := -- `fun (i : Fin $n) => @IsPolynomial.{$u, $v} $m ($typefun i) ($qpf i)`
      .lam `i (mkApp (mkConst ``Fin) n)
        (mkApp3 (mkConst ``QPF.IsPolynomial [u, v]) m
          (mkApp typefun (.bvar 0)) (mkApp qpf (.bvar 0)))
        .default
    Fin.mkDPropTuple polyType GsPoly
  return { domLevel := u, codLevel := v, typefun, qpf, isPolynomial? }

/--
Set the domain and codomain levels of a tuple of QPFs to `u` and `v`,
respectively, which are checked to be def-eq to the original levels.

If either level is not def-eq, an error is thrown.

Note: this does not change the contained expressions, only the level fields.
-/
public meta def setLevelsM (G : QPFTupleExpr n m) (u v : Level) :
    MetaM (QPFTupleExpr n m) := do
  unless ← Meta.isLevelDefEq G.domLevel u <&&> Meta.isLevelDefEq G.codLevel v do
    throwError "Universe level mismatch: expected a tuple of QPFs in universe \
      levels{indentD m!"{u}, {v}"}\n\
      but the tuple of QPFs{indentExpr G.typefun}\nlives in universe levels\
      {indentD m!"{G.domLevel}, {G.codLevel}"}"
  let domLevel ← instantiateLevelMVars u
  let codLevel ← instantiateLevelMVars v
  return { G with domLevel, codLevel }

/--
Construct an `QPFTupleExpr`, given an array of `QPFExpr`s.

See `QPFTupleExpr.ofVector`
-/
public meta def ofArray (Gs : Array (QPFExpr m)) :
    MetaM (QPFTupleExpr m Gs.size) := do
  ofVector Gs.toVector

end QPFTupleExpr

namespace QPFExpr
open Lean

/-!
## Meta Constructors
-/

/--
Create the least/inductive fixpoint of a qpf, i.e., an application of `QPF.Fix`.

Throws an error if the domain and codomain levels of `e` are not def-eq.
-/
public meta def mkFix (e : QPFExpr (n + 1)) : MetaM (QPFExpr n) := do
  let e ← e.unifyLevels
  let u := e.domLevel
  return {
    domLevel := u
    codLevel := u
    typefun := mkApp3 (mkConst ``QPF.Fix [u]) (toExpr n) e.typefun e.qpf
    qpf     := mkApp3 (mkConst ``QPF.qpfFix [u]) (toExpr n) e.typefun e.qpf
    isPolynomial? := e.isPolynomial?.map fun isPoly =>
      mkApp4 (mkConst ``QPF.Fix.instIsPolynomial [u]) (toExpr n) e.typefun e.qpf isPoly
  }

/--
Create the greates/coinductive fixpoint of a qpf,
i.e., an application of `QPF.Cofix`.

Throws an error if the domain and codomain levels of `e` are not def-eq.
-/
public meta def mkCofix (e : QPFExpr (n + 1)) : MetaM (QPFExpr n) := do
  let e ← e.unifyLevels
  let u := e.domLevel
  return {
    domLevel := u
    codLevel := u
    typefun := mkApp3 (mkConst ``QPF.Cofix [u]) (toExpr n) e.typefun e.qpf
    qpf     := mkApp3 (mkConst ``QPF.qpfCofix [u]) (toExpr n) e.typefun e.qpf
    isPolynomial? := e.isPolynomial?.map fun isPoly =>
      mkApp4 (mkConst ``QPF.Cofix.instIsPolynomial [u]) (toExpr n) e.typefun e.qpf isPoly
  }

/--
Create the `i`-th `n`-ary projection QPF, i.e., the `n`-ary type function
`fun αs => αs i`, as an application of `QPF.Prj`.
-/
public meta def mkProj (u : Level) {n : Nat} (i : Fin n) : QPFExpr n where
  domLevel := u
  codLevel := u
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
public meta def mkConstant (u : Level) (n : Nat) (A : Expr /- : Type $u -/) : QPFExpr n where
  domLevel := u
  codLevel := u
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
    (family : Expr → MetaM (QPFExpr n)) : MetaM (QPFExpr n) :=
  Meta.withLocalDeclD `a A fun a => do
    let Fa ← family a
    Fa.assertDomLevelDefEq u
    let Fa ← Fa.setCodLevelM u
    -- `fun (a : $A) => $(Fa.typefun) : $A → TypeFun.{$u} $n`
    let Ftypefun ← Meta.mkLambdaFVars #[a] Fa.typefun
    -- `fun (a : $A) => $(Fa.qpf) : (a : $A) → QPF.{$u, $u} $n ($Ftypefun a)`
    let Fqpf ← Meta.mkLambdaFVars #[a] Fa.qpf
    return {
      domLevel := u
      codLevel := u
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
expected to return the `n`-ary QPF `$F a` as a QPFExpr in universe `u`
(an error is thrown otherwise).

Note that the index type `$A` must live in the *same* universe `$u` as the
QPFs in the family.
-/
public meta def mkSigma (u : Level) (n : Nat) (A : Expr /- : Type $u -/)
    (family : Expr → MetaM (QPFExpr n)) : MetaM (QPFExpr n) :=
  mkDepFamily ``QPF.Sigma ``QPF.Sigma.qpf ``QPF.Sigma.instIsPolynomial u n A family

/--
Create the dependent product of a family of `n`-ary QPFs,
i.e., an application of `QPF.Pi`.

The family is described by `A`, an expression of type `Type $u`, together with
the monadic function `family`, which is given a free variable `a : $A` and is
expected to return the `n`-ary QPF `$F a` as a QPFExpr in universe `u`
(an error is thrown otherwise).

Since a non-dependent function type `$A → $B` is just a trivial/degenerate
dependent product, this is also how function types (which are functorial in
their codomain, but not in their domain) are represented.
-/
public meta def mkPi (u : Level) (n : Nat) (A : Expr /- : Type $u -/)
    (family : Expr → MetaM (QPFExpr n)) : MetaM (QPFExpr n) :=
  mkDepFamily ``QPF.Pi ``QPF.Pi.qpf ``QPF.Pi.instIsPolynomial u n A family

/--
Compose an `n`-ary QPF `F` with `n` `m`-ary QPFs `Gs`, i.e.,
create an application of `QPF.Comp`.

The QPFs in `Gs` must all have def-eq domain and codomain levels, which must
furthermore be def-eq to the domain level of `F`; an error is thrown otherwise.
The codomain level of `F` is unrestricted, and determines the codomain level of
the resulting QPF.

Note that the result is only polynomial (i.e., `isPolynomial?` is only `some _`)
if, additionally, the codomain level of `F` is def-eq to its domain level.
-/
public meta def mkComp (F : QPFExpr n) (Gs : Vector (QPFExpr m) n) :
    MetaM (QPFExpr m) := do
  -- `QPF.Comp` requires each `G i` to be homogeneous, in the domain universe of `F`
  let u := F.domLevel
  let Gs ← Gs.mapM fun G => do
    G.assertDomLevelDefEq u
    G.setCodLevelM u
  let G ← QPFTupleExpr.ofVector Gs
  -- If `Gs` is empty, the levels of `G` are still unassigned
  let G ← G.setLevelsM u u
  let u ← instantiateLevelMVars u
  let v := F.codLevel
  let n := toExpr n
  let m := toExpr m
  -- `QPF.Comp.instIsPolynomial` is only stated for homogeneous `F`
  let isHomogeneous ← Meta.isLevelDefEq u v
  return {
    domLevel := u
    codLevel := v
    typefun := mkApp4 (mkConst ``QPF.Comp [u, v]) n m F.typefun G.typefun
    qpf     := mkApp6 (mkConst ``QPF.Comp.inst [u, v]) n m F.typefun G.typefun F.qpf G.qpf
    isPolynomial? := do
      guard isHomogeneous
      let FisPoly ← F.isPolynomial?
      let GisPoly ← G.isPolynomial?
      return mkApp8 (mkConst ``QPF.Comp.instIsPolynomial [u])
        n m F.typefun G.typefun F.qpf G.qpf FisPoly GisPoly
  }
