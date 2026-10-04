module

public import Lean

/-!
# Fin-based Tuples

This file defines two meta helpers, `mkTuple` and `mkDTuple` for creating expressions
of fin-based non-dependent tuples or dependent tuples, respectively.

These helpers generate these tuples via list literals, to avoid having to
vendor an analogou to the Mathlib module `Mathlib/Data/Fin/Tuple`.

This is primarily used to make it easier to generate the composistion of QPFs at
meta-time, in `QPFExpr.mkComp`.
-/

section
namespace QPFTypes.Fin
open Lean Meta

/-!
## Non-Dependent Tuples
-/

/--
Create a Lean expression of a (non-dependent) tuple from a vector of `n` Lean expressions,
each of type `α`.

The tuple is constructed as `List.get` of a list literal contain the expressions in `xs`.
That is, when called with expressions `x₁`, ⋯, `xₙ`, each of type `$type`,
the following expression is returned: `[$x₁, ⋯, $xₙ].get`.
-/
public meta def mkTuple (type : Expr /- : Type _ -/) (xs : Vector Expr n) : MetaM Expr := do
  let listLit ← mkListLit type xs.toList
  let tuple ← mkAppOptM ``List.get #[some type, some listLit]
  let expectedType ← mkArrow (mkApp (.const ``Fin []) (toExpr n)) type
  let .some tuple ← coerce? tuple expectedType
    | throwError "Failed to coerce{indentExpr tuple}\nto{indentExpr expectedType}"
  return tuple

/-!
## Dependent Tuples

For dependent tuples, we still use a list literal.
However, to encode for the dependent types of each element,
we create a list of sigmas.
Then, we effectively use `by decide` to prove (a) that the list literal
has the correct length and, more imporantly, (b) that the first component of
the `i`-th element of the list literal is the index `i`.
To facilitate constructions of a list with these conditions, we define the
`DList` abbreviation, and then define `DList.get` as the getter of the
expected shape.
-/

public section DList

/-- A dependent list, encoded as a list of dependent pairs with some side-conditions. -/
@[reducible, expose]
protected def DList.{u} {n : Nat} (β : Fin n → Type u) :=
  { xs : List (Σ i : Fin n, β i) //
    ∃ h : xs.length = n, ∀ i : Fin n, xs[i].fst = i
  }

variable {n : Nat} {β : Fin n → Type u}

protected def DList.ofList (xs : List (Σ (i : Fin n), β i))
    (hlen : xs.length = n) (hget : ∀ i : Fin n, xs[i].fst = i) : Fin.DList β :=
  ⟨xs, ⟨hlen, hget⟩⟩

/-- Return the `i`-th element of a dependent list. -/
protected def DList.get {n} {β} (xs : @Fin.DList n β) : (i : Fin n) → β i :=
  have : n = xs.val.length := by grind
  fun i => xs.val[i] |>.snd |> (cast <| by grind)

end DList

/--
Given a Lean expression `e` of arrow type `_ → _`, recursively apply `e` to
proofs by `decide` of each of its remaining arguments,
until the result is no longer a function.

This cannot use `forallTelescope`, as later arguments may depend on earlier
arguments (as happens in `DList.ofList`); in which case a telescope will leak
the relevant free variable into the generated proof.
-/
private meta partial def applyDecideProofs (e : Expr) : MetaM Expr := do
  match ← whnf (← inferType e) with
  | .forallE _ argType _ _ => applyDecideProofs (.app e (← mkDecideProof argType))
  | _ => return e

/--
Create a Lean expression of a dependent tuple from a vector of `n` Lean expressions `xs`,
such that `xs[i]` is of type `α $i : Type $u`.

The tuple is constructed as `DList.get` of a (dependent) list literal.
That is, when called with expressions `x₁`, ⋯, `xₙ`, each of type `$type i`,
morally, the following expression is returned:
  `DList.get ⟨[⟨0, $x₁⟩, ⋯, ⟨n-1, $xₙ], by decide, by decide⟩`.
-/
public meta def mkDTuple (typefam : Expr /- : Fin $n → Type $u -/) (xs : Vector Expr n) :
    MetaM Expr := withErrorCtxt do
  let finN := mkApp (.const ``Fin []) (toExpr n)
  let u ← getDecLevel <| mkApp typefam (← mkFreshExprMVar finN)

  -- First, map `xs` into an array of Sigma expressions, with each element
  -- of `sigmas` being an expression of type `Σ (i : Fin n), $typefam i`.
  let sigmas :=
    let mkSigma (i : Fin n) : (x : Expr) → Expr :=
      mkApp4 (.const ``Sigma.mk [0, u]) finN typefam (toExpr i)
    xs.mapFinIdx fun i x hi => mkSigma ⟨i, hi⟩ x
  -- Then, convert `sigmas` into a lean expression of type `List (Σ (i : Fin n), $typefam i)`
  let sigmaType := -- `Σ (i : Fin n), $typefam i`
    mkApp2 (.const ``Sigma [0, u]) finN typefam
  -- `DList.ofList [${xs[0]}, ..., ${xs[n-1]}] ${by decide} ${by decide}`.
  let dlist ← do
    let list ← mkListLit sigmaType sigmas.toList
    let ofList := mkApp3 (.const ``DList.ofList [u]) (toExpr n) typefam list
    applyDecideProofs ofList
  -- Finally, `DList.get $dlist : (i : Fin $n) → $typefam i` is the desired tuple
  return mkApp3 (.const ``DList.get [u]) (toExpr n) typefam dlist
where
  withErrorCtxt {α} (x : MetaM α) : MetaM α := do
    try x catch err =>
      throwError "While constructing a dependent tuple with type family:{indentExpr typefam}
and the following elements: {xs.toList}

The following error occured:
{err.toMessageData}"
