module

import QPFTypes

/-!
# Example: interaction trees

Interaction trees, where the events are given by a type `ε` together with a family
`E : ε → Type u` of answer types, so that the answer to event `e : ε` has type `E e`.
An `ITree E R` is either
* `ret r`, a finished computation returning `r : R`,
* `tau t`, a silent step continuing as `t`, or
* `vis e k`, an event `e : ε`, whose answer `a : E e` determines the continuation `k a`.

`ITree E R` is built as `Cofix` of the shape functor
`ITreeF E R ITree = R ⊕ ITree ⊕ (Σ e : ε, E e → ITree)`,
whose `QPF` and `IsPolynomial` instances are derived by `@[qpf]`.
-/

namespace QPFTypes.Test.ITree

open QPF (Cofix)

universe u

/-! ## The type -/
section Def
variable {ε : Type u} (E : ε → Type u) (R : Type v)

@[qpf] def ITreeF (ITree : liveParam (Type (max u v))) : Type (max u v) :=
    R ⊕ ITree ⊕ (Σ e : ε, E e → ITree)

/-- Interaction trees -/
def ITree : Type (max u v) :=
  Cofix (@TypeFun.ofCurried 1 (ITreeF E R)) #t[]

end Def

variable {ε : Type u} {E : ε → Type u} {R : Type v}

/-! ## Constructors and destructor -/

@[match_pattern] def ITreeF.ret (r : R) : ITreeF E R β := .inl r
def ITree.ret (r : R) : ITree E R := Cofix.mk (.ret r)

@[match_pattern] def ITreeF.tau (t : β) : ITreeF E R β := .inr (.inl t)
def ITree.tau (t : ITree E R) : ITree E R := Cofix.mk (.tau t)

@[match_pattern] def ITreeF.vis (e : ε) (k : E e → β) : ITreeF E R β := .inr (.inr ⟨e, k⟩)
def ITree.vis (e : ε) (k : E e → ITree E R) : ITree E R := Cofix.mk (.vis e k)

def ITree.dest (t : ITree E R) : ITreeF E R (ITree E R) :=
  Cofix.dest t

@[simp, grind =] theorem ITree.dest_ret (r : R) :
    ITree.dest (ITree.ret r : ITree E R) = ITreeF.ret r :=
  Cofix.dest_mk _

@[simp, grind =] theorem ITree.dest_tau (t : ITree E R) :
    ITree.dest (ITree.tau t) = ITreeF.tau t :=
  Cofix.dest_mk _

@[simp, grind =] theorem ITree.dest_vis (e : ε) (k : E e → ITree E R) :
    ITree.dest (ITree.vis e k) = ITreeF.vis e k :=
  Cofix.dest_mk _

/-! ## Guarded corecursion specifications

These follow the Interaction Trees library's `subst`/`bind` and `iter`. See this
directory's `README.md` for sources and `GuardedCorecursion.v` for the checked Rocq
versions. `unsafe` only suppresses Lean's termination requirement: do not evaluate
these as though they were lazy trees.
-/

/-- Sequencing: return branches graft an existing tree; silent steps guard a direct call;
visible events guard calls beneath lambdas whose domains depend on the event.

Keeping `k` *outside* the local recursive function is intentional. Rocq can unfold this
helper to a nested cofixpoint capturing `k`, which is important for `iter` below. A
cofixpoint with `k` as an explicit recursive argument works for `bind` in isolation,
but does not support the same definition of `iter`. -/
unsafe def ITree.bind {S : Type v} (t : ITree E R) (k : R → ITree E S) : ITree E S :=
  let rec go (t : ITree E R) : ITree E S :=
    match t.dest with
    | .ret r => k r
    | .tau t' => .tau (go t')
    | .vis e h => .vis e (fun a => go (h a))
  go t

/-- Tail-recursive effectful iteration: `inl` continues and `inr` finishes.
The `tau` is essential when `step` can immediately return `inl` forever.

This is a Rocq-supported *edge case*, not a direct constructor-only corecursion:
unfolding `bind` exposes an inner cofixpoint capturing the guarded outer call.
It does not license passing recursive results to arbitrary functions. -/
unsafe def ITree.iter {S : Type v} (step : S → ITree E (Sum S R)) (s : S) : ITree E R :=
  ITree.bind (step s) (fun result =>
    match result with
    | .inl s' => .tau (ITree.iter step s')
    | .inr r => .ret r)

end QPFTypes.Test.ITree
