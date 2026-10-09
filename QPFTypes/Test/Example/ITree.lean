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
variable {ε : Type u} (E : ε → Type u) (R : Type u)

@[qpf] def ITreeF (ITree : liveParam (Type u)) : Type u :=
    R ⊕ ITree ⊕ (Σ e : ε, E e → ITree)

/-
FIXME: the above has the effects and result living in the same universe `u`,
these ought to be decoupled, as in the following definition:
```
variable {ε : Type u} (E : ε → Type u) (R : Type v)

@[qpf] def ITreeF (ITree : liveParam (Type (max u v))) : Type (max u v) :=
    R ⊕ ITree ⊕ (Σ e : ε, E e → ITree)
```

Doing so currently raises the following error:
```
While deriving a QPF from definition:
  ITreeF

failed to find a QPF in the head of the application:
  R ⊕ ITree ⊕ (e : ε) × (E e → ITree)
note that the head, after applying it to zero or more of the arguments, must be a type function with a `QPF` instance
```
-/

/-- Interaction trees -/
def ITree : Type u :=
  Cofix (@TypeFun.ofCurried 1 (ITreeF E R)) #t[]

end Def

variable {ε : Type u} {E : ε → Type u} {R : Type u}

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

end QPFTypes.Test.ITree
