-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

module

public import CTree.Defs

public section

namespace CTree

/--
The `iter` combinator loops over `body` while it returns a value in `I`,
and finally returns when it returns a value in `X`.
-/
def iter {I X} (body : I -> CTree E C (I ⊕ X)) (i : I) : CTree E C X := do
  let r ← body i
  match r with
  | .inl i => .tau1 (iter body i)
  | .inr r => return r
partial_fixpoint

section Splice

variable {EIn : Type u} {E : EIn → Type u} {CIn : Type u} {C : CIn → Type u} {I X : Type u}

/-- What `iter` does after a step of its body: go round again behind a silent step, or stop. -/
abbrev iterCont (f : I → CTree E C X) : I ⊕ X → CTree E C X
  | .inl i => CTree.tau1 (f i)
  | .inr x => pure x

theorem iter_eq (body : I → CTree E C (I ⊕ X)) (i : I) :
    iter body i = body i >>= iterCont (iter body) := by
  rw [iter]
  rfl

/--
`iter body` is the only solution of its unfolding equation: each recursive call is behind a silent
step, so the approximations of two solutions agree at every depth.
-/
theorem iter_unique (body : I → CTree E C (I ⊕ X)) (f : I → CTree E C X)
    (hf : ∀ i, f i = body i >>= iterCont f) (i : I) :
    f i = iter body i := by
  have key : ∀ n (t : CTree E C (I ⊕ X)),
      (t >>= iterCont f).approx n = (t >>= iterCont (iter body)).approx n := by
    intro n
    induction n with
    | zero => intro t; rfl
    | succ n ih =>
      intro t
      cases t with
      | ret r =>
        cases r with
        | inl j =>
          simp only [pure_bind, iterCont, CTree.tau1_def, approx_tau_succ]
          congr 1
          funext _
          rw [hf j, iter_eq]
          exact ih (body j)
        | inr x => simp
      | tau c k =>
        simp only [bind_tau, approx_tau_succ]
        congr 1
        funext x
        exact ih (k x)
      | vis e k =>
        simp only [bind_vis, approx_vis_succ]
        congr 1
        funext x
        exact ih (k x)
  ext n
  rw [hf i, iter_eq]
  exact key n (body i)

/--
Run `body`, and keep running it behind a silent step while it continues to a state satisfying
`p`. A step of `spliceWhile body p` is a step of `body` together with all the steps that follow
it through states satisfying `p`.
-/
def spliceWhile (body : I → CTree E C (I ⊕ X)) (p : I → Bool) (i : I) : CTree E C (I ⊕ X) := do
  match ← body i with
  | .inl j => if p j then CTree.tau1 (spliceWhile body p j) else pure (.inl j)
  | .inr x => pure (.inr x)
partial_fixpoint

theorem spliceWhile_eq (body : I → CTree E C (I ⊕ X)) (p : I → Bool) (i : I) :
    spliceWhile body p i = body i >>= fun
      | .inl j => if p j then CTree.tau1 (spliceWhile body p j) else pure (.inl j)
      | .inr x => pure (.inr x) := by
  rw [spliceWhile]

/--
Grouping the steps through states satisfying `p` with the step before them leaves the loop
unchanged, as a tree: the silent step between two steps of `body` stays inside the grouped step.
This lets two loops whose steps do not correspond one to one be regrouped until they do, so that
a lockstep simulation of their bodies applies.
-/
theorem iter_spliceWhile (body : I → CTree E C (I ⊕ X)) (p : I → Bool) (i : I) :
    iter.{u, u} body i = iter.{u, u} (spliceWhile body p) i := by
  refine (iter_unique body _ (fun j => ?_) i).symm
  rw [iter_eq, spliceWhile, bind_assoc]
  congr 1
  funext r
  cases r with
  | inr x => simp
  | inl m =>
    by_cases hp : p m
    · simp only [hp, ↓reduceIte, CTree.tau1_def, bind_tau, iterCont]
      rw [← iter_eq]
    · simp [hp]

end Splice

end CTree
