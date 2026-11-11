module

import QPFTypes

/-!
# Finitely branching, possibly-infinite rose trees

A node's children are a finite vector, encoded as `Σ n, Fin n → X`. This is the
polynomial presentation of a list of children, without needing a QPF instance for
Lean's `List`. In particular, this is not an infinitely branching `Nat → X` tree.
For children that are themselves coinductive lists (and can be infinite), see
`CoTree.lean`, which exercises nested cofixpoints instead.

This refines the branching-tree example to test nested containers: the recursive
occurrence is inside a dependent pair and a function codomain. Rocq accepts the
analogous nested `sigT` / `Fin.t` definition (see `GuardedCorecursion.v`). This does
*not* mean it accepts arbitrary `List.map` around recursive results.
See `README.md` for the exact distinction. The `unsafe` body is a specification only.
-/

namespace QPFTypes.Test.RoseTree

open QPF (Cofix)

@[qpf] def RoseTreeF (α : Type) (X : liveParam Type) :=
  α × (Σ n : Nat, Fin n → X)

def RoseTree (α : Type) : Type :=
  Cofix (@TypeFun.ofCurried 1 (RoseTreeF α)) #t[]

@[match_pattern] def RoseTreeF.node (a : α) (children : Fin n → X) : RoseTreeF α X :=
  (a, ⟨n, children⟩)

def RoseTree.node (a : α) (children : Fin n → RoseTree α) : RoseTree α :=
  Cofix.mk (.node a children)

def RoseTree.dest (t : RoseTree α) : RoseTreeF α (RoseTree α) := Cofix.dest t

/-- Unfold a finitely branching transition system. Each state determines both its label
and its arity. Calls occur beneath a constructor, a dependent pair, and a lambda;
the lambda's domain depends on the current state, not on a recursive result.
Arity zero produces a leaf. -/
unsafe def RoseTree.unfold (label : σ → α) (arity : σ → Nat)
    (next : (s : σ) → Fin (arity s) → σ) (s : σ) : RoseTree α :=
  .node (label s) (fun i : Fin (arity s) => RoseTree.unfold label arity next (next s i))

end QPFTypes.Test.RoseTree
