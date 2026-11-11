module

import QPFTypes

/-!
# Possibly-infinite binary trees

This is Bertot's `Ltree` from *CoInduction in Coq*, §1. A tree may have finite leaves
and/or infinite branches. Unlike a stream, a node has several recursive positions.
See this directory's `README.md` for sources and the Rocq comparison.
The `unsafe` definition is only a typechecked specification, not a productive Lean program.
-/

namespace QPFTypes.Test.Tree

open QPF (Cofix)

@[qpf] def TreeF (α X : liveParam Type) := Unit ⊕ (α × X × X)

def Tree (α : Type) : Type :=
  Cofix (@TypeFun.ofCurried 2 TreeF) #t[α]

@[match_pattern] def TreeF.leaf : TreeF α X := .inl ()
@[match_pattern] def TreeF.node (a : α) (l r : X) : TreeF α X := .inr (a, l, r)

def Tree.leaf : Tree α := Cofix.mk .leaf

def Tree.node (a : α) (l r : Tree α) : Tree α := Cofix.mk (.node a l r)

def Tree.dest (t : Tree α) : TreeF α (Tree α) := Cofix.dest t

/-- Two independent recursive calls in different recursive fields of a constructor.
Neither is an argument of the other; nested recursive calls are a different, rejected case. -/
unsafe def Tree.mirror (t : Tree α) : Tree α :=
  match t.dest with
  | .leaf => .leaf
  | .node a l r => .node a (Tree.mirror r) (Tree.mirror l)

end QPFTypes.Test.Tree
