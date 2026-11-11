module

import Test.Example.CoList

/-!
# Rose trees with coinductive child lists

`CoTree α = α × CoList (CoTree α)` nests two greatest fixed points: a node's
children form a possibly-infinite *coinductive list*, not an inductive list or a
function-valued family. Trees may have infinite breadth and infinite depth
independently; `.node a .nil` is a leaf.

This is `cotree` from Joomy Korkut's *A Rose Tree Is Blooming* (CPP 2026), §3,
and the accompanying Bloomberg `game-trees` library's `theories/Cotrees.v`.
See this directory's `README.md` for links and `GuardedCorecursion.v` for Rocq checks.

Both functions below rely on `CoList.mapCorec` capturing its mapping function
outside a local recursion. In Rocq, unfolding that helper exposes a nested
cofixpoint: the outer one builds trees, while the inner one builds child lists.
This is not a rule permitting arbitrary uses of `map` around recursive calls.
The `unsafe` bodies are typechecked specifications only, not lazy Lean programs.
-/

namespace QPFTypes.Test.CoTree

open QPF (Cofix)
open QPFTypes.Test.CoList (CoList)

@[qpf] def CoTreeF (α X : liveParam Type) := α × CoList X

-- Composition with a greatest fixed point still yields a polynomial shape functor.
example : QPF.IsPolynomial (@TypeFun.ofCurried 2 CoTreeF) := inferInstance

def CoTree (α : Type) : Type :=
  Cofix (@TypeFun.ofCurried 2 CoTreeF) #t[α]

@[match_pattern] def CoTreeF.node (a : α) (children : CoList X) : CoTreeF α X :=
  (a, children)

def CoTree.node (a : α) (children : CoList (CoTree α)) : CoTree α :=
  Cofix.mk (.node a children)

def CoTree.dest (t : CoTree α) : CoTreeF α (CoTree α) := Cofix.dest t

/-- Map labels at every depth and across possibly-infinite child lists. The partial
application `CoTree.map f` becomes a captured outer recursive reference in the inner
list cofixpoint; its calls occur in the heads of newly constructed child lists. -/
unsafe def CoTree.map (f : α → β) (t : CoTree α) : CoTree β :=
  match t.dest with
  | .node a children => .node (f a) (CoList.mapCorec (CoTree.map f) children)

/-- Unfold a game/transition graph whose successor lists may be infinite. No decreasing
state argument or finite branching assumption is needed. If every state has infinitely
many successors, this produces an infinitely branching, infinitely deep tree.

This is Korkut's `unfold_cotree`: unlike `RoseTree.unfold`, the child container itself
requires corecursion, exposed by unfolding `CoList.mapCorec`. -/
unsafe def CoTree.unfold (next : α → CoList α) (a : α) : CoTree α :=
  .node a (CoList.mapCorec (CoTree.unfold next) (next a))

end QPFTypes.Test.CoTree
