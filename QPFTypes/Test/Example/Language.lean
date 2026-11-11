module

import QPFTypes

/-!
# Languages as infinite tries

A language over alphabet `α` is a trie with an accepting bit (membership of the empty
word) and one derivative/subtrie per letter. This is the final-coalgebra view of
deterministic automata. Unlike a finite automaton, the trie need not have finitely many
states. See Traytel, *Formal Languages, Formally and Coinductively*, §§2–3, and the
sources and Rocq checks in this directory's `README.md`.

Only union is included: intersection/complement have essentially the same corecursion
shape. Concatenation's usual derivative equation, in contrast, nests recursive results
under union and is not directly Rocq-guarded. The `unsafe` body is a specification only.
-/

namespace QPFTypes.Test.Language

open QPF (Cofix)

@[qpf] def LanguageF (α : Type) (X : liveParam Type) := Bool × (α → X)

def Language (α : Type) : Type :=
  Cofix (@TypeFun.ofCurried 1 (LanguageF α)) #t[]

def Language.node (accepting : Bool) (next : α → Language α) : Language α :=
  Cofix.mk (accepting, next)

def Language.dest (l : Language α) : LanguageF α (Language α) := Cofix.dest l

def Language.acceptsEmpty (l : Language α) : Bool := l.dest.1

def Language.derivative (l : Language α) (a : α) : Language α := l.dest.2 a

/-- Pointwise binary corecursion under a function-valued field. The boolean expression
is in a nonrecursive field: it may inspect inputs, but must not inspect recursive results. -/
unsafe def Language.union (l r : Language α) : Language α :=
  .node (l.acceptsEmpty || r.acceptsEmpty)
    (fun a => Language.union (l.derivative a) (r.derivative a))

end QPFTypes.Test.Language
