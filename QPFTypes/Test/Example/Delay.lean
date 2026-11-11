module

import Test.Example.Stream

/-!
# Delayed computations (Capretta's partiality type)

`Delay α = α ⊕ Delay α`: a result is available `now`, or computation takes another
`later` step. Infinitely many `later`s represent divergence. `Delay Unit` also gives
the shape of the conaturals (zero / successor, including infinity).

This is the *unquotiented* delay type: the number of steps is observable. See Capretta,
*General Recursion via Coinductive Types*, §3, and this directory's `README.md`.
As in the other examples, `unsafe` only lets us typecheck a proposed corecursive body;
it does not turn Lean's evaluator into a lazy evaluator.
-/

namespace QPFTypes.Test.Delay

open QPF (Cofix)
open QPFTypes.Test.Stream (Stream)

@[qpf] def DelayF (α X : liveParam (Type u)) := α ⊕ X

def Delay (α : Type u) : Type u :=
  Cofix (@TypeFun.ofCurried 2 DelayF) #t[α]

@[match_pattern] def DelayF.now (a : α) : DelayF α X := .inl a
@[match_pattern] def DelayF.later (t : X) : DelayF α X := .inr t

def Delay.now (a : α) : Delay α := Cofix.mk (.now a)
def Delay.later (t : Delay α) : Delay α := Cofix.mk (.later t)

def Delay.dest (t : Delay α) : DelayF α (Delay α) := Cofix.dest t

/-- Search may never find a match, but each unsuccessful test emits a `later`.
Contrast with unguarded stream filtering: rejection of an element cannot just disappear
from the output. This definition does not assert eventual success. -/
unsafe def Delay.search (p : α → Bool) (s : Stream α) : Delay α :=
  if p s.head then
    .now s.head
  else
    .later (Delay.search p s.tail)

end QPFTypes.Test.Delay
