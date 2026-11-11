module

public import QPFTypes

/-!
# Infinite streams: the basic guarded corecursion patterns

Unlike `CoList`, a stream has no terminating constructor. The examples are inspired by
Rocq's standard library `Streams` and Chlipala's *CPDT*, chapter “Coinduction”.
See `README.md` in this directory for sources, the coverage table, and Rocq checks.

The `unsafe def`s below are specifications for a future guarded `codef`, not executable
lazy streams: Lean checks their types, but neither productivity nor termination.
-/

@[expose] public section

namespace QPFTypes.Test.Stream

open QPF (Cofix)

@[qpf] def StreamF (α X : liveParam (Type u)) := α × X

def Stream (α : Type u) : Type u :=
  Cofix (@TypeFun.ofCurried 2 StreamF) #t[α]

@[match_pattern] def StreamF.cons (a : α) (s : X) : StreamF α X := (a, s)

def Stream.cons (a : α) (s : Stream α) : Stream α := Cofix.mk (.cons a s)

def Stream.dest (s : Stream α) : StreamF α (Stream α) := Cofix.dest s

def Stream.head (s : Stream α) : α := s.dest.1

def Stream.tail (s : Stream α) : Stream α := s.dest.2

/-- A state generator: the next argument need not be a subterm of the current one.
The `let` and transparent `id` deliberately obscure the constructor guard; Rocq accepts
this after reduction. In particular, binding a recursive result before the constructor
is not in itself a reason to reject a definition. -/
unsafe def Stream.iterate (step : α → α) (a : α) : Stream α :=
  let rest := Stream.iterate step (step a)
  id (.cons a rest)

/-- Consume an input before producing output, and exchange the two inputs on each call
(CPDT's `interleave`). Guardedness is about output, not a decreasing input. -/
unsafe def Stream.interleave (s t : Stream α) : Stream α :=
  match s.dest with
  | .cons a s' => .cons a (Stream.interleave t s')

/-- More than one output constructor may guard a call. -/
unsafe def Stream.stutter (s : Stream α) : Stream α :=
  match s.dest with
  | .cons a s' => .cons a (.cons a (Stream.stutter s'))

/-- Variable-rate sampling: always emit the current element, then optionally skip one.
The conditional is *inside* the guard; its branches need not emit another constructor.
Destructors may inspect the inputs, but not the result of the recursive call. -/
unsafe def Stream.sample (skipNext : α → Bool) (s : Stream α) : Stream α :=
  .cons s.head (if skipNext s.head then
    Stream.sample skipNext s.tail.tail
  else
    Stream.sample skipNext s.tail)

mutual
  /-- Mutually corecursive values (CPDT's alternating boolean streams). Each call,
  including calls to a different member of the block, has its own guard. -/
  unsafe def Stream.truesFalses : Stream Bool :=
    .cons true Stream.falsesTrues

  unsafe def Stream.falsesTrues : Stream Bool :=
    .cons false Stream.truesFalses
end

end QPFTypes.Test.Stream
