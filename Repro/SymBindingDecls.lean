import Lean
@[reducible] def g : Nat → Nat
  | 0 => 0
  | n + 1 => g n
def f (n : Nat) := g n
example (n : Nat) : f n = f n := by
  sym => simp [f]
