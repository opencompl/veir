# Sym.simp crashes when unfolding a wrapper around a recursive reducible function

Tested with Lean 4.35.0-rc1, commit 86c6347c75e39ec18c40e25ed2143b71a6e04a0a (arm64-apple-darwin24.6.0, Release).

Run:

```sh
lean +leanprover/lean4:v4.35.0-rc1 Repro/SymBindingDecls.lean
```

## Reproducer

This seven-line file imports only Lean and has no third-party dependencies.

```lean
import Lean
@[reducible] def g : Nat → Nat
  | 0 => 0
  | n + 1 => g n
def f (n : Nat) := g n
example (n : Nat) : f n = f n := by
  sym => simp [f]
```

## Actual result

```text
Repro/SymBindingDecls.lean:7:9: error: internal error, expression has loose bound variables at `shareCommon`
  g #0
```

## Expected result and controls

The reflexive equality should be proved, or the tactic should report a normal failure rather than an internal error.

Each of these changes independently makes the file compile:

- Replace `sym => simp [f]` with `rfl`.
- Replace `sym => simp [f]` with ordinary `simp [f]`.
- Unfold the definitions first, then use `sym => simp` without registering `f` as a rewrite rule:

  ```lean
  example (n : Nat) : f n = f n := by
    unfold f g
    sym => simp
  ```

- Remove `@[reducible]` from `g`.
- Replace the recursive definition with the extensionally equivalent nonrecursive wrapper `@[reducible] def g : Nat → Nat := Nat.rec 0 (fun _ r => r)`.

This was reduced from `Veir.Puddle.MatchProg.bindingDecls`, then from a 22-line standalone reproducer involving a reducible recursive type family. The failure no longer requires custom datatypes, type families, higher-order functions, or list operations.
