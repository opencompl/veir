module

public import Veir.IR.Attribute

/-!
  # Felt interpreter-semantics model (F2 spike PoC) — Mathlib-free core

  **Status: proof-of-concept landed by the F2 scoping spike** (see
  `FOLLOWUP.md` §F2). This file is the empirical evidence behind F2's
  go/no-go: it shows the felt field model works and that a felt rewrite's
  two sides compute the same runtime value, at the level of values an
  interpreter actually produces.

  ## What this is, precisely

  `Veir/Interpreter/Basic.lean` does not interpret felt at all:
  `interpretOp'` returns `none` for every `OpCode.felt`, and
  `RuntimeValue` is `int`/`addr`/`reg` — there is no field-element runtime
  value. This file supplies a *standalone* model of what a felt interpreter
  would compute. It is deliberately **not** wired into the core
  `RuntimeValue`/`interpretOp'` yet (that is F3).

  ## Mathlib-free by design

  The core interpreter module imports no Mathlib, and keeping it that way
  is a goal. So a felt runtime value here is a **canonical `Nat`
  representative** in `[0, p)` with `Nat`-modular arithmetic — exactly how
  LLZK's registry helper reduces values (`lib/Util/Field.cpp::reduce`) — *not* a
  `ZMod p`. The correspondence to the abstract field model
  `Veir.Data.Felt` (`ZMod p`) and to the verified identities in
  `Proofs.lean` is proven separately in `InterpModel/Bridge.lean`, which is
  the *only* place Mathlib enters.

  ## Field model (F2 Q1)

  `!felt.type` carries an optional field *name* but no prime; the prime
  lives in LLZK's field registry (`lib/Util/Field.cpp::initKnownFields`),
  keyed by name. `feltPrime` mirrors that registry. `FeltVal.felt p v`
  carries its modulus `p`, as `RuntimeValue.int` carries its bitwidth. An
  unnamed field is uninterpreted (`none`) — matching LLZK's "filled in by
  backend".
-/

public section

namespace Veir.FeltInterp

open Veir

/-- A felt runtime value: a field element as a canonical `Nat` representative
    in `[0, p)` carrying its own modulus `p` (mirroring how
    `RuntimeValue.int` carries its bitwidth). Mathlib-free. -/
inductive FeltVal where
  | felt (p : Nat) (val : Nat)
deriving Repr, DecidableEq

/-- Field-name → prime, mirroring LLZK `lib/Util/Field.cpp::initKnownFields`.
    Keyed on `FeltType.fieldName : Option ByteArray`. Unnamed field
    (`!felt.type`) ⇒ `none` (uninterpreted — "filled in by the backend"). -/
def feltPrime (name : Option ByteArray) : Option Nat :=
  match name with
  | none => none
  | some n =>
    if n = "bn254".toUTF8 then
      some 21888242871839275222246405745257275088548364400416034343698204186575808495617
    else if n = "bn128".toUTF8 then
      some 21888242871839275222246405745257275088548364400416034343698204186575808495617
    else if n = "grumpkin".toUTF8 then
      some 21888242871839275222246405745257275088696311157297823662689037894645226208583
    else if n = "babybear".toUTF8 then some 2013265921
    else if n = "goldilocks".toUTF8 then some 18446744069414584321
    else if n = "mersenne31".toUTF8 then some 2147483647
    else if n = "koalabear".toUTF8 then some 2130706433
    else none

/-- Reduce an integer literal to its canonical representative in `[0, p)`,
    mirroring LLZK `Field::reduce` (`i % p`, made non-negative). For `p > 0`,
    Lean's `Int.emod` already lands in `[0, p)`. -/
def reduce (p : Nat) (i : Int) : Nat := (i % (p : Int)).toNat

/-! ## Minimal `Felt.interpretOp'` arms, mirroring `Arith.interpretOp'`. -/

/-- Interpret `felt.const`: resolve the field's prime from the registry and
    reduce the integer literal into `[0, p)`. Unknown/unnamed field ⇒ `none`. -/
def interpretConst (a : FeltConstAttr) : Option FeltVal :=
  match feltPrime a.fieldType.fieldName with
  | none => none
  | some p => some (.felt p (reduce p a.value))

/-- Interpret `felt.add` — defined only when both operands live in the same field. -/
def interpretAdd : FeltVal → FeltVal → Option FeltVal
  | .felt p a, .felt p' b => if p' = p then some (.felt p ((a + b) % p)) else none

/-- Interpret `felt.sub`. -/
def interpretSub : FeltVal → FeltVal → Option FeltVal
  | .felt p a, .felt p' b => if p' = p then some (.felt p ((a + (p - b)) % p)) else none

/-- Interpret `felt.mul`. -/
def interpretMul : FeltVal → FeltVal → Option FeltVal
  | .felt p a, .felt p' b => if p' = p then some (.felt p ((a * b) % p)) else none

/-- Interpret `felt.neg`. -/
def interpretNeg : FeltVal → Option FeltVal
  | .felt p a => some (.felt p ((p - a) % p))

/-! ## (F2 (B)) Op-level semantic-equivalence lemma — Mathlib-free.

    The genuine "RHS computes the same value as LHS" content of the
    `right_identity_zero_add` peephole, isolated from the IR surgery:
    interpreting `felt.add x (felt.const 0)` yields exactly `x`'s runtime
    value, for any field. Pure `Nat` arithmetic — no Mathlib, no primality. -/

/-- Interpreting `felt.add x (felt.const 0)` returns exactly `x`'s value,
    when the constant's field resolves to the same prime `x` lives in and
    `x`'s representative is canonical (`a < p`). This is the semantic
    justification for `right_identity_zero_add`, over the values the
    interpreter computes. -/
theorem interpretAdd_const_zero
    (p : Nat) (a : Nat) (ha : a < p) (cst : FeltConstAttr)
    (hval : cst.value = 0)
    (hp : feltPrime cst.fieldType.fieldName = some p) :
    (interpretConst cst).bind (interpretAdd (.felt p a)) = some (.felt p a) := by
  simp only [interpretConst, hp, hval, reduce, Int.zero_emod, Int.toNat_zero,
    Option.bind_some, interpretAdd, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt ha]

end Veir.FeltInterp

end
