import Veir.Interpreter.Basic

/-! Tests for the `comb` dialect's semantics, through `Veir.interpretOp'`.

Going through the dispatch rather than calling `Veir.Data.Comb` directly is deliberate: the
dispatch is where an operation's operands are matched to a common width, where the operations that
need it read their result width out of `resultTypes`, and where an attribute becomes a parameter.
Those are the joints a bug sits in, and a test of `Data.Comb` alone would not cross them.

The cases chosen are the ones where being wrong is *quiet*. An operation returning something wildly
different would be caught by anything; an operand order or a bit offset would be caught by almost
nothing.
-/

open Veir

private def ity (w : Nat) : TypeAttr := IntegerType.signless w

/-- Run one `comb` operation and read back a single integer result, or `none` if it did not
evaluate or produced poison. -/
private def comb (op : Comb) (props : Comb.propertiesOf op) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) : Option Nat := do
  let (results, _) ← Comb.interpretOp' op props resultTypes operands #[]
  let r : RuntimeValue ← results[0]?
  match r with
  | .int _ (.val v) => some v.toNat
  | _ => none

/-- Whether the operation evaluated to poison. -/
private def combIsPoison (op : Comb) (props : Comb.propertiesOf op) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) : Bool :=
  match Comb.interpretOp' op props resultTypes operands #[] with
  | some (results, _) =>
    match (results[0]? : Option RuntimeValue) with
    | some (.int _ .poison) => true
    | _ => false
  | none => false

private def i (w v : Nat) : RuntimeValue := .int w (.val (BitVec.ofNat w v))
private def poison (w : Nat) : RuntimeValue := .int w .poison

/-! ### Variadic integer operations

Wrap-around matters: these are modular at the operand width, and an implementation that widened
before operating would show up here. So does the unit each folds from -- `and` folding from zero
rather than all ones would return zero for everything.
-/

private def testVariadic : String := Id.run do
  if comb .add () #[ity 4] #[i 4 9, i 4 12] != some 5 then return "add"      -- 21 mod 16
  if comb .mul () #[ity 4] #[i 4 3, i 4 7] != some 5 then return "mul"       -- 21 mod 16
  if comb .and () #[ity 4] #[i 4 12, i 4 10] != some 8 then return "and"
  if comb .or () #[ity 4] #[i 4 12, i 4 10] != some 14 then return "or"
  if comb .xor () #[ity 4] #[i 4 12, i 4 10] != some 6 then return "xor"
  -- `comb` has no `not`; xor against all ones is CIRCT's idiom for it.
  if comb .xor () #[ity 4] #[i 4 10, i 4 15] != some 5 then return "xor as not"
  -- Really variadic, and really folding from the right unit.
  if comb .add () #[ity 4] #[i 4 1, i 4 2, i 4 3] != some 6 then return "add of three"
  if comb .and () #[ity 4] #[i 4 14, i 4 12, i 4 10] != some 8 then return "and of three"
  if comb .mul () #[ity 4] #[i 4 2, i 4 3] != some 6 then return "mul unit is one"
  if comb .and () #[ity 4] #[i 4 7] != some 7 then return "and unit is all ones"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testVariadic

/-! ### Poison propagates from any operand -/

private def testPoison : String := Id.run do
  if !combIsPoison .add () #[ity 4] #[i 4 1, poison 4] then return "add, poison last"
  if !combIsPoison .and () #[ity 4] #[poison 4, i 4 1] then return "and, poison first"
  if !combIsPoison .xor () #[ity 4] #[i 4 1, poison 4, i 4 2] then return "xor, poison in the middle"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testPoison

/-! ### Malformed operands are refused, not guessed at

Both of these are rejected by the verifier, so an interpreter should never see one. That is an
argument for refusing them rather than for crashing or inventing an answer: the first version of
this dispatch read `operands.toList[0]!`, which panics on an empty operand list.
-/

private def testMalformed : String := Id.run do
  if (comb .add () #[ity 4] #[]).isSome then return "add accepted no operands"
  if (comb .and () #[ity 4] #[]).isSome then return "and accepted no operands"
  if (comb .or () #[ity 4] #[]).isSome then return "or accepted no operands"
  if (comb .xor () #[ity 4] #[]).isSome then return "xor accepted no operands"
  if (comb .mul () #[ity 4] #[]).isSome then return "mul accepted no operands"
  -- Operands at disagreeing widths, rather than silently truncating or extending one.
  if (comb .add () #[ity 4] #[i 4 1, i 8 1]).isSome then return "add accepted a width mismatch"
  if (comb .or () #[ity 4] #[i 8 1, i 4 1]).isSome then return "or accepted a width mismatch"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testMalformed
