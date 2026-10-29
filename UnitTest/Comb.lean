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

/-! ### Subtraction and shifts

Binary rather than variadic, so the arity is part of what is checked: a variadic reading of `sub`
would fold three operands instead of refusing them.

A shift at or past the operand width is **poison** in CIRCT, where `BitVec.shiftLeft` gives zero.
That is the one place this semantics is not simply Lean's, and the only way to notice is to ask.
-/

private def testSubAndShifts : String := Id.run do
  if comb .sub () #[ity 4] #[i 4 3, i 4 5] != some 14 then return "sub"      -- -2 mod 16
  if comb .shl () #[ity 4] #[i 4 3, i 4 2] != some 12 then return "shl"
  if comb .shl () #[ity 4] #[i 4 9, i 4 1] != some 2 then return "shl out of the top"
  if comb .shru () #[ity 4] #[i 4 9, i 4 1] != some 4 then return "shru"
  if comb .shrs () #[ity 4] #[i 4 9, i 4 1] != some 12 then return "shrs sign extends"
  -- Logical and arithmetic differ on a negative operand, so both are really being tested.
  if comb .shru () #[ity 4] #[i 4 9, i 4 1] == comb .shrs () #[ity 4] #[i 4 9, i 4 1] then
    return "shru and shrs agree"
  -- At or past the width: poison, not zero.
  if !combIsPoison .shl () #[ity 4] #[i 4 3, i 4 4] then return "shl at the width"
  if !combIsPoison .shru () #[ity 4] #[i 4 3, i 4 7] then return "shru past the width"
  if !combIsPoison .shrs () #[ity 4] #[i 4 3, i 4 4] then return "shrs at the width"
  -- A shift by zero is in range and is the identity, so the bound is `≥ w` and not `> 0`.
  if comb .shl () #[ity 4] #[i 4 3, i 4 0] != some 3 then return "shl by zero"
  -- Poison propagates, and binary arity is enforced.
  if !combIsPoison .sub () #[ity 4] #[i 4 1, poison 4] then return "sub poison"
  if (comb .sub () #[ity 4] #[i 4 1, i 4 2, i 4 3]).isSome then return "sub took three"
  if (comb .shl () #[ity 4] #[i 4 1]).isSome then return "shl took one"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testSubAndShifts

/-! ### Comparison

CIRCT's `ICmpPredicate` is carried as the integer it prints as, and an off-by-one in that number
is a silent change of meaning rather than an error. All ten are checked, including the six the
CircuitHdl backend never emits -- a predicate table is exactly the kind of thing that is wrong in
one entry.

At width 4, `9` is `-7` signed and `6` is `6`, which separates the signed predicates from the
unsigned ones.
-/

private def testIcmp : String := Id.run do
  let c (p a b : Nat) : Option Nat :=
    comb .icmp { predicate := IntegerAttr.mk (Int.ofNat p) (IntegerType.signless 64) } #[ity 1]
      #[i 4 a, i 4 b]
  if c 0 6 6 != some 1 then return "eq"
  if c 0 6 9 != some 0 then return "eq false"
  if c 1 6 9 != some 1 then return "ne"
  if c 2 9 6 != some 1 then return "slt: -7 < 6"
  if c 3 9 9 != some 1 then return "sle"
  if c 4 6 9 != some 1 then return "sgt: 6 > -7"
  if c 5 6 6 != some 1 then return "sge"
  if c 6 6 9 != some 1 then return "ult: 6 < 9"
  if c 6 9 6 != some 0 then return "ult false"
  if c 7 9 9 != some 1 then return "ule"
  if c 8 9 6 != some 1 then return "ugt"
  if c 9 6 6 != some 1 then return "uge"
  -- The signed and unsigned readings of the same bits disagree, so these are two tests and not
  -- one written twice. Without this, a table with `slt` and `ult` transposed would pass.
  if c 2 9 6 == c 6 9 6 then return "slt and ult agree, so the predicate is being ignored"
  if c 4 6 9 == c 8 6 9 then return "sgt and ugt agree"
  -- A predicate outside the table is refused rather than defaulted to `eq`.
  if (comb .icmp { predicate := IntegerAttr.mk 10 (IntegerType.signless 64) } #[ity 1]
      #[i 4 6, i 4 6]).isSome then return "an unknown predicate was accepted"
  -- Poison, and arity.
  if !combIsPoison .icmp { predicate := IntegerAttr.mk 0 (IntegerType.signless 64) } #[ity 1]
      #[poison 4, i 4 1] then return "icmp poison"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testIcmp

/-! ### Mux

The one operation that is defined when an operand is not. A mux selects, so poison in the arm it
did *not* select cannot reach the result -- which is what makes a mux usable to guard an undefined
computation, and is worth a test rather than a comment. Poison in the condition is poison, since
then nothing was selected.

Its operands are also the only ones in the dialect that are deliberately at different widths: an
`i1` condition and two arms at the result width.
-/

private def testMux : String := Id.run do
  if comb .mux () #[ity 4] #[i 1 1, i 4 11, i 4 12] != some 11 then return "selects true"
  if comb .mux () #[ity 4] #[i 1 0, i 4 11, i 4 12] != some 12 then return "selects false"
  -- The exception, both ways round.
  if comb .mux () #[ity 4] #[i 1 1, i 4 7, poison 4] != some 7 then return "poison in the false arm"
  if comb .mux () #[ity 4] #[i 1 0, poison 4, i 4 9] != some 9 then return "poison in the true arm"
  -- But a poison condition selects nothing.
  if !combIsPoison .mux () #[ity 4] #[poison 1, i 4 7, i 4 9] then return "poison condition"
  -- Arity, and arms that disagree with each other.
  if (comb .mux () #[ity 4] #[i 1 1, i 4 2]).isSome then return "mux took two operands"
  if (comb .mux () #[ity 4] #[i 1 1, i 4 1, i 8 1]).isSome then return "mux took mismatched arms"
  -- A condition wider than one bit is refused rather than truncated.
  if (comb .mux () #[ity 4] #[i 4 1, i 4 1, i 4 2]).isSome then return "mux took an i4 condition"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testMux

