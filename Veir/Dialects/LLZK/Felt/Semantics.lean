module

public import Veir.IR.Attribute

/-!
# LLZK Felt semantics

Mathlib-free executable semantics for the built-in named fields supported by
LLZK. Unnamed fields, and names whose modulus is supplied externally, remain
uninterpreted.
-/

namespace Veir.FeltSemantics

public section

/-- Resolve the modulus of an LLZK built-in field. -/
def prime? (type : FeltType) : Option Nat :=
  match type.fieldName with
  | none => none
  | some name =>
    if name = "bn254".toUTF8 then
      some 21888242871839275222246405745257275088548364400416034343698204186575808495617
    else if name = "bn128".toUTF8 then
      some 21888242871839275222246405745257275088548364400416034343698204186575808495617
    else if name = "grumpkin".toUTF8 then
      some 21888242871839275222246405745257275088696311157297823662689037894645226208583
    else if name = "babybear".toUTF8 then some 2013265921
    else if name = "goldilocks".toUTF8 then some 18446744069414584321
    else if name = "mersenne31".toUTF8 then some 2147483647
    else if name = "koalabear".toUTF8 then some 2130706433
    else none

/-- Whether `value` is the canonical representative of an element of `type`.
    Unknown and unnamed fields remain uninterpreted. -/
def IsCanonical (type : FeltType) (value : Nat) : Prop :=
  match prime? type with
  | some p => value < p
  | none => False

instance (type : FeltType) (value : Nat) : Decidable (IsCanonical type value) :=
  match h : prime? type with
  | none => isFalse (by simp [IsCanonical, h])
  | some p =>
    if hvalue : value < p then
      isTrue (by simp [IsCanonical, h, hvalue])
    else
      isFalse (by simp [IsCanonical, h, hvalue])

/-- Reduce an integer to its canonical representative modulo `p`. -/
def reduce (p : Nat) (value : Int) : Nat :=
  (value % (p : Int)).toNat

/-- Addition of canonical field representatives. -/
def add (p lhs rhs : Nat) : Nat :=
  (lhs + rhs) % p

/-- Subtraction of field representatives, returning a canonical representative. -/
def sub (p lhs rhs : Nat) : Nat :=
  reduce p (Int.ofNat lhs - Int.ofNat rhs)

/-- Multiplication of canonical field representatives. -/
def mul (p lhs rhs : Nat) : Nat :=
  (lhs * rhs) % p

/-- Negation of a field representative, returning a canonical representative. -/
def neg (p value : Nat) : Nat :=
  reduce p (-Int.ofNat value)

end

end Veir.FeltSemantics
