module

public import Veir.Data.LLVM.PoisonOr.Basic

open Veir.Data.LLVM.PoisonOr

namespace Veir.Data.LLVM

public section

@[expose]
def Int w := PoisonOr <| BitVec w

instance {w : Nat} : Inhabited (Int w) := ⟨poison⟩
instance {w : Nat} : Repr (Int w) where
  reprPrec x _ := match x with
    | .poison => "poison"
    | .value v => s!"value {v}"

instance {w : Nat} : ToString (Int w) where
  toString x := match x with
    | .poison => "poison"
    | .value v => s!"value {v}"

namespace Int

def add {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := do
  let x' ← x
  let y' ← y

  if nsw ∧ BitVec.saddOverflow x' y' then
    poison
  if nuw ∧ BitVec.uaddOverflow x' y' then
    poison

  value (x' + y')

instance {w : Nat} : Add (Int w) where
  add := add

def sub {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := do
  let x' ← x
  let y' ← y

  if nsw ∧ BitVec.ssubOverflow x' y' then
    poison
  if nuw ∧ BitVec.usubOverflow x' y' then
    poison

  value (x' - y')

instance {w : Nat} : Sub (Int w) where
  sub := sub

def mul {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := do
  let x' ← x
  let y' ← y

  if nsw ∧ BitVec.smulOverflow x' y' then
    poison
  if nuw ∧ BitVec.umulOverflow x' y' then
    poison

  value (x' * y')

instance {w : Nat} : Mul (Int w) where
  mul := mul

def udiv {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := do
  let x' ← x
  let y' ← y

  if exact ∧ x'.umod y' ≠ 0 then
    poison
  if y' = 0 then
    poison

  value (x' / y')

instance {w : Nat} : Div (Int w) where
  div := udiv

def sdiv {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := do
  let x' ← x
  let y' ← y

  if y' == 0 || (w != 1 && x' == (BitVec.intMin w) && y' == -1) then
    poison

  if exact ∧ x'.smod y' ≠ 0 then
    poison

  if y' = 0 then
    poison

  value (x' / y')

def urem {w : Nat} (x y : Int w) : Int w := do
  let x' ← x
  let y' ← y

  if y' = 0 then
    poison

  value (x' % y')

instance {w : Nat} : Mod (Int w) where
  mod := urem

def srem {w : Nat} (x y : Int w) : Int w := do
  let x' ← x
  let y' ← y

  if y' == 0 || (w != 1 && x' == (BitVec.intMin w) && y' == -1) then
    poison

  value (x'.srem y')

def shl {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := do
  let x' ← x
  let y' ← y

  if nsw ∧ ((x' <<< y').sshiftRight'  y' ≠ x') then
    poison
  if nuw ∧ ((x' <<< y') >>> y' ≠ x') then
    poison
  if y' ≥ w then
    poison

  value (x' <<< y')

instance {w : Nat} : ShiftLeft (Int w) where
  shiftLeft := shl

def lshr {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := do
  let x' ← x
  let y' ← y

  if y' ≥ w then
    poison

  if exact ∧(x' >>> y') <<< y' ≠ x' then
    poison

  value (x' >>> y')

instance {w : Nat} : ShiftRight (Int w) where
  shiftRight := lshr

def ashr {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := do
  let x' ← x
  let y' ← y

  if y' ≥ w then
    poison

  if exact ∧ (x' >>> y') <<< y' ≠ x' then
    poison

  value (x'.sshiftRight' y')

def and {w : Nat} (x y : Int w) : Int w := do
  let x' ← x
  let y' ← y
  value (x' &&& y')

instance {w : Nat} : AndOp (Int w) where
  and := and

def or {w : Nat} (x y : Int w) : Int w := do
  let x' ← x
  let y' ← y
  value (x' ||| y')

instance {w : Nat} : OrOp (Int w) where
  or := or

def xor {w : Nat} (x y : Int w) : Int w := do
  let x' ← x
  let y' ← y
  value (x' ^^^ y')

instance {w : Nat} : XorOp (Int w) where
  xor := xor

def cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) : Int w₂ :=
  match x with
  | value v => value (v.cast h)
  | poison => poison


end Int

end

end Veir.Data.LLVM
