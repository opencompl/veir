module

public import Veir.Dialects.ModArith.OpInfo.Basic

public section

namespace Veir

/-- The positive modulus and storage width of a single `mod_arith` result. -/
private def modArithResultInfo (resultTypes : Array TypeAttr) : Option (Nat × Nat) := do
  let [resultType] := resultTypes.toList | none
  let .modArithType modArithType := resultType.val | none
  if modArithType.modulus.value ≤ 0 then none
  else some (modArithType.modulus.value.toNat, modArithType.modulus.type.bitwidth)

/--
  Fold table for partially-constant `mod_arith` operations.

  Returning an operand for the usual zero and one identities would require
  that operand to be a canonical residue. `RuntimeValue.Conforms` guarantees
  only its storage width, so the only partial fold here is multiplication by
  zero, whose constant result refines a poison operand as well.
-/
def Mod_Arith.foldsTo (op : Mod_Arith) (_properties : Mod_Arith.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  match modArithResultInfo resultTypes with
  | none => .noFold
  | some (modulus, bitwidth) =>
    let isZeroResidue {w : Nat} (value : BitVec w) :=
      value.toNat % modulus = 0
    match op with
    | .mul =>
      match constOperands.toList with
      | [some (.int _ (.val c)), _] =>
        if isZeroResidue c then .useConstant (.int bitwidth (.val 0)) else .noFold
      | [_, some (.int _ (.val c))] =>
        if isZeroResidue c then .useConstant (.int bitwidth (.val 0)) else .noFold
      | _ => .noFold
    | .add | .sub | .constant => .noFold

end Veir
