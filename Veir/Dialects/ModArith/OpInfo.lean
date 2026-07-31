module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.ModArith.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Mod_Arith where
| add
| constant
| mul
| sub
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Mod_Arith.propertiesOf (op : Mod_Arith) : Type :=
match op with
| .constant => ModArithConstantProperties
| .add | .sub | .mul => Unit

def Mod_Arith.fromAttrDict
    (op : Mod_Arith) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Mod_Arith.propertiesOf op) := by
  cases op
  case constant => exact ModArithConstantProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Mod_Arith.toAttrDict
    (op : Mod_Arith) (props : Mod_Arith.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert
      "value".toUTF8 (Attribute.integerAttr props.value)
  | _ => Std.HashMap.emptyWithCapacity 0

def Mod_Arith.hasSideEffects
    (_op : Mod_Arith) (_props : Mod_Arith.propertiesOf _op) : Bool :=
  false

def Mod_Arith.readsMemory (_op : Mod_Arith) : Bool :=
  false

def Mod_Arith.isConstantLike (op : Mod_Arith) : Bool :=
  match op with
  | .constant => true
  | _ => false

def Mod_Arith.hasSSADominance (_op : Mod_Arith) (_index : Nat) : Bool :=
  true

#generate_dialect Mod_Arith

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

instance : HasDialectOpInfo Mod_Arith where
  fromName := Mod_Arith.fromName
  name := Mod_Arith.name
  propertiesOf := Mod_Arith.propertiesOf
  fromAttrDict := Mod_Arith.fromAttrDict
  toAttrDict := Mod_Arith.toAttrDict
  hasSideEffects := Mod_Arith.hasSideEffects
  readsMemory := Mod_Arith.readsMemory
  isConstantLike := Mod_Arith.isConstantLike
  foldsTo := Mod_Arith.foldsTo
  hasSSADominance := Mod_Arith.hasSSADominance
