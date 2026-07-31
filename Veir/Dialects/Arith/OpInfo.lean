module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Arith.Properties
public import Veir.Dialects.LLVM.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Arith where
| addi
| addui_extended
| andi
| ceildivsi
| ceildivui
| cmpi
| constant
| divsi
| divui
| extsi
| extui
| floordivsi
| maxsi
| maxui
| minsi
| minui
| muli
| mulsi_extended
| mului_extended
| ori
| remsi
| remui
| select
| shli
| shrsi
| shrui
| subi
| subui_extended
| trunci
| xori
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Arith.propertiesOf (op : Arith) : Type :=
match op with
| .constant => ArithConstantProperties
| .addi => ArithIntegerOverflowFlagsProperties
| .subi => ArithIntegerOverflowFlagsProperties
| .muli => ArithIntegerOverflowFlagsProperties
| .divsi => ExactProperties
| .divui => ExactProperties
| .cmpi => IcmpProperties
| .shli => ArithIntegerOverflowFlagsProperties
| .shrsi => ExactProperties
| .shrui => ExactProperties
| .ori => DisjointProperties
| .trunci => ArithIntegerOverflowFlagsProperties
| .extui => NnegProperties
| _ => Unit

def Arith.fromAttrDict
    (op : Arith) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Arith.propertiesOf op) := by
  cases op
  case constant => exact ArithConstantProperties.fromAttrDict attrDict
  case addi | subi | muli | shli | trunci =>
    exact ArithIntegerOverflowFlagsProperties.fromAttrDict attrDict
  case divsi | divui | shrsi | shrui =>
    exact ExactProperties.fromAttrDict attrDict
  case cmpi => exact IcmpProperties.fromAttrDictFor "arith.cmpi" attrDict
  case ori => exact DisjointProperties.fromAttrDict attrDict
  case extui => exact NnegProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Arith.toAttrDict
    (op : Arith) (props : Arith.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert
      "value".toUTF8 (Attribute.integerAttr props.value)
  | .addi | .subi | .muli | .shli | .trunci => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.attr.nsw || props.attr.nuw then
      dict := dict.insert
        "overflowFlags".toUTF8
        (Attribute.arithIntegerOverflowFlagsAttr props.attr)
    dict
  | .cmpi =>
    let value := IntegerAttr.mk (Int.ofNat props.predicate.toNat) (IntegerType.mk 64)
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr value)
  | .divsi | .divui | .shrsi | .shrui => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.exact then
      dict := dict.insert "exact".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .ori => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.disjoint then
      dict := dict.insert "disjoint".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .extui => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.nneg then
      dict := dict.insert "nneg".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | _ => Std.HashMap.emptyWithCapacity 0

def Arith.hasSideEffects (_op : Arith) (_props : Arith.propertiesOf _op) : Bool :=
  false

def Arith.readsMemory (_op : Arith) : Bool :=
  false

def Arith.isConstantLike (op : Arith) : Bool :=
  match op with
  | .constant => true
  | _ => false

def Arith.hasSSADominance (_op : Arith) (_index : Nat) : Bool :=
  true

#generate_dialect Arith

/--
  Fold table for `arith` operations with partially-constant operands.
  The all-constant case is handled generically by `OpCode.foldsTo`.
-/
def Arith.foldsTo (op : Arith) (properties : Arith.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  match op with
  | .addi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .subi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .muli =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .andi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = BitVec.allOnes bw then .useOperand 0
      else .noFold
    | _ => .noFold
  | .ori =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then
        .useConstant (.int bw (.val (BitVec.allOnes bw)))
      else .noFold
    | _ => .noFold
  | .xori =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shli =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shrsi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shrui =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  -- Division / remainder by zero is immediate UB: fold to poison.
  | .divsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .divui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .ceildivui | .ceildivsi | .floordivsi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] =>
      if c = 1 then .useOperand 0 else .noFold
    | _ => .noFold
  | .remsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 ∨ c = BitVec.allOnes bw then
        .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .remui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .maxsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMin bw then .useOperand 0
      else if c = BitVec.intMax bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .minsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMax bw then .useOperand 0
      else if c = BitVec.intMin bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .maxui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .minui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.allOnes bw then .useOperand 0
      else if c = 0 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .cmpi =>
    match constOperands.toList with
    | [_, some (.int 1 (.val c))] =>
      if properties.predicate = .ne ∧ c = 0 then .useOperand 0
      else if properties.predicate = .eq ∧ c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .select => Fold.selectFoldsTo resultTypes constOperands
  | _ => .noFold

instance : HasDialectOpInfo Arith where
  fromName := Arith.fromName
  name := Arith.name
  propertiesOf := Arith.propertiesOf
  fromAttrDict := Arith.fromAttrDict
  toAttrDict := Arith.toAttrDict
  hasSideEffects := Arith.hasSideEffects
  readsMemory := Arith.readsMemory
  isConstantLike := Arith.isConstantLike
  foldsTo := Arith.foldsTo
  hasSSADominance := Arith.hasSSADominance

end

end Veir
