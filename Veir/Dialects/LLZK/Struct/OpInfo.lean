module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Struct.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Struct where
| «def»
| member
| new
| readm
| writem
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Struct.propertiesOf (op : LLZK.Struct) : Type :=
match op with
| .«def» => StructDefProperties
| .member => StructMemberProperties
| .new => Unit
| .readm => StructReadProperties
| .writem => StructWriteProperties

def LLZK.Struct.fromAttrDict
    (op : LLZK.Struct) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Struct.propertiesOf op) :=
  match op with
  | .«def» => StructDefProperties.fromAttrDict attrDict
  | .member => StructMemberProperties.fromAttrDict "struct.member" attrDict
  | .new => .ok ()
  | .readm => StructReadProperties.fromAttrDict "struct.readm" "member_name" attrDict
  | .writem => StructWriteProperties.fromAttrDict "struct.writem" "member_name" attrDict

def LLZK.Struct.toAttrDict
    (op : LLZK.Struct) (props : LLZK.Struct.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op, props with
  | .«def», props => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    dict := dict.insert "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)
    dict
  | .member, props => props.toAttrDict
  | .new, _ => Std.HashMap.emptyWithCapacity 0
  | .readm, props => props.toAttrDict "member_name"
  | .writem, props =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "member_name".toUTF8 (Attribute.flatSymbolRefAttr props.name_ref)

/--
`struct.def` and the member declarations are symbol-carrying declarations
with no results; VEIR does not model the `Symbol` trait, so they report
`.unknown` to keep DCE from erasing them (the `global.def` precedent).
Reads and writes report their corresponding effects; `struct.new` allocates.
-/
def LLZK.Struct.getEffects
    (op : LLZK.Struct) (_props : LLZK.Struct.propertiesOf op) : MemoryEffects :=
  match op with
  | .«def» | .member => .unknown
  | .new => .allocate
  | .readm => .read
  | .writem => .write

def LLZK.Struct.isConstantLike (_op : LLZK.Struct) : Bool :=
  false

def LLZK.Struct.isIsolatedFromAbove (op : LLZK.Struct) : Bool :=
  match op with
  | .«def» => true
  | _ => false

def LLZK.Struct.getRegionKind (op : LLZK.Struct) (_index : Nat) : RegionKind :=
  match op with
  | .«def» => .Graph
  | _ => .SSACFG

def LLZK.Struct.hasSSADominance (op : LLZK.Struct) (_index : Nat) : Bool :=
  match op with
  | .«def» => false
  | _ => true

def LLZK.Struct.hasNoTerminator (op : LLZK.Struct) (_index : Nat) : Bool :=
  match op with
  | .«def» => true
  | _ => false

#generate_dialect LLZK.Struct

instance : IsOpCode LLZK.Struct where
  fromName := LLZK.Struct.fromName
  name := LLZK.Struct.name
  propertiesOf := LLZK.Struct.propertiesOf
  fromAttrDict := LLZK.Struct.fromAttrDict
  toAttrDict := LLZK.Struct.toAttrDict

@[expose]
def LLZK.Struct.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Struct] (opType : LLZK.Struct) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .«def» => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "struct.def: Expected 0 operand(s)"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "struct.def: Expected 0 result(s)"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "struct.def: Expected 1 region (the struct body)"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "struct.def: Expected 0 successors"
  | .member => op.verifyPlainOpCounts ctx opIn 0 0
  | .new => op.verifyPlainOpCounts ctx opIn 0 1
  | .readm => do
    let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
    if op.getNumOperands ctx.raw opIn < 1 then
      throw s!"{instrName}: Expected at least 1 operand (the component)"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw s!"{instrName}: Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw s!"{instrName}: Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw s!"{instrName}: Expected 0 successors"
  | .writem => op.verifyPlainOpCounts ctx opIn 2 0

instance : HasOpInfo LLZK.Struct where
  verifyLocalInvariants := LLZK.Struct.verifyLocalInvariants
  getEffects := LLZK.Struct.getEffects
  isConstantLike := LLZK.Struct.isConstantLike
  getRegionKind := LLZK.Struct.getRegionKind
  hasSSADominance := LLZK.Struct.hasSSADominance
  hasNoTerminator := LLZK.Struct.hasNoTerminator
  isIsolatedFromAbove := LLZK.Struct.isIsolatedFromAbove

end

end Veir
