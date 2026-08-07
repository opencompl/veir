module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Func.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Func where
| func
| call
| return
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Func.propertiesOf (op : Func) : Type :=
match op with
| .func => FuncFuncProperties
| .call => FuncCallProperties
| _ => Unit

def Func.fromAttrDict
    (op : Func) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Func.propertiesOf op) := by
  cases op
  case func => exact FuncFuncProperties.fromAttrDict attrDict
  case call => exact FuncCallProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Func.toAttrDict
    (op : Func) (props : Func.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .call => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "callee".toUTF8 (.flatSymbolRefAttr props.callee)
    dict
  | .func => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    if let some sym_name := props.sym_name then
      dict := dict.insert "sym_name".toUTF8 (.stringAttr sym_name)
    if let some function_type := props.function_type then
      dict := dict.insert "function_type".toUTF8 function_type
    dict
  | _ => Std.HashMap.emptyWithCapacity 0

def Func.hasSideEffects (_op : Func) (_props : Func.propertiesOf _op) : Bool :=
  true

def Func.readsMemory (op : Func) (_props : Func.propertiesOf op) : Bool :=
  match op with
  | .call => true
  | .func | .return => false

def Func.writesMemory (op : Func) (_props : Func.propertiesOf op) : Bool :=
  match op with
  | .call => true
  | .func | .return => false

def Func.isConstantLike (_op : Func) : Bool :=
  false

def Func.hasSSADominance (_op : Func) (_index : Nat) : Bool :=
  true

def Func.isTerminator (op : Func) : Bool :=
  match op with
  | .return => true
  | .func | .call => false

#generate_dialect Func

instance : HasOpInfo Func where
  fromName := Func.fromName
  name := Func.name
  propertiesOf := Func.propertiesOf
  fromAttrDict := Func.fromAttrDict
  toAttrDict := Func.toAttrDict
  hasSideEffects := Func.hasSideEffects
  readsMemory := Func.readsMemory
  writesMemory := Func.writesMemory
  isConstantLike := Func.isConstantLike
  hasSSADominance := Func.hasSSADominance
  isTerminator := Func.isTerminator

end

end Veir
