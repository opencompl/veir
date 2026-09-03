module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Global.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Global where
| «def»
| read
| write
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Global.propertiesOf (op : LLZK.Global) : Type :=
match op with
| .«def» => GlobalDefProperties
| .read => GlobalRefProperties
| .write => GlobalRefProperties

def LLZK.Global.fromAttrDict
    (op : LLZK.Global) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Global.propertiesOf op) :=
  match op with
  | .«def» => GlobalDefProperties.fromAttrDict attrDict
  | .read => GlobalRefProperties.fromAttrDict "global.read" attrDict
  | .write => GlobalRefProperties.fromAttrDict "global.write" attrDict

def LLZK.Global.toAttrDict
    (op : LLZK.Global) (props : LLZK.Global.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .«def» => Id.run do
    let mut dict := (Std.HashMap.emptyWithCapacity 4).insert
      "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)
    if props.constant then
      dict := dict.insert "constant".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict := dict.insert "type".toUTF8 props.type
    if let some initialValue := props.initial_value then
      dict := dict.insert "initial_value".toUTF8 initialValue
    return dict
  | .read | .write =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "name_ref".toUTF8 (Attribute.flatSymbolRefAttr props.name_ref)

@[get_effects]
def LLZK.Global.getEffects
    (op : LLZK.Global) (_props : LLZK.Global.propertiesOf op) : MemoryEffects :=
  match op with
  | .«def» => .unknown
  | .read => .read
  | .write => .write

def LLZK.Global.isConstantLike (_op : LLZK.Global) : Bool := false

def LLZK.Global.hasSSADominance (_op : LLZK.Global) (_index : Nat) : Bool := true

#generate_dialect LLZK.Global

instance : IsOpCode LLZK.Global where
  fromName := LLZK.Global.fromName
  name := LLZK.Global.name
  propertiesOf := LLZK.Global.propertiesOf
  fromAttrDict := LLZK.Global.fromAttrDict
  toAttrDict := LLZK.Global.toAttrDict

private partial def OperationPtr.getEnclosingBuiltinModule? {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Option OperationPtr :=
  match op.getParentOp! ctx with
  | none => none
  | some parent =>
    if IsOpCode.name (parent.getOpType! ctx) = "builtin.module".toUTF8 then
      some parent
    else
      parent.getEnclosingBuiltinModule? ctx

private def OperationPtr.resolveGlobalDef {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Global] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (props : GlobalRefProperties) : Except String GlobalDefProperties := do
  let some moduleOp := op.getEnclosingBuiltinModule? ctx.raw
    | throw "expected an enclosing builtin.module"
  let mut target : Option GlobalDefProperties := none
  for candidate in ctx.raw.operations.keys do
    if candidate.getParentOp! ctx.raw = some moduleOp then
      match toDialect? LLZK.Global (candidate.getOpType! ctx.raw) with
      | some .«def» =>
        let candidateProps : LLZK.Global.propertiesOf .«def» :=
          candidate.getProperties! ctx.raw LLZK.Global.«def»
        let candidateName := "@" ++ String.fromUTF8! candidateProps.sym_name.value
        if candidateName = props.name_ref.value then
          if target.isSome then
            throw s!"global reference '{props.name_ref}' is ambiguous"
          target := some candidateProps
      | _ => pure ()
  let some targetProps := target
    | throw s!"'{props.name_ref}' does not name a global.def"
  return targetProps

def LLZK.Global.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Global] (opType : LLZK.Global) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .«def» => do
    op.verifyPlainOpCounts ctx opIn 0 0
    match op.getParentOp! ctx.raw with
    | some parent =>
      if IsOpCode.name (parent.getOpType! ctx.raw) != "builtin.module".toUTF8 then
        throw "global.def: expected parent to be builtin.module"
    | none =>
      throw "global.def: expected parent to be builtin.module"
    let props : LLZK.Global.propertiesOf .«def» :=
      op.getProperties! ctx.raw LLZK.Global.«def»
    props.verify
  | .read => do
    op.verifyPlainOpCounts ctx opIn 0 1
    let props : LLZK.Global.propertiesOf .read :=
      op.getProperties! ctx.raw LLZK.Global.read
    let target ← op.resolveGlobalDef ctx props
    if (op.getResultTypes! ctx.raw)[0]! != target.type then
      throw s!"global.read: result type does not match '{props.name_ref}'"
  | .write => do
    op.verifyPlainOpCounts ctx opIn 1 0
    let props : LLZK.Global.propertiesOf .write :=
      op.getProperties! ctx.raw LLZK.Global.write
    let target ← op.resolveGlobalDef ctx props
    if target.constant then
      throw s!"global.write: cannot write to constant global '{props.name_ref}'"
    if (op.getOperandTypes! ctx.raw)[0]! != target.type then
      throw s!"global.write: operand type does not match '{props.name_ref}'"

instance : HasOpInfo LLZK.Global where
  verifyLocalInvariants := LLZK.Global.verifyLocalInvariants
  getEffects := LLZK.Global.getEffects
  isConstantLike := LLZK.Global.isConstantLike
  hasSSADominance := LLZK.Global.hasSSADominance

end

end Veir
