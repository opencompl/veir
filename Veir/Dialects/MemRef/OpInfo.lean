module

public import Veir.IR.OpInfo
public import Veir.Dialects.MemRef.Properties
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
Access to statically shaped memrefs.

VeIR covers only the fragment needed to read and write named global state:
`global` declares a symbol, `get_global` turns that symbol into a memref
value, and `load`/`store` access it at rank-many `index` positions. The
allocation, view, and metadata operations of MLIR's `memref` dialect, dynamic
shapes, layouts, and memory spaces are all outside this fragment; see
`MemRefType`.
-/
@[opcodes]
inductive MemRef where
/-- `() -> ()`: declare a global memref symbol with a statically shaped type. -/
| global
/-- `() -> memref<...>`: the memref for a named `memref.global`. -/
| get_global
/-- `(memref<...>, index...) -> T`: read the element at the given indices. -/
| load
/-- `(T, memref<...>, index...) -> ()`: write the element at the given indices. -/
| store
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def MemRef.propertiesOf (op : MemRef) : Type :=
match op with
| .global => MemRefGlobalProperties
| .get_global => MemRefGetGlobalProperties
| .load | .store => Unit

/--
Reject any property on an operation that carries none.

MLIR gives `load` and `store` an optional `nontemporal`, `alignment`, and
`invariant` attribute, none of which is modelled here. Each one changes what
the operation means, so accepting it and dropping it would silently alter the
program; carrying one is an error instead.
-/
private def noProperties (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Unit :=
  if attrDict.size > 0 then
    let plural := if attrDict.size = 1 then "property" else "properties"
    let names := attrDict.toArray.map fun (key, _) => String.fromUTF8! key
    let names := names.insertionSort fun a b => (compare a b).isLT
    .error s!"{opName}: expected no properties, but got {attrDict.size} {plural}: \
      {String.intercalate ", " names.toList}"
  else
    .ok ()

def MemRef.fromAttrDict (op : MemRef) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (MemRef.propertiesOf op) := by
  cases op
  case global => exact MemRefGlobalProperties.fromAttrDict attrDict
  case get_global => exact MemRefGetGlobalProperties.fromAttrDict attrDict
  case load => exact noProperties "memref.load" attrDict
  case store => exact noProperties "memref.store" attrDict

def MemRef.toAttrDict
    (op : MemRef) (props : MemRef.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .global => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    dict := dict.insert "type".toUTF8 props.type
    dict
  | .get_global => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "name".toUTF8 (.flatSymbolRefAttr props.name)
    dict
  | .load | .store => Std.HashMap.emptyWithCapacity 0

/--
`get_global` is pure: MLIR guarantees it always yields the same memref, so
common subexpression elimination may share it and dead code elimination may
drop it when unused.

`global` is given unknown effects for the same reason `llvm.mlir.global` is:
it declares storage that `get_global` reaches by symbol rather than by SSA use,
so claiming it has no effects would make it trivially dead and let DCE erase a
declaration that is still referenced.
-/
@[get_effects]
def MemRef.getEffects
    (op : MemRef) (_props : MemRef.propertiesOf op) : MemoryEffects :=
  match op with
  | .global => .unknown
  | .get_global => .none
  | .load => .read
  | .store => .write

def MemRef.isConstantLike (_op : MemRef) : Bool :=
  false

def MemRef.hasSSADominance (_op : MemRef) (_index : Nat) : Bool :=
  true

#generate_dialect MemRef

instance : IsOpCode MemRef where
  fromName := MemRef.fromName
  name := MemRef.name
  propertiesOf := MemRef.propertiesOf
  fromAttrDict := MemRef.fromAttrDict
  toAttrDict := MemRef.toAttrDict

/-- Check that `ty` is a `memref` type, and return it. -/
def TypeAttr.verifyMemRefType
    (ty : TypeAttr) (errMsg : String) : Except String MemRefType :=
  match ty.val with
  | .memRefType type => pure type
  | _ => throw errMsg

/-- Operands `[first, stop)` are the indices of an access, and must be `index`. -/
def MemRef.verifyIndexOperands {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (first stop : Nat) (instrName : String) :
    Except String PUnit := do
  for i in [first:stop] do
    ((op.getOperand! ctx.raw i).getType! ctx.raw).verifyIndexType
      s!"{instrName}: Expected operand {i} to have index type"

/--
Verify a `memref` operation.

`global` takes and produces nothing and its `type` property must be a memref
type; `get_global` produces one memref and nothing else. `load` and `store`
take a memref followed by exactly rank-many `index` operands -- so a rank-0
memref is accessed with no indices at all -- and the loaded result, or the
stored value, has the memref's element type. That the indices are in bounds is
a precondition, not a checked invariant: violating it is undefined behavior.
-/
@[expose]
def MemRef.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo MemRef]
    (opType : MemRef) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  op.checkIsNonNullIntegerType ctx opIn
  match opType with
  | .global =>
    op.verifyPlainOpCounts ctx opIn 0 0
    let props : MemRef.propertiesOf .global := op.getProperties! ctx.raw MemRef.global
    let _ ← props.type.verifyMemRefType
      s!"{instrName}: Expected 'type' to be a memref type"
  | .get_global =>
    op.verifyPlainOpCounts ctx opIn 0 1
    let _ ← ((op.getResult 0).get! ctx.raw).type.verifyMemRefType
      s!"{instrName}: Expected result 0 to have memref type"
  | .load =>
    if op.getNumOperands ctx.raw opIn = 0 then
      throw s!"{instrName}: Expected at least 1 operand"
    let memRefType ← ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyMemRefType
      s!"{instrName}: Expected operand 0 to have memref type"
    let numOperands := 1 + memRefType.shape.size
    op.verifyPlainOpCounts ctx opIn numOperands 1
    MemRef.verifyIndexOperands op ctx 1 numOperands instrName
    if ((op.getResult 0).get! ctx.raw).type.val ≠ memRefType.elementType then
      throw s!"{instrName}: Expected result 0 to have the memref's element type"
  | .store =>
    if op.getNumOperands ctx.raw opIn < 2 then
      throw s!"{instrName}: Expected at least 2 operands"
    let memRefType ← ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyMemRefType
      s!"{instrName}: Expected operand 1 to have memref type"
    let numOperands := 2 + memRefType.shape.size
    op.verifyPlainOpCounts ctx opIn numOperands 0
    MemRef.verifyIndexOperands op ctx 2 numOperands instrName
    if ((op.getOperand! ctx.raw 0).getType! ctx.raw).val ≠ memRefType.elementType then
      throw s!"{instrName}: Expected operand 0 to have the memref's element type"

instance : HasOpInfo MemRef where
  verifyLocalInvariants := MemRef.verifyLocalInvariants
  getEffects := MemRef.getEffects
  isConstantLike := MemRef.isConstantLike
  hasSSADominance := MemRef.hasSSADominance

end

end Veir
