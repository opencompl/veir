module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Interfaces.ControlFlowInterfaces
public import Veir.Verifier.Basic
public import Veir.Dialects.WasmSSA.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive WasmSSA where
-- | abs
| add
| and
| block
| block_return
-- | branch_if
| call
-- | ceil
| clz
| const
-- | convert_s
-- | convert_u
-- | copysign
| ctz
-- | demote
-- | div
| div_si
| div_ui
| eq
| eqz
-- | extend
-- | extend_i32_s
-- | extend_i32_u
-- | floor
| func
-- | ge
| ge_si
| ge_ui
-- | global
-- | global_get
-- | global_set
-- | gt
| gt_si
| gt_ui
-- | if
-- | import_func
-- | import_global
-- | import_mem
-- | import_table
-- | le
| le_si
| le_ui
-- | local
-- | local_get
-- | local_set
-- | local_tee
-- | loop
-- | lt
| lt_si
| lt_ui
-- | max
-- | memory
-- | min
| mul
| ne
-- | nearest
-- | neg
| or
| popcnt
-- | promote
-- | reinterpret
| rem_si
| rem_ui
| return
-- | rotl
-- | rotr
-- | select
-- | shl
-- | shr_s
-- | shr_u
-- | sqrt
| sub
-- | table
-- | trunc
-- | trunc_sat_si
-- | trunc_sat_ui
-- | trunc_si
-- | trunc_ui
-- | wrap
| xor
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def WasmSSA.propertiesOf (op : WasmSSA) : Type :=
  match op with
  | .call => WasmSSACallProperties
  | .const => WasmSSAConstProperties
  | .func => WasmSSAFuncProperties
  | _ => Unit

def WasmSSA.fromAttrDict
    (op : WasmSSA) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (WasmSSA.propertiesOf op) :=
  match op with
  | .call => WasmSSACallProperties.fromAttrDict attrDict
  | .const => WasmSSAConstProperties.fromAttrDict attrDict
  | .func => WasmSSAFuncProperties.fromAttrDict attrDict
  | .add
  | .and
  | .block
  | .block_return
  | .clz
  | .ctz
  | .div_si
  | .div_ui
  | .eq
  | .eqz
  | .ge_si
  | .ge_ui
  | .gt_si
  | .gt_ui
  | .le_si
  | .le_ui
  | .lt_si
  | .lt_ui
  | .mul
  | .ne
  | .or
  | .popcnt
  | .rem_si
  | .rem_ui
  | .return
  | .sub
  | .xor => .ok ()

def WasmSSA.toAttrDict
    (op : WasmSSA) (props : WasmSSA.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .call | .const | .func => props.toAttrDict
  | _ => Std.HashMap.emptyWithCapacity 0

#generate_dialect WasmSSA

instance : IsOpCode WasmSSA where
  fromName := WasmSSA.fromName
  name := WasmSSA.name
  propertiesOf := WasmSSA.propertiesOf
  fromAttrDict := WasmSSA.fromAttrDict
  toAttrDict := WasmSSA.toAttrDict

/--
Verify the local invariants of a `wasmssa` operation in any operation-info type
containing the `wasmssa` dialect.
-/
@[expose]
def WasmSSA.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo WasmSSA] (opType : WasmSSA) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .add | .sub | .mul -- <-- TODO: split out and account for float ops when support added
  | .and | .or | .xor | .div_si | .div_ui | .rem_si | .rem_ui => do
    op.verifyIntegerBinop ctx opIn
  | .clz | .ctz | .popcnt => do
    let _ ← op.verifyIntegerUnop ctx opIn
  | .eq | .ne -- <-- TODO: split out and add float checks when support added
  | .lt_si | .lt_ui | .le_si | .le_ui | .gt_si | .gt_ui | .ge_si | .ge_ui => do
      op.verifyCmpResultGeneric ctx opIn (IntegerType.signless 32)
  | .eqz => do
    op.verifyPlainOpCounts ctx opIn 1 1
    let operand := op.getOperand! ctx.raw 1
    let bitness_error_msg := "wasmssa.eqz: Expected i32 or i64 operand type"
    ((operand.getType! ctx.raw).verifyI32 bitness_error_msg) <|> ((operand.getType! ctx.raw).verifyI64 bitness_error_msg)
    op.verifyResultTypeMatches ctx (IntegerType.signless 32) "wasmssa.eqz: Expected i32 result type"
  | .block => do
    -- `block` is a terminator of the enclosing block that owns a body region.
    -- Its `inputs` seed the body's entry-block arguments, and `target` is
    -- where control resumes once the body exits via `block_return`.
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "wasmssa.block: Expected 1 region"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "wasmssa.block: Expected 0 results"
    if op.getNumSuccessors ctx.raw opIn ≠ 1 then
      throw "wasmssa.block: Expected 1 successor"
    let body := op.getRegion! ctx.raw 0
    let some entry := body.getFirstBlock! ctx.raw
      | throw "wasmssa.block: Expected a non-empty body region"
    if entry.getNumArguments! ctx.raw ≠ op.getNumOperands ctx.raw opIn then
      throw s!"wasmssa.block: Expected the body entry block to take \
        {op.getNumOperands ctx.raw opIn} argument(s) (one per input), \
        got {entry.getNumArguments! ctx.raw}"
    op.verifyOperandTypesMatchTypeArray ctx 0 ((entry.getArgumentTypes! ctx.raw).map (·.val)) "wasmssa.block: body entry block"
  | .block_return => do
    op.verifyTerminatorCounts ctx opIn 0
    let some parent := op.getParentOp! ctx.raw
      | throw "wasmssa.block_return: Expected to be nested in a 'wasmssa.block'"
    if toDialect? WasmSSA (parent.getOpType! ctx.raw) ≠ some WasmSSA.block then
      throw "wasmssa.block_return: Expected to be nested in a 'wasmssa.block'"
    if parent.getNumSuccessors! ctx.raw ≠ 1 then
      throw "wasmssa.block_return: Expected the enclosing 'wasmssa.block' to have 1 successor"
    let target := parent.getSuccessor! ctx.raw 0
    if op.getNumOperands ctx.raw opIn ≠ target.getNumArguments! ctx.raw then
      throw s!"wasmssa.block_return: Expected {target.getNumArguments! ctx.raw} operand(s) \
        to match the target's block arguments, got {op.getNumOperands ctx.raw opIn}"
    op.verifyOperandTypesMatchTypeArray ctx 0 ((target.getArgumentTypes! ctx.raw).map (·.val)) "wasmssa.block_return: target"
  | .call => do
    -- Upstream wasmssa doesn't seem to bother checking whether calls
    -- match callee signatures, and it's non-obvious how to do that
    -- efficiently in VeIR, so skipping for now.
    if op.getNumOperands ctx.raw opIn = 0 then
      throw "wasmssa.call: Expected calle name"
    if op.getNumRegions ctx.raw opIn != 0 then
      throw "wasmssa.call: Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn != 0 then
      throw "wasmssa.call: Expected 0 successors"
  | .const => do
    op.verifyPlainOpCounts ctx opIn 0 1
    let props : WasmSSAConstProperties := op.getProperties! ctx.raw WasmSSA.const
    -- TODO: when adding float const support: add necessary checks here
    op.verifyNormalizedIntegerAttr ctx opIn props.value
    let const_type := props.value.type
    let const_value := props.value.value
    if const_type.bitwidth != 32 && const_type.bitwidth != 64 then
      throw s!"wasmssa.const: Expected 32- or 64-bit integer, found {const_type.bitwidth}-bit const `{const_value}`"
    let result_type := (op.getResult 0).getType! ctx.raw
    if result_type.val != .integerType const_type then
      throw s!"wasmssa.const: Expected value and result types to match ({const_type} ≠ {result_type})"
  | .func => do
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "wasmssa.func: Expected 1 region"
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "wasmssa.func: Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "wasmssa.func: Expected 0 results"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "wasmssa.func: Expected 0 successors"
  | .return => do
    op.verifyTerminatorCounts ctx opIn 0
    if let some (_, props) := op.getMatchingAncestorOpUnbounded? ctx.raw WasmSSA.func then
        let funcOutputType := props.function_type.outputs
        let opOperandCount := op.getNumOperands ctx.raw opIn
        if opOperandCount ≠ funcOutputType.size then
          throw s!"wasmssa.return: Expected wasmssa.return operand count ({opOperandCount}) to match enclosing function ({funcOutputType.size})"
        op.verifyOperandTypesMatchTypeArray ctx 0 funcOutputType "wasmssa.return"

@[get_effects]
def WasmSSA.getEffects
    (op : WasmSSA) (_props : WasmSSA.propertiesOf op) : MemoryEffects :=
  match op with
  | _ => .none

def WasmSSA.isConstantLike (op : WasmSSA) : Bool :=
  match op with
  | _ => false

def WasmSSA.symbolInterface? (op : WasmSSA) : Option (SymbolOpInterface (WasmSSA.propertiesOf op)) :=
  match op with
  | .func => some { getSymName := fun props => some props.sym_name }
  | _ => none

def WasmSSA.functionInterface? (op : WasmSSA) : Option (FunctionOpInterface (WasmSSA.propertiesOf op)) :=
  match op with
  | .func =>
    some {
      getFunctionType := fun props => props.function_type
      setFunctionType := fun props functionType =>
          { props with function_type := functionType }
    }
  | _ => none

def WasmSSA.branchOpInterface? (op : WasmSSA) : Option (BranchOpInterface (WasmSSA.propertiesOf op)) :=
  match op with
  | _ => none

def WasmSSA.hasSSADominance (_op : WasmSSA) (_index : Nat) : Bool :=
  true

@[is_terminator]
def WasmSSA.isTerminator (op : WasmSSA) : Bool :=
  match op with
  | .block | .block_return | .return => true
  | _ => false

def WasmSSA.isIsolatedFromAbove (op : WasmSSA) : Bool :=
  match op with
  | _ => false


instance : HasOpInfo WasmSSA where
  verifyLocalInvariants := WasmSSA.verifyLocalInvariants
  getEffects := WasmSSA.getEffects
  isConstantLike := WasmSSA.isConstantLike
  symbolInterface? := WasmSSA.symbolInterface?
  functionInterface? := WasmSSA.functionInterface?
  branchOpInterface? := WasmSSA.branchOpInterface?
  hasSSADominance := WasmSSA.hasSSADominance
  isTerminator := WasmSSA.isTerminator
  isIsolatedFromAbove := WasmSSA.isIsolatedFromAbove

end

end Veir
