module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Interfaces.ControlFlowInterfaces
public import Veir.Verifier.Basic
public import Veir.Dialects.WasmSSA.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

/---
WasmSSA opcodes.

Unsupported opcodes include all floating-point operations,
globals, imports, tables and memory operations.
-/
@[opcodes]
inductive WasmSSA where
-- | abs
| add
| and
| block
| block_return
| branch_if
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
| extend
| extend_i32_s
| extend_i32_u
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
| if
-- | import_func
-- | import_global
-- | import_mem
-- | import_table
-- | le
| le_si
| le_ui
| local
| local_get
| local_set
| local_tee
| loop
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
| rotl
| rotr
| select
| shl
| shr_s
| shr_u
-- | sqrt
| sub
-- | table
-- | trunc
-- | trunc_sat_si
-- | trunc_sat_ui
-- | trunc_si
-- | trunc_ui
| wrap
| xor
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def WasmSSA.propertiesOf (op : WasmSSA) : Type :=
  match op with
  | .branch_if => WasmSSABranchIfProperties
  | .call => WasmSSACallProperties
  | .const => WasmSSAConstProperties
  | .extend => WasmSSAExtendProperties
  | .func => WasmSSAFuncProperties
  | .local => WasmSSALocalProperties
  | _ => Unit

def WasmSSA.fromAttrDict
    (op : WasmSSA) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (WasmSSA.propertiesOf op) :=
  match op with
  | .branch_if => WasmSSABranchIfProperties.fromAttrDict attrDict
  | .call => WasmSSACallProperties.fromAttrDict attrDict
  | .const => WasmSSAConstProperties.fromAttrDict attrDict
  | .extend => WasmSSAExtendProperties.fromAttrDict attrDict
  | .func => WasmSSAFuncProperties.fromAttrDict attrDict
  | .local => WasmSSALocalProperties.fromAttrDict attrDict
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
  | .extend_i32_s
  | .extend_i32_u
  | .ge_si
  | .ge_ui
  | .gt_si
  | .gt_ui
  | .if
  | .le_si
  | .le_ui
  | .local_get
  | .local_set
  | .local_tee
  | .loop
  | .lt_si
  | .lt_ui
  | .mul
  | .ne
  | .or
  | .popcnt
  | .rem_si
  | .rem_ui
  | .return
  | .rotl
  | .rotr
  | .select
  | .shl
  | .shr_s
  | .shr_u
  | .sub
  | .xor
  | .wrap => expectNoProperties "wasmssa" attrDict

def WasmSSA.toAttrDict
    (op : WasmSSA) (props : WasmSSA.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .branch_if | .call | .const | .extend | .func | .local => props.toAttrDict
  | _ => Std.HashMap.emptyWithCapacity 0

#generate_dialect WasmSSA

instance : IsOpCode WasmSSA where
  fromName := WasmSSA.fromName
  name := WasmSSA.name
  propertiesOf := WasmSSA.propertiesOf
  fromAttrDict := WasmSSA.fromAttrDict
  toAttrDict := WasmSSA.toAttrDict

inductive IsFunc : WasmSSA → Type
  | func : IsFunc .func
instance : OpcodeFamily IsFunc where
  classify := fun t => match t with | .func => some .func | _ => none

inductive LabelLevelOp : WasmSSA → Type
  | block : LabelLevelOp .block
  | loop : LabelLevelOp .loop
  | if : LabelLevelOp .if

instance : OpcodeFamily LabelLevelOp where
  classify := fun t => match t with
    | .block => some .block
    | .if => some .if
    | .loop => some .loop
    | _ => none

abbrev WasmI32 : TypeAttr := IntegerType.signless 32
abbrev WasmI64 : TypeAttr := IntegerType.signless 64
abbrev WasmLocal : TypeAttr → TypeAttr := fun t => WasmSSA.LocalRefType.mk t

inductive WasmSSAOperationType where
  /-- Has a fixed set of possible input and output types -/
  | fixed (cases : Array (Array TypeAttr × Array TypeAttr))
  /-- Requires special handling -/
  | special


/--
This "table" accounts for the possible input and output type sets for most ops,
including all arithmetic and comparison ops.

Anything control-flow related should return .special to be handled separately.
-/
def WasmSSA.getExpectedTypes (opType : WasmSSA) : WasmSSAOperationType :=
  match opType with
  | .add | .sub | .mul -- <-- TODO: split out and account for float ops when support added
  | .and | .or | .xor | .div_si | .div_ui | .rem_si | .rem_ui
  | .shl | .shr_s | .shr_u | .rotl | .rotr =>
    .fixed #[(#[WasmI32, WasmI32], #[WasmI32]), (#[WasmI64, WasmI64], #[WasmI64])]
  | .clz | .ctz | .popcnt | .extend =>
    .fixed #[(#[WasmI32], #[WasmI32]), (#[WasmI64], #[WasmI64])]
  | .eq | .ne -- <-- TODO: split out and add float checks when support added
  | .lt_si | .lt_ui | .le_si | .le_ui | .gt_si | .gt_ui | .ge_si | .ge_ui =>
    .fixed #[(#[WasmI32, WasmI32], #[WasmI32]), (#[WasmI64, WasmI64], #[WasmI32])]
  | .extend_i32_s | .extend_i32_u =>
    .fixed #[(#[WasmI32], #[WasmI64])]
  | .wrap =>
    .fixed #[(#[WasmI64], #[WasmI32])]
  | .eqz =>
    .fixed #[(#[WasmI32], #[WasmI32]), (#[WasmI64], #[WasmI32])]
  | .const =>
    .fixed #[(#[], #[WasmI32]), (#[], #[WasmI64])]
  | .select =>
    .fixed #[(#[WasmI32, WasmI32, WasmI32], #[WasmI32]), (#[WasmI64, WasmI64, WasmI32], #[WasmI64])]
  | .local_get =>
    .fixed #[(#[WasmLocal WasmI32], #[WasmI32]), (#[WasmLocal WasmI64], #[WasmI64])]
  | .local_set =>
    .fixed #[(#[WasmLocal WasmI32, WasmI32], #[]), (#[WasmLocal WasmI64, WasmI64], #[])]
  | .local_tee =>
    .fixed #[(#[WasmLocal WasmI32, WasmI32], #[WasmI32]), (#[WasmLocal WasmI64, WasmI64], #[WasmI64])]
  | .block | .block_return | .branch_if | .call | .func | .if
  | .local | .loop | .return =>
    .special

@[expose]
def WasmSSA.verifyLocalInvariants
    {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo WasmSSA]
    (opType : WasmSSA)
    (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw)
    : Except String PUnit := do
  if let .fixed expectedTypes := getExpectedTypes opType then
    let opTypes := (op.getOperandTypes ctx.raw opIn, op.getResultTypes ctx.raw opIn)
    unless expectedTypes.contains opTypes do
      let prettyPrint : Array TypeAttr × Array TypeAttr → String := fun (operands, results) =>
        let operandStr := ", ".intercalate (operands.toList.map toString)
        let resultStr := ", ".intercalate (results.toList.map toString)
        if results.size > 1 then
          s!"({operandStr}) -> ({resultStr})"
        else
          s!"({operandStr}) -> {resultStr}"
      let expectedTypeString := " | ".intercalate (expectedTypes.map prettyPrint).toList
      throw s!"expected to have one of the following types: {expectedTypeString}; \
        but found type {prettyPrint opTypes} instead"

  match opType with
  -- All these are verified by checking against the table in getExpectedTypes.
  -- The assumption is anything simple enough to have a type describable there
  -- is some sort of pure op with no control flow or inner regions.
  | .add    | .eq           | .ge_ui | .lt_ui     | .popcnt | .shl
  | .and    | .eqz          | .gt_si | .local_get | .rem_si | .shr_s
  | .clz    | .gt_ui        | .ne    | .local_set | .rem_ui | .shr_u
  | .ctz    | .extend_i32_s | .le_si | .local_tee | .rotl   | .sub
  | .div_si | .extend_i32_u | .le_ui | .mul       | .or     | .xor
  | .div_ui | .ge_si        | .lt_si | .rotr      | .select | .wrap => do
    let opName := String.fromUTF8! opType.name
    let successorCount := op.getNumSuccessors ctx.raw opIn
    let regionCount := op.getNumRegions ctx.raw opIn
    if successorCount ≠ 0 then
      throw s!"{opName}: expected 0 successors, found {successorCount}"
    if regionCount ≠ 0 then
      throw s!"{opName}: expected 0 regions, found {regionCount}"

  | .block | .loop | .if => do
    let opName := String.fromUTF8! opType.name
    if opType = .if then
      if op.getNumOperands! ctx.raw = 0 then
        throw "wasmssa.if: expected 1 or more operands, but found 0"
      else
        let conditionType := (op.getOperand! ctx.raw 0).getType! ctx.raw
        if conditionType.val ≠ WasmI32 then
          throw s!"wasmssa.if: operand #0 must be 32-bit signless integer, but got '{conditionType}'"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw s!"{opName}: requires zero results"
    if op.getNumSuccessors ctx.raw opIn ≠ 1 then
      throw s!"{opName}: requires 1 successor but found {op.getNumSuccessors ctx.raw opIn}"
    let expectedRegions := if opType = .if then 2 else 1
    if op.getNumRegions ctx.raw opIn ≠ expectedRegions then
      throw s!"{opName}: {if opType = .if then "expected 2 regions" else "requires one region"}"
    let operandOffset := if opType = .if then 1 else 0
    let numInputs := op.getNumOperands ctx.raw opIn - operandOffset

    let some entry := (op.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
      | throw s!"{opName}: region #0 must not be empty"
    if entry.getNumArguments! ctx.raw ≠ numInputs then
      throw s!"{opName}: region #0 entry block expected {numInputs} argument(s) \
        to match the inputs, but found {entry.getNumArguments! ctx.raw}"
    op.verifyOperandTypesMatchTypeArray ctx operandOffset ((entry.getArgumentTypes! ctx.raw).map (·.val)) s!"{opName}: region #0 entry block"

    if opType = .if then
      if let some secondEntry := (op.getRegion! ctx.raw 1).getFirstBlock! ctx.raw then
        if secondEntry.getNumArguments! ctx.raw ≠ numInputs then
          throw s!"{opName}: region #1 entry block expected {numInputs} argument(s) \
            to match the inputs, but found {secondEntry.getNumArguments! ctx.raw}"
        op.verifyOperandTypesMatchTypeArray ctx operandOffset ((secondEntry.getArgumentTypes! ctx.raw).map (·.val)) s!"{opName}: region #1 entry block"

  | .block_return => do
    op.verifyTerminatorCounts ctx opIn 0
    let some labelLevelParentOp := op.getNthAncestorOpInMatchingChain? LabelLevelOp ctx.raw 0
      | throw "wasmssa.block_return: expects parent op to be one of 'wasmssa.block', 'wasmssa.loop', 'wasmssa.if'"
    if labelLevelParentOp.op.getNumSuccessors! ctx.raw ≠ 1 then
      throw "wasmssa.block_return: expects parent op to have 1 successor"
    let target := labelLevelParentOp.op.getSuccessor! ctx.raw 0
    if op.getNumOperands ctx.raw opIn ≠ target.getNumArguments! ctx.raw then
      throw s!"wasmssa.block_return: expected {target.getNumArguments! ctx.raw} operand(s) \
        to match the target block's arguments, but found {op.getNumOperands ctx.raw opIn}"
    op.verifyOperandTypesMatchTypeArray ctx 0 ((target.getArgumentTypes! ctx.raw).map (·.val)) "wasmssa.block_return: target block"

  | .branch_if => do
    op.verifyTerminatorCounts ctx opIn 1
    -- We know from WasmSSABranchIfProperties.fromAttrDict that it is a non-negative integer
    let expectedNesting := (op.getProperties! ctx.raw WasmSSA.branch_if).exitLevel.value.natAbs
    let some frameOp := op.getNthAncestorOpInMatchingChain? LabelLevelOp ctx.raw expectedNesting
      | throw s!"wasmssa.branch_if: expects {expectedNesting + 1} directly nested parent op(s) \
          of 'wasmssa.block', 'wasmssa.loop', 'wasmssa.if'"
    -- The branch target is the successor in the case of `if` or `block`,
    -- but the body in the case of `loop`.
    let target : BlockPtr ← match frameOp with
      | ⟨.block, frameOp, _⟩
      | ⟨.if, frameOp, _⟩ =>
        if frameOp.getNumSuccessors! ctx.raw ≠ 1 then
          throw "wasmssa.branch_if: expects the target op to have 1 successor"
        else
          pure (frameOp.getSuccessor! ctx.raw 0)
      | ⟨.loop, loopOp, _⟩ =>
        if loopOp.getNumRegions! ctx.raw ≠ 1 then
          throw "wasmssa.branch_if: expects the target 'wasmssa.loop' to have one region"
        else
          let some target := (loopOp.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
            | throw "wasmssa.branch_if: expects the target 'wasmssa.loop' to have a non-empty region"
          pure target
    if op.getNumOperands ctx.raw opIn ≠ target.getNumArguments! ctx.raw + 1 then
      throw s!"wasmssa.branch_if: expected {target.getNumArguments! ctx.raw} input(s) \
        to match the target block's arguments, but found {op.getNumOperands ctx.raw opIn - 1}"
    let conditionType := (op.getOperand! ctx.raw 0).getType! ctx.raw
    if conditionType ≠ WasmI32 then
      throw s!"wasmssa.branch_if: operand #0 must be 32-bit signless integer, but got '{conditionType}'"
    op.verifyOperandTypesMatchTypeArray ctx 1 ((target.getArgumentTypes! ctx.raw).map (·.val)) "wasmssa.branch_if: target block"

  | .call => do
    -- Upstream wasmssa doesn't seem to bother checking whether calls
    -- match callee signatures, and it's non-obvious how to do that
    -- efficiently in VeIR, so skipping for now.
    if op.getNumRegions ctx.raw opIn != 0 then
      throw "wasmssa.call: requires zero regions"
    if op.getNumSuccessors ctx.raw opIn != 0 then
      throw s!"wasmssa.call: requires 0 successors but found {op.getNumSuccessors ctx.raw opIn}"

  | .const => do
    op.verifyPlainOpCounts ctx opIn 0 1
    let props : WasmSSAConstProperties := op.getProperties! ctx.raw WasmSSA.const
    -- TODO: when adding float const support: add necessary checks here
    op.verifyNormalizedIntegerAttr ctx opIn props.value
    if ((op.getResult 0).getType! ctx.raw).val ≠ .integerType props.value.type then
      throw "wasmssa.const: failed to verify that all of {value, result} have same type"

  | .extend => do
    let bitsToTake := (op.getProperties! ctx.raw WasmSSA.extend).bitsToTake.value
    let inputType := (op.getOperand! ctx.raw 0).getType! ctx.raw
    let .integerType intType := inputType.val | unreachable!
    if bitsToTake ≥ intType.bitwidth then
      throw s!"wasmssa.extend: trying to extend the {bitsToTake} low bits from a '{inputType}' value is illegal"

  | .func => do
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "wasmssa.func: requires one region"
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "wasmssa.func: requires zero operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "wasmssa.func: requires zero results"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw s!"wasmssa.func: requires 0 successors but found {op.getNumSuccessors ctx.raw opIn}"

  | .local => do
    op.verifyPlainOpCounts ctx opIn 0 1
    let localRefType := WasmSSA.LocalRefType.mk (op.getProperties! ctx.raw WasmSSA.local).type
    let expectedResultType := (Attribute.wasmssaLocalRefType localRefType).asType
    let actualResultType := (op.getResult 0).getType! ctx.raw
    if actualResultType ≠ expectedResultType then
      throw s!"wasmssa.local: expected result type to be '{expectedResultType}' but found '{actualResultType}'"
    unless #[WasmI32, WasmI64].contains localRefType.elementType.asType do
      throw s!"wasmssa.local: expected reference to signless 32-bit integer or signless 64-bit integer"

  | .return => do
    op.verifyTerminatorCounts ctx opIn 0
    if let some ⟨.func, _, props⟩ := op.getNthMatchingAncestorOpUnbounded? IsFunc ctx.raw 0 then
        let funcOutputType := props.function_type.outputs
        let opOperandCount := op.getNumOperands ctx.raw opIn
        if opOperandCount ≠ funcOutputType.size then
          throw s!"wasmssa.return: has {opOperandCount} operands, but enclosing function returns {funcOutputType.size}"
        op.verifyOperandTypesMatchTypeArray ctx 0 funcOutputType "wasmssa.return"

@[get_effects]
def WasmSSA.getEffects
    (op : WasmSSA) (_props : WasmSSA.propertiesOf op) : MemoryEffects :=
  match op with
  | .call => MemoryEffects.unknown
  | _ => .none

def WasmSSA.isConstantLike (op : WasmSSA) : Bool :=
  match op with
  | .const => true
  | _ => false

def WasmSSA.isCommutative (op : WasmSSA) : Bool :=
  match op with
  | _ => false

def WasmSSA.symbolInterface? (op : WasmSSA) : Option (SymbolOpInterface (WasmSSA.propertiesOf op)) :=
  match op with
  | .func => some { getSymName := fun props => some props.sym_name }
  | _ => none

def WasmSSA.verifyBody {OpInfo : Type} [IsOpCode OpInfo]
    (props : WasmSSAFuncProperties) (op : OperationPtr) (ctx : IRContext OpInfo) :
    Except String Unit := do
  if let some entryBlock := op.getRegion! ctx 0 |>.getFirstBlock! ctx then
    let entryBlockArgTypes := entryBlock.getArgumentTypes! ctx

    let functionInputTypes := props.function_type.inputs
    if functionInputTypes.size ≠ entryBlockArgTypes.size then
      throw s!"entry block should have same number of arguments as function type. \
        Function type has {functionInputTypes.size}, entry block has {entryBlockArgTypes.size}"

    for (entryBlockArgType, idx) in entryBlockArgTypes.zipIdx, functionInputType in functionInputTypes do
      if let Attribute.wasmssaLocalRefType refType := entryBlockArgType.val then
        if refType.elementType ≠ functionInputType then
          throw s!"func argument type #{idx} ({functionInputType}) doesn't match entry block referenced type ({refType.elementType})"
      else
        throw s!"entry block argument type should be LocalRefType, got {entryBlockArgType} for block argument {idx}"

def WasmSSA.functionInterface? (op : WasmSSA) : Option (FunctionOpInterface (WasmSSA.propertiesOf op)) :=
  match op with
  | .func =>
    some {
      getFunctionType := fun props => props.function_type
      setFunctionType := fun props functionType =>
          { props with function_type := functionType }
      verifyBody := WasmSSA.verifyBody
    }
  | _ => none

def WasmSSA.callOpInterface? (op : WasmSSA) : Option (CallOpInterface (WasmSSA.propertiesOf op)) :=
  match op with
  | .call =>
    some {
        getCallableForCallee? := fun props _ => some (CallInterfaceCallable.symbol props.callee)
        getArgOperands := fun _ args => args
    }
  | _ => none

def WasmSSA.branchOpInterface? (op : WasmSSA) : Option (BranchOpInterface (WasmSSA.propertiesOf op)) :=
  match op with
  | _ => none

def WasmSSA.unconditionalBranch? (op : WasmSSA) (props : WasmSSA.propertiesOf op) : Option (OpKind WasmSSA) :=
  match op with
  | _ => none

def WasmSSA.hasSSADominance (_op : WasmSSA) (_index : Nat) : Bool :=
  true

@[is_terminator]
def WasmSSA.isTerminator (op : WasmSSA) : Bool :=
  match op with
  | .block | .block_return | .branch_if | .if | .loop | .return => true
  | _ => false

def WasmSSA.isIsolatedFromAbove (op : WasmSSA) : Bool :=
  match op with
  | .func => true
  | _ => false

instance : HasOpInfo WasmSSA where
  verifyLocalInvariants := WasmSSA.verifyLocalInvariants
  getEffects := WasmSSA.getEffects
  isConstantLike := WasmSSA.isConstantLike
  isCommutative := WasmSSA.isCommutative
  symbolInterface? := WasmSSA.symbolInterface?
  functionInterface? := WasmSSA.functionInterface?
  callOpInterface? := WasmSSA.callOpInterface?
  branchOpInterface? := WasmSSA.branchOpInterface?
  unconditionalBranch? := WasmSSA.unconditionalBranch?
  hasSSADominance := WasmSSA.hasSSADominance
  isTerminator := WasmSSA.isTerminator
  isIsolatedFromAbove := WasmSSA.isIsolatedFromAbove

end

end Veir
