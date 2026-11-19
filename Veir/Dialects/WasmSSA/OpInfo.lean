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
-- | local
-- | local_get
-- | local_set
-- | local_tee
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
-- | wrap
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
  | .xor => expectNoProperties "wasmssa" attrDict

def WasmSSA.toAttrDict
    (op : WasmSSA) (props : WasmSSA.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .branch_if | .call | .const | .extend | .func => props.toAttrDict
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

inductive WasmSSAOperationType where
  /-- Has a fixed set of possible input and output types -/
  | fixed (cases : Array (Array TypeAttr × Array TypeAttr))
  /-- Requires special handling -/
  | special

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
  | .eqz =>
    .fixed #[(#[WasmI32], #[WasmI32]), (#[WasmI64], #[WasmI32])]
  | .const =>
    .fixed #[(#[], #[WasmI32]), (#[], #[WasmI64])]
  | .select =>
    .fixed #[(#[WasmI32, WasmI32, WasmI32], #[WasmI32]), (#[WasmI64, WasmI64, WasmI32], #[WasmI64])]
  | .block | .loop | .if | .block_return | .branch_if | .call | .func | .return =>
    .special

@[expose]
def WasmSSA.verifyLocalInvariants
    {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo WasmSSA]
    (opType : WasmSSA)
    (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw)
    : Except String PUnit := do
  let ty := op.getOpType ctx.raw opIn
  dbg_trace s!"Op `{(String.fromUTF8? opType.name).or ("unknown")}` with {(op.getOperands ctx.raw opIn).size} \
    operands, {(op.getResults ctx.raw opIn).size} results, \
    {(IsOpCode.toAttrDict ty (op.getProperties ctx.raw ty)).size} properties, \
    {(op.getAttributes ctx.raw opIn).entries.size} attributes, \
    {(op.getRegions ctx.raw opIn).size} regions, \
    {(op.getSuccessors ctx.raw opIn).size} successors"

  if let .fixed expectedTypes := getExpectedTypes opType then
    let opTypes := (op.getOperandTypes ctx.raw opIn, op.getResultTypes ctx.raw opIn)
    if ! expectedTypes.contains opTypes then
      let expectedTypeString := expectedTypes.map (fun (operands, results) => s!"({operands}) -> ({results})")
      throw s!"expected to have one of the following types: {expectedTypeString}; \
        but found type ({opTypes.fst}) -> ({opTypes.snd}) instead"

  match opType with
  | .add    | .eq           | .ge_ui | .lt_ui  | .rem_ui | .shr_u
  | .and    | .eqz          | .gt_si | .mul    | .rotl   | .sub
  | .clz    | .extend       | .gt_ui | .ne     | .rotr   | .xor
  | .ctz    | .extend_i32_s | .le_si | .or     | .select
  | .div_si | .extend_i32_u | .le_ui | .popcnt | .shl
  | .div_ui | .ge_si        | .lt_si | .rem_si | .shr_s => do
    op.verifyNonOperandCounts ctx opIn 1 0 0

  | .block | .loop | .if => do
    let opName := String.fromUTF8! opType.name
    if opType = .if then
      if op.getNumOperands! ctx.raw ≠ 1 then
        throw "wasmssa.if: Expected 'condition' operand"
      else
        if ((op.getOperand! ctx.raw 0).getType! ctx.raw).val ≠ WasmI32 then
          throw "wasmssa.if: Expected 'condition' to be a 32-bit signless integer"
    else
      if op.getNumOperands! ctx.raw ≠ 0 then
        throw s!"{opName}: Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw s!"{opName}: Expected 0 results"
    if op.getNumSuccessors ctx.raw opIn ≠ 1 then
      throw s!"{opName}: Expected 1 successor 'target' block"
    let expectedRegions := if opType = .if then 2 else 1
    if op.getNumRegions ctx.raw opIn ≠ expectedRegions then
      throw s!"{opName}: Expected {expectedRegions} region(s)"
    let operandOffset := if opType = .if then 1 else 0

    let some entry := (op.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
      | throw s!"{opName}: Expected a non-empty region"
    if entry.getNumArguments! ctx.raw + operandOffset ≠ op.getNumOperands ctx.raw opIn then
      throw s!"{opName}: Expected {entry.getNumArguments! ctx.raw + 1} operand(s) \
      to match the nested block's arguments (including 'condition'), got {op.getNumOperands ctx.raw opIn} operands instead"
    op.verifyOperandTypesMatchTypeArray ctx operandOffset ((entry.getArgumentTypes! ctx.raw).map (·.val)) s!"{opName}: region entry block"

    if opType = .if then
      if let some secondEntry := (op.getRegion! ctx.raw 0).getFirstBlock! ctx.raw then
        if secondEntry.getNumArguments! ctx.raw + operandOffset ≠ op.getNumOperands ctx.raw opIn then
          throw s!"{opName}: Expected {secondEntry.getNumArguments! ctx.raw + 1} operand(s) \
          to match the nested block's arguments (including 'condition'), got {op.getNumOperands ctx.raw opIn} operands instead"
        op.verifyOperandTypesMatchTypeArray ctx operandOffset ((secondEntry.getArgumentTypes! ctx.raw).map (·.val)) s!"{opName}: region entry block"

  | .block_return => do
    op.verifyTerminatorCounts ctx opIn 0
    let some labelLevelParentOp := op.getNthAncestorOpInMatchingChain? LabelLevelOp ctx.raw 0
      | throw "wasmssa.block_return: Expected to be nested in a LabelLevelOp ('wasmssa.block', 'wasmssa.if', 'wasmssa.loop')"
    if labelLevelParentOp.op.getNumSuccessors! ctx.raw ≠ 1 then
      throw "wasmssa.block_return: Expected the enclosing LavelLevelOp to have 1 successor"
    let target := labelLevelParentOp.op.getSuccessor! ctx.raw 0
    if op.getNumOperands ctx.raw opIn ≠ target.getNumArguments! ctx.raw then
      throw s!"wasmssa.block_return: Expected {target.getNumArguments! ctx.raw} operand(s) \
        to match the target's arguments, got {op.getNumOperands ctx.raw opIn} operands instead"
    op.verifyOperandTypesMatchTypeArray ctx 0 ((target.getArgumentTypes! ctx.raw).map (·.val)) "wasmssa.block_return: target"

  | .branch_if => do
    op.verifyTerminatorCounts ctx opIn 1
    -- We know from WasmSSABranchIfProperties.fromAttrDict that it is a non-negative integer
    let expectedNesting := (op.getProperties! ctx.raw WasmSSA.branch_if).exitLevel.value.natAbs
    let some frameOp := op.getNthAncestorOpInMatchingChain? LabelLevelOp ctx.raw expectedNesting
      | throw s!"wasmssa.branch_if: Expected to be nested {expectedNesting}-deep in LabelLevelOps (`wasmssa.block`, `wasmssa.if`, `wasmssa.loop`)"
    -- The branch target is the successor in the case of `if` or `block`,
    -- but the body in the case of `loop`.
    let target : BlockPtr ← match frameOp with
      | ⟨.block, frameOp, props⟩
      | ⟨.if, frameOp, props⟩ =>
        if frameOp.getNumSuccessors! ctx.raw ≠ 1 then
          throw "wasmssa.branch_if: Expected the targetted LabelLevelOp to have 1 successor"
        else
          pure (frameOp.getSuccessor! ctx.raw 0)
      | ⟨.loop, loopOp, props⟩ =>
        if loopOp.getNumRegions! ctx.raw ≠ 1 then
          throw "wasmssa.branch_if: expected targetted `loop` to have 1 region"
        else
          let some target := (loopOp.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
            | throw "wasmssa.branch_if: expected targetted `loop` to have a nonempty region"
          pure target
    if op.getNumOperands ctx.raw opIn ≠ target.getNumArguments! ctx.raw + 1 then
      throw s!"wasmssa.branch_if: Expected {target.getNumArguments! ctx.raw + 1} operand(s) \
        to match the target's arguments (including 'conditioin'), got {op.getNumOperands ctx.raw opIn} operands instead"
    if (op.getOperand! ctx.raw 0).getType! ctx.raw ≠ WasmI32 then
      throw "wasmssa.branch_if: expected 'condition' to be a signless 32-bit integer"
    op.verifyOperandTypesMatchTypeArray ctx 1 ((target.getArgumentTypes! ctx.raw).map (·.val)) "wasmssa.branch_if: target"

  | .call => do
    -- Upstream wasmssa doesn't seem to bother checking whether calls
    -- match callee signatures, and it's non-obvious how to do that
    -- efficiently in VeIR, so skipping for now.
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
    if let some ⟨.func, ancestor, props⟩ := op.getNthMatchingAncestorOpUnbounded? IsFunc ctx.raw 0 then
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
  | .const => true
  | _ => false

def WasmSSA.isCommutative (op : WasmSSA) : Bool :=
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
