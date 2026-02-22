import Veir.Parser.Parser
import Veir.Parser.AttrParser
import Veir.IR.Basic
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSetInBounds

open Veir.Parser.Lexer
open Veir.Parser
open Veir.AttrParser

namespace Veir.Parser

structure MlirParserState where
  /-- The current IR context. -/
  ctx : IRContext
  hctx : ctx.FieldsInBounds
  /-- The values that have been defined at that point in the parser. -/
  values : Std.HashMap ByteArray ValuePtr
  /--
    The blocks that have been already parsed.
    The Bool value indicates whether the block has already been parsed
    (true), or has been forward declared (false).
  -/
  blocks : Std.HashMap ByteArray (BlockPtr × Bool)

def MlirParserState.fromContext (ctx : IRContext) (hctx : ctx.FieldsInBounds := by grind) : MlirParserState :=
  {ctx := ctx, hctx, values := Std.HashMap.emptyWithCapacity 128, blocks := Std.HashMap.emptyWithCapacity 1}

abbrev MlirParserM := StateT MlirParserState (EStateM String ParserState)

/--
  Execute the action with the given initial state.
  Returns the result along with the final state, or an error message.
-/
def MlirParserM.run (self : MlirParserM α)
  (mlirParserState : MlirParserState) (parserState: ParserState) : Except String (α × MlirParserState × ParserState) :=
  match (StateT.run self mlirParserState).run parserState with
  | .ok (a, mlirParserState) parserState => .ok (a, mlirParserState, parserState)
  | .error err _ => .error err

/--
  Execute the action with the given initial state.
  Returns the result or an error message.
-/
def MlirParserM.run' (self : MlirParserM α)
  (mlirParserState : MlirParserState) (parserState: ParserState) : Except String α :=
  match self.run mlirParserState parserState with
  | .ok (a, _, _) => .ok a
  | .error err => .error err

/--
  Get the current IR context that is stored in the parser state.
-/
def getContext : MlirParserM {ctx : IRContext // ctx.FieldsInBounds} := do
  let st ← get
  return ⟨st.ctx, st.hctx⟩

/--
  Get a value that has previously been parsed given its name.
-/
def getValue? (name : ByteArray) : MlirParserM (Option ValuePtr) := do
  return (← get).values[name]?

/--
  Get the original input that is being parsed.
-/
def getInput : MlirParserM ByteArray := do
  return (← getThe ParserState).input

/--
  Register a parsed value with the given name.
  This is used to keep track of values that have been defined during parsing.
-/
def registerValueDef (name : ByteArray) (value : ValuePtr) : MlirParserM Unit := do
  modify fun s => { s with values := s.values.insert name value }

/--
  Set the current IR context.
  This should be called whenever any modifications have been made to the context
  outside of the parser monad.
-/
def setContext (ctx : IRContext) (hctx : ctx.FieldsInBounds := by grind) : MlirParserM Unit := do
  modify fun s => {s with ctx, hctx}

set_option warn.sorry false in
/--
  Create a block at the given insert point and register its name in the parsing context.
  If a block was already declared with the given name, use that block instead, and
  insert it at the given insert point.
-/
def defineBlock (name : ByteArray) (ip : BlockInsertPoint) : MlirParserM BlockPtr := do
  let state ← get
  match state.blocks[name]? with
  | some (block, true) => -- Block of this name is already defined.
    throw s!"block %{String.fromUTF8! name} has already been defined"
  | some (block, false) => -- Block of this name was forward declared.
    /- Insert the block at the given location. -/
    let ⟨ctx, h_ctx_FieldsInBound⟩ ← getContext
    match hctx' : Rewriter.insertBlock? ctx block ip (by sorry) (by sorry) h_ctx_FieldsInBound with
    | none => throw "internal error: failed to insert block"
    | some ctx' =>
      setContext ctx'
    /- Notify the parsing context that the block is defined. -/
    modifyThe MlirParserState (fun state =>
    {state with
      blocks :=
        state.blocks.insert name (block, true)})
    return block
  | none => -- Block has not yet been declared or referenced.
    /- Create the block. -/
    let ⟨ctx, h_ctx_FieldsInBound⟩ ← getContext
    match hctx' : Rewriter.createBlock ctx ip h_ctx_FieldsInBound (by sorry) with
    | none => throw "internal error: failed to create block"
    | some (ctx', block) =>
      setContext ctx
      /- Notify the parsing context that the block is defined. -/
      modifyThe MlirParserState fun s =>
      {s with blocks := s.blocks.insert name (block, true)}
      return block

set_option warn.sorry false in
/--
  Forward declare a block with the given name.
  If the block was already forward declared or defined, return the existing block.
  Otherwise, create a new block without inserting it in a region.
-/
def defineBlockUse (name : ByteArray) : MlirParserM BlockPtr := do
  let state ← get
  match state.blocks[name]? with
  | some (block, _) => -- Block already defined or forward declared
    return block
  | none => -- Block not yet encountered
    /- Create the block. -/
    let ⟨ctx, h_ctx_FieldsInBound⟩ ← getContext
    match hctx' : Rewriter.createBlock ctx none h_ctx_FieldsInBound (by sorry) with
    | none => throw "internal error: failed to create block"
    | some (ctx', block) =>
      setContext ctx
      /- Notify the parsing context that the block is forward declared. -/
      modifyThe MlirParserState fun s =>
      {s with blocks := s.blocks.insert name (block, false)}
      return block

/--
  Parse an operation result.
-/
def parseOpResult : MlirParserM ByteArray := do
  let nameToken ← parseToken .percentIdent "operation result expected"
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  return slice.of (← getInput)

/--
  Parse the results before an operation definition,
  either as a list of values followed by '=', or nothing.
-/
def parseOpResults : MlirParserM (Array ByteArray) := do
  let .percentIdent := (← peekToken).kind | return #[]
  let results ← parseList parseOpResult
  parsePunctuation "=" "'=' expected after operation results"
  return results

/--
  An operand whose type has not yet been resolved.
  This is used during parsing to allow parsing operands before their types.
  Once the operation type is known, `resolveOperand` can be used to create an SSA value and
  check that the type matches with previous uses.
-/
structure UnresolvedOperand where
  name : ByteArray

/--
  Parse an operation operand.
-/
def parseOperand : MlirParserM UnresolvedOperand := do
  let nameToken ← parseToken .percentIdent "operand expected"
  return UnresolvedOperand.mk ({ nameToken.slice with start := nameToken.slice.start + 1 }.of (← getInput))

/--
  Parse a list of operation operands delimited by parentheses.
-/
def parseOperands : MlirParserM (Array UnresolvedOperand) := do
  parseDelimitedList .paren parseOperand

/--
  Parse a list of block operands delimited by square brackets, if present.
-/
def parseBlockOperand : MlirParserM BlockPtr := do
  let labelToken ← parseToken .caretIdent "block name expected"
  let slice := { labelToken.slice with start := labelToken.slice.start + 1 } -- skip ^ character
  let name := slice.of (← getInput)
  let block ← defineBlockUse name
  return block

/--
  Parse a single block operand.
-/
def parseBlockOperands : MlirParserM (Array BlockPtr) := do
  return (← parseOptionalDelimitedList .square parseBlockOperand).getD #[]

/--
  Resolve an operand to an SSA value of the expected type.
  Throw an error if the value is not defined or if the type does not match.
-/
def resolveOperand (operand : UnresolvedOperand) (expectedType : TypeAttr) : MlirParserM ValuePtr := do
  let some value := (← getValue? operand.name) | throw s!"use of undefined value %{String.fromUTF8! operand.name}"
  let parsedType := value.getType! (← getContext)
  if parsedType ≠ expectedType then
    throw s!"type mismatch for value %{String.fromUTF8! operand.name}: expected {expectedType}, got {parsedType}"
  return value

/--
  Parse a type, if present.
-/
def parseOptionalType : MlirParserM (Option TypeAttr) := do
  match AttrParser.parseOptionalType.run AttrParserState.mk (← getThe ParserState) with
  | .ok (ty, _, parserState) =>
    set parserState
    return ty
  | .error err => throw err

/--
  Parse a type, otherwise return an error.
-/
def parseType (errorMsg : String := "type expected") : MlirParserM TypeAttr := do
  match ← parseOptionalType with
  | some ty => return ty
  | none => throw errorMsg

/--
  Parse an operation type, consisting of a colon followed by a function type.
-/
def parseOperationType : MlirParserM (Array TypeAttr × Array TypeAttr) := do
  parsePunctuation ":"
  let inputs ← parseDelimitedList .paren parseType
  parsePunctuation "->"
  if (←peekToken).kind = .lParen then
    let outputs ← parseDelimitedList .paren parseType
    return (inputs, outputs)
  else
    let outputType ← parseType
    return (inputs, #[outputType])

/--
  Parse an SSA value followed by a colon and a type, if present.
-/
def parseTypedValue : MlirParserM (ByteArray × TypeAttr) := do
  let nameToken ← parseToken .percentIdent "value expected"
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)
  parsePunctuation ":"
  let ty ← parseType
  return (name, ty)

/--
  Parse the properties of an operation.
  Currently, these properties are not stored in the IR, but we still need to parse them to be able
  to parse valid MLIR syntax.
-/
def parseOpProperties (opCode : OpCode) : MlirParserM (propertiesOf opCode) := do
  if not (← parseOptionalPunctuation "<") then
    match Properties.fromAttrDict opCode {} with
    | .ok properties => return properties
    | .error err => throw err
  match AttrParser.parseAttributeDictionary.run AttrParserState.mk (← getThe ParserState) with
  | .ok (properties, _, parserState) =>
    set parserState
    parsePunctuation ">"
    match Properties.fromAttrDict opCode (.ofArray properties) with
    | .ok properties => return properties
    | .error err => throw err
  | .error err => throw err

/--
  Parse the attributes of an operation, if present.
  Currently, these attributes are not stored in the IR, but we still need to parse them to be able
  to parse valid MLIR syntax.
-/
def parseOpAttributes : MlirParserM DictionaryAttr := do
  match AttrParser.parseOptionalAttributeDictionary.run AttrParserState.mk (← getThe ParserState) with
  | .ok (attrs, _, parserState) =>
    set parserState
    match attrs with
    | none => return DictionaryAttr.empty
    | some attrs => return DictionaryAttr.fromArray attrs
  | .error err => throw err

set_option warn.sorry false in
/--
  Parse a block label, if present, and create and insert the block at the given insert point.
-/
def parseOptionalBlockLabel (ip : BlockInsertPoint) : MlirParserM (Option BlockPtr) := do
  /- Parse the block name. -/
  let some labelToken ← parseOptionalToken .caretIdent
    | return none
  let slice := { labelToken.slice with start := labelToken.slice.start + 1 } -- skip ^ character
  let name := slice.of (← getInput)
  /- Parse the arguments. -/
  let arguments := (← parseOptionalDelimitedList .paren parseTypedValue).getD #[]
  parsePunctuation ":" "':' expected after block label"
  /- Create the block or get it if it was forward declared. -/
  let block ← defineBlock name ip
  /- Insert block arguments in the block. -/
  let blockArguments := arguments.mapIdx (fun index (_, type) => BlockArgument.mk (ValueImpl.mk type none) index () block)
  let ⟨ctx, h_ctx_FieldsInBound⟩ ← getContext
  let h_block_InBounds : block.InBounds ctx := by sorry
  let ctx' := block.setArguments ctx blockArguments h_block_InBounds
  setContext ctx' (by
    show (block.setArguments ctx blockArguments h_block_InBounds).FieldsInBounds
    constructor
    · -- TODO(gzgz): why can't grind solve this?
      intro op opIn 
      constructor
      · intros res hres heq
        constructor
        · have hres_ctx : res.InBounds ctx := by
            rw [BlockPtr.setArguments_opResultPtr_mono] at hres; exact hres
          have h_maybe_ctx := OpResultPtr.firstUse!_inBounds h_ctx_FieldsInBound hres_ctx
          have h_get_eq : res.get (block.setArguments ctx blockArguments h_block_InBounds)
                            (by rw [BlockPtr.setArguments_opResultPtr_mono]; exact hres) =
                          res.get ctx hres_ctx := by
            simp [OpResultPtr.get, OperationPtr.get, BlockPtr.setArguments, BlockPtr.set]
          rw [h_get_eq]
          rw [OpResultPtr.get!_eq_get hres_ctx] at h_maybe_ctx
          intro z hz
          rw [BlockPtr.setArguments_opOperandPtr_mono h_block_InBounds (newArguments := blockArguments)]
          exact h_maybe_ctx z hz
        · -- owner_inBounds
          have hres_ctx : res.InBounds ctx := by
            rw [BlockPtr.setArguments_opResultPtr_mono] at hres; exact hres
          have h_owner_ctx := OpResultPtr.owner!_inBounds h_ctx_FieldsInBound hres_ctx
          simp only [OpResultPtr.get!_eq_get hres_ctx] at h_owner_ctx
          have h_get_eq : res.get (block.setArguments ctx blockArguments h_block_InBounds)
                            (by rw [BlockPtr.setArguments_opResultPtr_mono]; exact hres) =
                          res.get ctx hres_ctx := by
            simp [OpResultPtr.get, OperationPtr.get, BlockPtr.setArguments, BlockPtr.set]
          rw [h_get_eq]
          rw [BlockPtr.setArguments_operationPtr_mono h_block_InBounds (newArguments := blockArguments)]
          exact h_owner_ctx
      · -- prev_inBounds
        have opIn_ctx : op.InBounds ctx := by
          rw [BlockPtr.setArguments_operationPtr_mono] at opIn; exact opIn
        have h_prev_ctx := OperationPtr.prev!_inBounds h_ctx_FieldsInBound opIn_ctx
        simp only [OperationPtr.get!_eq_get opIn_ctx] at h_prev_ctx
        have h_get_eq : op.get (block.setArguments ctx blockArguments h_block_InBounds) opIn =
                        op.get ctx opIn_ctx := by
          simp [OperationPtr.get, BlockPtr.setArguments, BlockPtr.set]
        rw [h_get_eq]
        intro z hz
        rw [BlockPtr.setArguments_operationPtr_mono h_block_InBounds (newArguments := blockArguments)]
        exact h_prev_ctx z hz
      · -- next_inBounds
        have opIn_ctx : op.InBounds ctx := by
          rw [BlockPtr.setArguments_operationPtr_mono] at opIn; exact opIn
        have h_next_ctx := OperationPtr.next!_inBounds h_ctx_FieldsInBound opIn_ctx
        simp only [OperationPtr.get!_eq_get opIn_ctx] at h_next_ctx
        have h_get_eq : op.get (block.setArguments ctx blockArguments h_block_InBounds) opIn =
                        op.get ctx opIn_ctx := by
          simp [OperationPtr.get, BlockPtr.setArguments, BlockPtr.set]
        rw [h_get_eq]
        intro z hz
        rw [BlockPtr.setArguments_operationPtr_mono h_block_InBounds (newArguments := blockArguments)]
        exact h_next_ctx z hz
      · -- parent_inBounds
        have opIn_ctx : op.InBounds ctx := by
          rw [BlockPtr.setArguments_operationPtr_mono] at opIn; exact opIn
        have h_parent_ctx := OperationPtr.parent!_inBounds h_ctx_FieldsInBound opIn_ctx
        simp only [OperationPtr.get!_eq_get opIn_ctx] at h_parent_ctx
        have h_get_eq : op.get (block.setArguments ctx blockArguments h_block_InBounds) opIn =
                        op.get ctx opIn_ctx := by
          simp [OperationPtr.get, BlockPtr.setArguments, BlockPtr.set]
        rw [h_get_eq]
        intro z hz
        rw [BlockPtr.setArguments_blockPtr_mono h_block_InBounds (newArguments := blockArguments)]
        exact h_parent_ctx z hz
      · -- blockOperands_inBounds
        intro operand hoperand heq
        have opIn_ctx : op.InBounds ctx := by
          rw [BlockPtr.setArguments_operationPtr_mono] at opIn; exact opIn
        have hoperand_ctx : operand.InBounds ctx := by
          rw [BlockPtr.setArguments_blockOperandPtr_mono] at hoperand; exact hoperand
        have hFIB := h_ctx_FieldsInBound.operations_inBounds op opIn_ctx
        have h_blockoperand := hFIB.blockOperands_inBounds operand hoperand_ctx heq
        have h_get_eq : operand.get (block.setArguments ctx blockArguments h_block_InBounds) hoperand =
                        operand.get ctx hoperand_ctx := by
          simp [BlockOperandPtr.get, OperationPtr.get, BlockPtr.setArguments, BlockPtr.set]
        constructor
        · rw [h_get_eq]; intro z hz
          rw [BlockPtr.setArguments_blockOperandPtr_mono h_block_InBounds (newArguments := blockArguments)]
          exact h_blockoperand.nextUse_inBounds z hz
        · rw [h_get_eq]
          rw [BlockPtr.setArguments_blockOperandPtrPtr_mono h_block_InBounds (newArguments := blockArguments)]
          exact h_blockoperand.back_inBounds
        · rw [h_get_eq]
          rw [BlockPtr.setArguments_operationPtr_mono h_block_InBounds (newArguments := blockArguments)]
          exact h_blockoperand.owner_inBounds
        · rw [h_get_eq]
          rw [BlockPtr.setArguments_blockPtr_mono h_block_InBounds (newArguments := blockArguments)]
          exact h_blockoperand.value_inBounds
      · -- regions_inBounds
        intro i hi
        have opIn_ctx : op.InBounds ctx := by
          rw [BlockPtr.setArguments_operationPtr_mono] at opIn; exact opIn
        rw [BlockPtr.setArguments_regionPtr_mono h_block_InBounds (newArguments := blockArguments)]
        grind [OperationPtr.getRegion, OperationPtr.getNumRegions, OperationPtr.get,
               BlockPtr.setArguments, BlockPtr.set, IRContext.FieldsInBounds,
               Operation.FieldsInBounds]
      · -- operands_inBounds
        intro operand hoperand heq
        have opIn_ctx : op.InBounds ctx := by
          rw [BlockPtr.setArguments_operationPtr_mono] at opIn; exact opIn
        have hoperand_ctx : operand.InBounds ctx := by
          rw [BlockPtr.setArguments_opOperandPtr_mono] at hoperand; exact hoperand
        have hFIB := h_ctx_FieldsInBound.operations_inBounds op opIn_ctx
        have h_operand := hFIB.operands_inBounds operand hoperand_ctx heq
        have h_get_eq : operand.get (block.setArguments ctx blockArguments h_block_InBounds) hoperand =
                        operand.get ctx hoperand_ctx := by
          simp [OpOperandPtr.get, OperationPtr.get, BlockPtr.setArguments, BlockPtr.set]
        constructor
        · rw [h_get_eq]; intro z hz
          rw [BlockPtr.setArguments_opOperandPtr_mono h_block_InBounds (newArguments := blockArguments)]
          exact h_operand.nextUse_inBounds z hz
        · rw [h_get_eq]; sorry -- back_inBounds depends on BlockArgumentPtr properties
        · rw [h_get_eq]
          rw [BlockPtr.setArguments_operationPtr_mono h_block_InBounds (newArguments := blockArguments)]
          exact h_operand.owner_inBounds
        · rw [h_get_eq]; sorry -- value_inBounds depends on BlockArgumentPtr properties
    · sorry -- blocks_inBounds (block related)
    · -- regions_inBounds for IRContext
      intro region regionIn
      have regionIn_ctx : region.InBounds ctx := by
        rw [BlockPtr.setArguments_regionPtr_mono] at regionIn; exact regionIn
      have hFIB := h_ctx_FieldsInBound.regions_inBounds region regionIn_ctx
      have h_get_eq : region.get (block.setArguments ctx blockArguments h_block_InBounds) regionIn =
                      region.get ctx regionIn_ctx := by
        simp [RegionPtr.get, BlockPtr.setArguments, BlockPtr.set]
      rw [h_get_eq]
      constructor
      · intro blk hblk
        rw [BlockPtr.setArguments_blockPtr_mono h_block_InBounds (newArguments := blockArguments)]
        exact hFIB.firstBlock_inBounds blk hblk
      · intro blk hblk
        rw [BlockPtr.setArguments_blockPtr_mono h_block_InBounds (newArguments := blockArguments)]
        exact hFIB.lastBlock_inBounds blk hblk
      · intro parent hparent
        rw [BlockPtr.setArguments_operationPtr_mono h_block_InBounds (newArguments := blockArguments)]
        exact hFIB.parent_inBounds parent hparent
    )
  /- Register the block argument names in the parser state. -/
  for ((argName, argType), index) in arguments.zipIdx do
    registerValueDef argName (ValuePtr.blockArgument {block := block, index := index})
  return some block

/--
  Parse the label of an entry block and create and insert the block at the given insert point.
  Since the entry block does not need a label, if no label is found,
  a block with an empty name is created and returned.
-/
def parseEntryBlockLabel (ip : BlockInsertPoint) : MlirParserM BlockPtr := do
  /- Try to parse a block label. -/
  if let some block ← parseOptionalBlockLabel ip then
    return block
  else -- Otherwise, create a block with an empty name.
    let block ← defineBlock ByteArray.empty ip
    return block

set_option warn.sorry false in
mutual

/--
  Parse the regions of an operation.
-/
partial def parseOpRegions : MlirParserM (Array RegionPtr) := do
  return (← parseOptionalDelimitedList .paren parseRegion).getD #[]

/--
  Parse an operation, if present, and insert it at the given insert point.
-/
partial def parseOptionalOp (ip : Option InsertPoint) : MlirParserM (Option OperationPtr) := do
  /- Parse the operation. -/
  let results ← parseOpResults
  let some opName ← parseOptionalStringLiteral | return none
  let operands ← parseOperands
  let blockOperands ← parseBlockOperands

  /- Get the operation opcode. -/
  let opId := OpCode.fromName opName.toByteArray

  let properties ← parseOpProperties opId
  let regions ← parseOpRegions
  let attrs ← parseOpAttributes
  let (inputTypes, outputTypes) ← parseOperationType

  /- Check that the number of results matches with the operation type. -/
  if outputTypes.size ≠ results.size then
    throw s!"operation '{opName}' declares {outputTypes.size} result types, but {results.size} result names were provided"

  /- Check that the number and types of operands matches with the operation type. -/
  if inputTypes.size ≠ operands.size then
    throw s!"operation '{opName}' declares {inputTypes.size} operand types, but {operands.size} operands were provided"
  let operands ← operands.zip inputTypes |>.mapM (fun (operand, type) => resolveOperand operand type)

  /- Set context in monad to default to preserve linearity whilst modifying -/
  let ⟨ctx, h_ctx_FieldsInBound⟩ ← getContext
  setContext Inhabited.default (by
    -- TODO(gzgz): extract into a separate theorem about `default` being
    -- `FieldsInBound`
    simp [default, instInhabitedIRContext.default]
    constructor <;> simp [OperationPtr.InBounds, BlockPtr.InBounds, RegionPtr.InBounds])

  match hctx' : Rewriter.createOp ctx opId outputTypes operands blockOperands regions properties ip (by sorry) (by sorry) (by sorry) (by sorry) h_ctx_FieldsInBound with
  | none => throw "internal error: failed to create operation"
  | some (ctx', op) =>
    let ctx'' := op.setAttributes ctx' attrs (by sorry)

    /- Update the parser context. -/
    setContext ctx''

    /- Register the new operation results in the parser state. -/
    for index in 0...(op.getNumResults! ctx') do
      let resultValue := op.getResult index
      registerValueDef results[index]! resultValue
    return op

/--
  Parse an operation.
-/
partial def parseOp (ip : Option InsertPoint) : MlirParserM OperationPtr := do
  let some op ← parseOptionalOp ip | throw "operation expected"
  return op

/--
  Parse a region.
-/
partial def parseRegion : MlirParserM RegionPtr := do
  /- Reset the block parsing state, as blocks are local to regions. -/
  let oldBlocks := (← getThe MlirParserState).blocks
  modifyThe MlirParserState fun s => {s with blocks := Std.HashMap.emptyWithCapacity 1}

  /- Create the region and parse the open delimiter. -/
  parsePunctuation "{"
  let ctx := ← getContext
  match hctx' : Rewriter.createRegion ctx with
  | none => throw "internal error: failed to create region"
  | some (ctx', region) =>
    setContext ctx'

    /- Case where there are no blocks inside the region. -/
    if (← parseOptionalPunctuation "}") then
      return region

    /- Parse the first block separately, as it may not have a label. -/
    let _ ← parseEntryBlock (BlockInsertPoint.atEnd region)
    /- Parse the following blocks. -/
    while true do
      if (← parseOptionalBlock (BlockInsertPoint.atEnd region)) = none then
        break

    /- Parse the closing delimiter. -/
    parsePunctuation "}"

    /- Check that all blocks in the regions that were forward declared were parsed. -/
    for (blockName, (_, parsed)) in (← getThe MlirParserState).blocks do
      if !parsed then
        throw s!"block %{String.fromUTF8! blockName} was declared but not defined"

    /- Restore the previous block parsing state. -/
    modifyThe MlirParserState fun s => {s with blocks := oldBlocks}
    return region

/--
  Parse the entry block and insert it into the given region.
  Compared to a normal block, the entry block does not need a label.
-/
partial def parseEntryBlock (ip : BlockInsertPoint) : MlirParserM BlockPtr := do
  let block ← parseEntryBlockLabel ip
  while true do
    if (← parseOptionalOp (InsertPoint.atEnd block)) = none then
      break
  return block

/--
  Parse a block and insert it at the given block insert point.
-/
partial def parseOptionalBlock (ip : BlockInsertPoint) : MlirParserM (Option BlockPtr) := do
  let some block ← parseOptionalBlockLabel ip
    | return none
  while true do
    if (← parseOptionalOp (InsertPoint.atEnd block)) == none then
      break
  return block

end

end Veir.Parser
