module

public import Veir.IR.Basic
import all Veir.IR.Basic

/-!
Operations that deallocate, allocate, and set fields of elements contained in an `IRContext`.

These operations are not safe to use in general, as they do not always maintain the structural
invariants of the `IRContext`. They should only be used as building blocks for operations
that maintain the invariants defined in `WellFormed.lean`.
-/

public section

namespace Veir

variable {OpInfo : Type} [IsOpCode OpInfo]
variable {Dialect : Type} [IsOpCode Dialect] [HasDialect OpInfo Dialect]
variable {ctx ctx' : IRContext OpInfo}

attribute [local grind] OperationPtr.InBounds OpOperandPtr.InBounds BlockOperandPtr.InBounds
  OpResultPtr.InBounds BlockArgumentPtr.InBounds BlockOperandPtrPtr.InBounds

namespace OperationPtr

def set (ptr : OperationPtr) (ctx : IRContext OpInfo) (newOp : Operation OpInfo) : IRContext OpInfo :=
  {ctx with operations := ctx.operations.insert ptr newOp}

def setNextOp (op : OperationPtr) (ctx : IRContext OpInfo) (newNext : Option OperationPtr)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOp := op.get ctx
  op.set ctx { oldOp with next := newNext}

def setNextOp! (op : OperationPtr) (ctx : IRContext OpInfo) (newNext : Option OperationPtr) : IRContext OpInfo :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with next := newNext}

@[grind =_, eq_bang ←]
theorem setNextOp!_eq_setNextOp {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.setNextOp! ctx newNext = op.setNextOp ctx newNext inBounds := by
  grind [setNextOp, setNextOp!]

def setPrevOp (op : OperationPtr) (ctx : IRContext OpInfo) (newPrev : Option OperationPtr)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with prev := newPrev}

def setPrevOp! (op : OperationPtr) (ctx : IRContext OpInfo) (newPrev : Option OperationPtr) : IRContext OpInfo :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with prev := newPrev}

@[grind =_, eq_bang ←]
theorem setPrevOp!_eq_setPrevOp {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.setPrevOp! ctx newPrev = op.setPrevOp ctx newPrev inBounds := by
  grind [setPrevOp, setPrevOp!]

def setParent (op : OperationPtr) (ctx : IRContext OpInfo) (newParent : Option BlockPtr)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with parent := newParent}

def setParent! (op : OperationPtr) (ctx : IRContext OpInfo) (newParent : Option BlockPtr) : IRContext OpInfo :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with parent := newParent}

@[grind =_, eq_bang ←]
theorem setParent!_eq_setParent {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.setParent! ctx newParent = op.setParent ctx newParent inBounds := by
  grind [setParent, setParent!]

def setRegions (op : OperationPtr) (ctx : IRContext OpInfo) (newRegions : Array RegionPtr)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with regions := newRegions}

def setRegions! (op : OperationPtr) (ctx : IRContext OpInfo) (newRegions : Array RegionPtr) : IRContext OpInfo :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with regions := newRegions}

@[grind =_, eq_bang ←]
theorem setRegions!_eq_setRegions {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.setRegions! ctx newRegions = op.setRegions ctx newRegions inBounds := by
  grind [setRegions, setRegions!]

def pushRegion (op : OperationPtr) (ctx : IRContext OpInfo) (reg : RegionPtr)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  op.setRegions ctx ((op.get ctx).regions.push reg)

def pushRegion! (op : OperationPtr) (ctx : IRContext OpInfo) (reg : RegionPtr) :=
  op.setRegions! ctx ((op.get! ctx).regions.push reg)

@[grind =_, eq_bang ←]
theorem pushRegion!_eq_pushRegion {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.pushRegion! ctx reg = op.pushRegion ctx reg inBounds := by
  grind [pushRegion!, pushRegion]

def setResults (op : OperationPtr) (ctx : IRContext OpInfo) (newResults : Array OpResult)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with results := newResults}

def setResults! (op : OperationPtr) (ctx : IRContext OpInfo) (newResults : Array OpResult) : IRContext OpInfo :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with results := newResults}

@[grind =_, eq_bang ←]
theorem setResults!_eq_setResults {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.setResults! ctx newResults = op.setResults ctx newResults inBounds := by
  grind [setResults, setResults!]

def pushResult (op : OperationPtr) (ctx : IRContext OpInfo) (resultS : OpResult)
      (hop : op.InBounds ctx := by grind) :=
    op.setResults ctx ((op.get ctx).results.push resultS)

def pushResult! (op : OperationPtr) (ctx : IRContext OpInfo) (resultS : OpResult) : IRContext OpInfo :=
  op.setResults! ctx ((op.get! ctx).results.push resultS)

@[grind =_, eq_bang ←]
theorem pushResult!_eq_pushResult {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.pushResult! ctx resultS = op.pushResult ctx resultS inBounds := by
  grind [pushResult, pushResult!]

def setBlockOperands (op : OperationPtr) (ctx : IRContext OpInfo) (newOperands : Array BlockOperand)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOp := op.get ctx (by grind)
  op.set ctx {oldOp with blockOperands := newOperands}

def setBlockOperands! (op : OperationPtr) (ctx : IRContext OpInfo) (newOperands : Array BlockOperand) :
    IRContext OpInfo :=
  let oldOp := op.get! ctx
  op.set ctx {oldOp with blockOperands := newOperands}

@[grind =_, eq_bang ←]
theorem setBlockOperands!_eq_setBlockOperands {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.setBlockOperands! ctx newOperands = op.setBlockOperands ctx newOperands inBounds := by
  grind [setBlockOperands, setBlockOperands!]

def pushBlockOperand (op : OperationPtr) (ctx : IRContext OpInfo) (operands : BlockOperand)
      (hop : op.InBounds ctx := by grind) :=
    op.setBlockOperands ctx ((op.get ctx).blockOperands.push operands)

def pushBlockOperand! (op : OperationPtr) (ctx : IRContext OpInfo) (operands : BlockOperand) :
    IRContext OpInfo :=
  op.setBlockOperands! ctx ((op.get! ctx).blockOperands.push operands)

@[grind =_, eq_bang ←]
theorem pushBlockOperand!_eq_pushBlockOperand
    {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.pushBlockOperand! ctx operands = op.pushBlockOperand ctx operands inBounds := by
  grind [pushBlockOperand, pushBlockOperand!]

def setOperands (op : OperationPtr) (ctx : IRContext OpInfo) (newOperands : Array OpOperand)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with operands := newOperands}

def setOperands! (op : OperationPtr) (ctx : IRContext OpInfo) (newOperands : Array OpOperand) : IRContext OpInfo :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with operands := newOperands}

@[grind =_, eq_bang ←]
theorem setOperands!_eq_setOperands {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.setOperands! ctx newOperands = op.setOperands ctx newOperands inBounds := by
  grind [setOperands, setOperands!]

def pushOperand (op : OperationPtr) (ctx : IRContext OpInfo) (operandS : OpOperand)
      (hop : op.InBounds ctx := by grind) :=
    op.setOperands ctx ((op.get ctx).operands.push operandS)

def pushOperand! (op : OperationPtr) (ctx : IRContext OpInfo) (operands : OpOperand) : IRContext OpInfo :=
  op.setOperands! ctx ((op.get! ctx).operands.push operands)

@[grind =_, eq_bang ←]
theorem pushOperand!_eq_pushOperand {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.pushOperand! ctx operands = op.pushOperand ctx operands inBounds := by
  grind [pushOperand, pushOperand!]

def setAttributes (op : OperationPtr) (ctx : IRContext OpInfo) (newAttrs : DictionaryAttr)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOp := op.get ctx
  op.set ctx { oldOp with attrs := newAttrs}

def setAttributes! (op : OperationPtr) (ctx : IRContext OpInfo) (newAttrs : DictionaryAttr) : IRContext OpInfo :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with attrs := newAttrs}

@[grind =_, eq_bang ←]
theorem setAttributes!_eq_setAttributes {op : OperationPtr} (inBounds : op.InBounds ctx) :
    op.setAttributes! ctx newAttrs = op.setAttributes ctx newAttrs inBounds := by
  grind [setAttributes, setAttributes!]

/--
Set the properties of an operation of type `opCode`.
The passed `opCode` can either be of the global `OpInfo` type, or the dialect-specific
`Dialect` type. The `OpInfo` version is often the one used when manipulating generic operations,
while the `Dialect` version is often easier to use when manipulating dialect-specific operations.
-/
def setProperties (op : OperationPtr) (ctx : IRContext OpInfo) (opCode : Dialect)
    (newProperties : propertiesOf opCode)
    (inBounds : op.InBounds ctx := by grind)
    (hprop : op.getOpType! ctx = opCode := by grind) : IRContext OpInfo :=
  have h : (op.get ctx inBounds).opType = opCode := by grind [getOpType!]
  let oldOp := op.get ctx (by grind)
  let newPropertiesGlobal := HasDialect.ofDialectProperties OpInfo opCode newProperties
  op.set ctx { oldOp with properties := h ▸ newPropertiesGlobal }

/--
Set the properties of an operation of type `opCode`.
The implicitely passed `opCode` can either be of the global `OpInfo` type, or the dialect-specific
`Dialect` type. The `OpInfo` version is often the one used when manipulating generic operations,
while the `Dialect` version is often easier to use when manipulating dialect-specific operations.

This function panics if the given operation is not in bounds.
-/
def setProperties! {opCode : Dialect} (op : OperationPtr) (ctx : IRContext OpInfo)
  (newProperties : propertiesOf opCode)
  (hprop : op.getOpType! ctx = opCode := by grind) : IRContext OpInfo :=
  have h : (op.get! ctx).opType = opCode := by grind [getOpType!]
  let oldOp := op.get! ctx
  let newPropertiesGlobal := HasDialect.ofDialectProperties OpInfo opCode newProperties
  op.set ctx { oldOp with properties := h ▸ newPropertiesGlobal }

@[grind =_, eq_bang ←]
theorem setProperties!_eq_setProperties {op : OperationPtr} {opCode : Dialect}
    (newProperties : propertiesOf opCode) (inBounds : op.InBounds ctx)
    (hprop : op.getOpType! ctx = opCode) :
    op.setProperties! ctx newProperties =
    op.setProperties ctx opCode newProperties inBounds := by
  grind [setProperties, setProperties!]

def allocEmpty {Dialect : Type} [IsOpCode Dialect] [HasDialect OpInfo Dialect]
    (ctx : IRContext OpInfo) (opType : Dialect)
    (properties : propertiesOf opType) :
    Option (IRContext OpInfo × OperationPtr) :=
  let newOpPtr : OperationPtr := ⟨ctx.nextID⟩
  let globalProperties := HasDialect.ofDialectProperties OpInfo opType properties
  let operation := Operation.empty (opType : OpInfo) globalProperties
  if _ : ctx.operations.contains newOpPtr then none else
  let ctx := { ctx with nextID := ctx.nextID + 1 }
  let ctx := newOpPtr.set ctx operation
  (ctx, newOpPtr)

-- `inBounds` is unused as ExtHashMap does not require proof of key presence for `erase`.
-- We still keep it as an API consistency.
set_option linter.unusedVariables false in
def dealloc (op : OperationPtr) (ctx : IRContext OpInfo)
    (inBounds : op.InBounds ctx := by grind) : IRContext OpInfo :=
  { ctx with operations := ctx.operations.erase op }

end OperationPtr

namespace OpOperandPtr

def set (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newOperand : OpOperand)
    (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let op := operand.op.get ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        operands := op.operands.set operand.index newOperand (by grind)} }

def set! (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newOperand : OpOperand) : IRContext OpInfo :=
  let op := operand.op.get! ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        operands := op.operands.set! operand.index newOperand } }

@[grind =_, eq_bang ←]
theorem set!_eq_set {operand : OpOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.set! ctx newOperand = operand.set ctx newOperand inBounds := by
  grind [set, set!]

def setNextUse (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newNextUse : Option OpOperandPtr)
    (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with nextUse := newNextUse }

def setNextUse! (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newNextUse : Option OpOperandPtr) : IRContext OpInfo :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with nextUse := newNextUse }

@[grind =_, eq_bang ←]
theorem setNextUse!_eq_setNextUse {operand : OpOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.setNextUse! ctx newNextUse = operand.setNextUse ctx newNextUse inBounds := by
  grind [setNextUse, setNextUse!]

def setBack (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newBack : OpOperandPtrPtr)
    (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with back := newBack }

def setBack! (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newBack : OpOperandPtrPtr) : IRContext OpInfo :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with back := newBack }

@[grind =_, eq_bang ←]
theorem setBack!_eq_setBack {operand : OpOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.setBack! ctx newBack = operand.setBack ctx newBack inBounds := by
  grind [setBack, setBack!]

def setOwner (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newOwner : OperationPtr)
    (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with owner := newOwner }

def setOwner! (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newOwner : OperationPtr) : IRContext OpInfo :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with owner := newOwner }

@[grind =_, eq_bang ←]
theorem setOwner!_eq_setOwner {operand : OpOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.setOwner! ctx newOwner = operand.setOwner ctx newOwner inBounds := by
  grind [setOwner, setOwner!]

def setValue (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newValue : ValuePtr)
    (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with value := newValue }

def setValue! (operand : OpOperandPtr) (ctx : IRContext OpInfo) (newValue : ValuePtr) : IRContext OpInfo :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with value := newValue }

@[grind =_, eq_bang ←]
theorem setValue!_eq_setValue {operand : OpOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.setValue! ctx newValue = operand.setValue ctx newValue inBounds := by
  grind [setValue, setValue!]

end OpOperandPtr

namespace BlockOperandPtr

def set (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newOperand : BlockOperand) (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let op := operand.op.get ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        blockOperands := op.blockOperands.set operand.index newOperand (by grind)} }

def set! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newOperand : BlockOperand) : IRContext OpInfo :=
  let op := operand.op.get! ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        blockOperands := op.blockOperands.set! operand.index newOperand } }

@[grind =_, eq_bang ←]
theorem set!_eq_set {operand : BlockOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.set! ctx newOperand = operand.set ctx newOperand inBounds := by
  grind [set, set!]

def setNextUse (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newNextUse : Option BlockOperandPtr)
    (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with nextUse := newNextUse }

def setNextUse! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newNextUse : Option BlockOperandPtr) :
    IRContext OpInfo :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with nextUse := newNextUse }

@[grind =_, eq_bang ←]
theorem setNextUse!_eq_setNextUse {operand : BlockOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.setNextUse! ctx newNextUse = operand.setNextUse ctx newNextUse inBounds := by
  grind [setNextUse, setNextUse!]

def setBack (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newBack : BlockOperandPtrPtr)
    (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with back := newBack }

def setBack! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newBack : BlockOperandPtrPtr) : IRContext OpInfo :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with back := newBack }

@[grind =_, eq_bang ←]
theorem setBack!_eq_setBack {operand : BlockOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.setBack! ctx newBack = operand.setBack ctx newBack inBounds := by
  grind [setBack, setBack!]

def setOwner (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newOwner : OperationPtr)
    (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with owner := newOwner }

def setOwner! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newOwner : OperationPtr) : IRContext OpInfo :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with owner := newOwner }

@[grind =_, eq_bang ←]
theorem setOwner!_eq_setOwner {operand : BlockOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.setOwner! ctx newOwner = operand.setOwner ctx newOwner inBounds := by
  grind [setOwner, setOwner!]

def setValue (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newValue : BlockPtr)
    (operandIn : operand.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with value := newValue }

def setValue! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (newValue : BlockPtr) : IRContext OpInfo :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with value := newValue }

@[grind =_, eq_bang ←]
theorem setValue!_eq_setValue {operand : BlockOperandPtr} (inBounds : operand.InBounds ctx) :
    operand.setValue! ctx newValue = operand.setValue ctx newValue inBounds := by
  grind [setValue, setValue!]

end BlockOperandPtr

namespace OpResultPtr

def set (result : OpResultPtr) (ctx : IRContext OpInfo) (newresult : OpResult) (resultIn : result.InBounds ctx := by grind) : IRContext OpInfo :=
  let op := result.op.get ctx
  { ctx with
    operations := ctx.operations.insert result.op
      { op with results := op.results.set result.index newresult (by grind)} }

def set! (result : OpResultPtr) (ctx : IRContext OpInfo) (newresult : OpResult) : IRContext OpInfo :=
  let op := result.op.get! ctx
  { ctx with
    operations := ctx.operations.insert result.op
      { op with results := op.results.set! result.index newresult } }

@[grind =_, eq_bang ←]
theorem set!_eq_set {result : OpResultPtr} (inBounds : result.InBounds ctx) :
    result.set! ctx newresult = result.set ctx newresult inBounds := by
  grind [set, set!]

def setType (result : OpResultPtr) (ctx : IRContext OpInfo) (newType : TypeAttr)
    (resultIn : result.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldResult := result.get ctx
  result.set ctx { oldResult with type := newType }

def setType! (result : OpResultPtr) (ctx : IRContext OpInfo) (newType : TypeAttr) : IRContext OpInfo :=
  let oldResult := result.get! ctx
  result.set! ctx { oldResult with type := newType }

@[grind =_, eq_bang ←]
theorem setType!_eq_setType {result : OpResultPtr} (inBounds : result.InBounds ctx) :
    result.setType! ctx newType = result.setType ctx newType inBounds := by
  grind [setType, setType!]

def setFirstUse (result : OpResultPtr) (ctx : IRContext OpInfo) (newFirstUse : Option OpOperandPtr)
    (resultIn : result.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldResult := result.get ctx
  result.set ctx { oldResult with firstUse := newFirstUse }

def setFirstUse! (result : OpResultPtr) (ctx : IRContext OpInfo) (newFirstUse : Option OpOperandPtr) : IRContext OpInfo :=
  let oldResult := result.get! ctx
  result.set! ctx { oldResult with firstUse := newFirstUse }

@[grind =_, eq_bang ←]
theorem setFirstUse!_eq_setFirstUse {result : OpResultPtr} (inBounds : result.InBounds ctx) :
    result.setFirstUse! ctx newFirstUse = result.setFirstUse ctx newFirstUse inBounds := by
  grind [setFirstUse, setFirstUse!]

def setOwner (result : OpResultPtr) (ctx : IRContext OpInfo) (newOwner : OperationPtr)
    (resultIn : result.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldResult := result.get ctx
  result.set ctx { oldResult with owner := newOwner }

def setOwner! (result : OpResultPtr) (ctx : IRContext OpInfo) (newOwner : OperationPtr) : IRContext OpInfo :=
  let oldResult := result.get! ctx
  result.set! ctx { oldResult with owner := newOwner }

@[grind =_, eq_bang ←]
theorem setOwner!_eq_setOwner {result : OpResultPtr} (inBounds : result.InBounds ctx) :
    result.setOwner! ctx newOwner = result.setOwner ctx newOwner inBounds := by
  grind [setOwner, setOwner!]

end OpResultPtr

namespace BlockPtr

def set (ptr : BlockPtr) (ctx : IRContext OpInfo) (newBlock : Block) : IRContext OpInfo :=
  {ctx with blocks := ctx.blocks.insert ptr newBlock}

def setParent (block : BlockPtr) (ctx : IRContext OpInfo) (newParent : Option RegionPtr)
    (inBounds : block.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with parent := newParent}

def setParent! (block : BlockPtr) (ctx : IRContext OpInfo) (newParent : Option RegionPtr) : IRContext OpInfo :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with parent := newParent}

@[grind =_, eq_bang ←]
theorem setParent!_eq_setParent {block : BlockPtr} (inBounds : block.InBounds ctx) :
    block.setParent! ctx newParent = block.setParent ctx newParent inBounds := by
  grind [setParent, setParent!]

def setFirstUse (block : BlockPtr) (ctx : IRContext OpInfo) (newFirstUse : Option BlockOperandPtr)
    (inBounds : block.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with firstUse := newFirstUse}

def setFirstUse! (block : BlockPtr) (ctx : IRContext OpInfo) (newFirstUse : Option BlockOperandPtr) : IRContext OpInfo :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with firstUse := newFirstUse}

@[grind =_, eq_bang ←]
theorem setFirstUse!_eq_setFirstUse {block : BlockPtr} (inBounds : block.InBounds ctx) :
    block.setFirstUse! ctx newFirstUse = block.setFirstUse ctx newFirstUse inBounds := by
  grind [setFirstUse, setFirstUse!]

def setFirstOp (block : BlockPtr) (ctx : IRContext OpInfo) (newFirstOp : Option OperationPtr)
    (inBounds : block.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with firstOp := newFirstOp}

def setFirstOp! (block : BlockPtr) (ctx : IRContext OpInfo) (newFirstOp : Option OperationPtr) : IRContext OpInfo :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with firstOp := newFirstOp}

@[grind =_, eq_bang ←]
theorem setFirstOp!_eq_setFirstOp {block : BlockPtr} (inBounds : block.InBounds ctx) :
    block.setFirstOp! ctx newFirstOp = block.setFirstOp ctx newFirstOp inBounds := by
  grind [setFirstOp, setFirstOp!]

def setLastOp (block : BlockPtr) (ctx : IRContext OpInfo) (newLastOp : Option OperationPtr)
    (inBounds : block.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with lastOp := newLastOp}

def setLastOp! (block : BlockPtr) (ctx : IRContext OpInfo) (newLastOp : Option OperationPtr) : IRContext OpInfo :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with lastOp := newLastOp}

@[grind =_, eq_bang ←]
theorem setLastOp!_eq_setLastOp {block : BlockPtr} (inBounds : block.InBounds ctx) :
    block.setLastOp! ctx newLastOp = block.setLastOp ctx newLastOp inBounds := by
  grind [setLastOp, setLastOp!]

def setNextBlock (block : BlockPtr) (ctx : IRContext OpInfo) (newNext : Option BlockPtr)
    (inBounds : block.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with next := newNext}

def setNextBlock! (block : BlockPtr) (ctx : IRContext OpInfo) (newNext : Option BlockPtr) : IRContext OpInfo :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with next := newNext}

@[grind =_, eq_bang ←]
theorem setNextBlock!_eq_setNextBlock {block : BlockPtr} (inBounds : block.InBounds ctx) :
    block.setNextBlock! ctx newNext = block.setNextBlock ctx newNext inBounds := by
  grind [setNextBlock, setNextBlock!]

def setPrevBlock (block : BlockPtr) (ctx : IRContext OpInfo) (newPrev : Option BlockPtr)
    (inBounds : block.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with prev := newPrev}

def setPrevBlock! (block : BlockPtr) (ctx : IRContext OpInfo) (newPrev : Option BlockPtr) : IRContext OpInfo :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with prev := newPrev}

@[grind =_, eq_bang ←]
theorem setPrevBlock!_eq_setPrevBlock {block : BlockPtr} (inBounds : block.InBounds ctx) :
    block.setPrevBlock! ctx newPrev = block.setPrevBlock ctx newPrev inBounds := by
  grind [setPrevBlock, setPrevBlock!]

def allocEmpty (ctx : IRContext OpInfo) : Option (IRContext OpInfo × BlockPtr) :=
  let newBlockPtr : BlockPtr := ⟨ctx.nextID⟩
  let ctx : IRContext OpInfo := { ctx with nextID := ctx.nextID + 1}
  if _ : ctx.blocks.contains newBlockPtr then none else
  let ctx := newBlockPtr.set ctx Block.empty
  some (ctx, newBlockPtr)

theorem allocEmpty_def (heq : allocEmpty ctx = some (ctx', ptr')) :
    ctx' = set ⟨ctx.nextID⟩ {ctx with nextID := ctx.nextID + 1} Block.empty := by
  grind [allocEmpty]

-- `inBounds` is currently unused, but we keep it as we intend to switch to a different data
-- structure that will require it in the future.
set_option linter.unusedVariables false in
def dealloc (block : BlockPtr) (ctx : IRContext OpInfo)
    (inBounds : block.InBounds ctx := by grind) : IRContext OpInfo :=
  { ctx with blocks := ctx.blocks.erase block }

def setArguments (block : BlockPtr) (ctx : IRContext OpInfo)
    (newArguments : Array BlockArgument) (inBounds : block.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldBlock := block.get ctx (by grind)
  block.set ctx { oldBlock with arguments := newArguments }

def setArguments! (block : BlockPtr) (ctx : IRContext OpInfo) (newArguments : Array BlockArgument) :
    IRContext OpInfo :=
  let oldBlock := block.get! ctx
  block.set ctx { oldBlock with arguments := newArguments }

@[grind =_, eq_bang ←]
theorem setArguments!_eq_setArguments {block : BlockPtr} (inBounds : block.InBounds ctx) :
    block.setArguments! ctx newArguments = block.setArguments ctx newArguments inBounds := by
  grind [setArguments, setArguments!]

def pushArgument (block : BlockPtr) (ctx : IRContext OpInfo) (result : BlockArgument)
      (inBounds : block.InBounds ctx := by grind) :=
    block.setArguments ctx ((block.get ctx).arguments.push result)

def pushArgument! (block : BlockPtr) (ctx : IRContext OpInfo) (result : BlockArgument) : IRContext OpInfo :=
  block.setArguments! ctx ((block.get! ctx).arguments.push result)

@[grind =_, eq_bang ←]
theorem pushArgument!_eq_pushArgument {block : BlockPtr} (inBounds : block.InBounds ctx) :
    block.pushArgument! ctx result = block.pushArgument ctx result inBounds := by
  grind [pushArgument, pushArgument!]

end BlockPtr

namespace BlockArgumentPtr

def set (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newresult : BlockArgument) (argIn : arg.InBounds ctx := by grind) : IRContext OpInfo :=
  let block := arg.block.get ctx
  { ctx with
    blocks := ctx.blocks.insert arg.block
      { block with arguments := block.arguments.set arg.index newresult (by grind)} }

def set! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newresult : BlockArgument) : IRContext OpInfo :=
  let block := arg.block.get! ctx
  { ctx with
    blocks := ctx.blocks.insert arg.block
      { block with arguments := block.arguments.set! arg.index newresult } }

@[grind =_, eq_bang ←]
theorem set!_eq_set {arg : BlockArgumentPtr} (inBounds : arg.InBounds ctx) :
    arg.set! ctx newresult = arg.set ctx newresult inBounds := by
  grind [set, set!]

def setType (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newType : TypeAttr) (argIn : arg.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with type := newType }

def setType! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newType : TypeAttr) : IRContext OpInfo :=
  let oldResult := arg.get! ctx
  arg.set! ctx { oldResult with type := newType }

@[grind =_, eq_bang ←]
theorem setType!_eq_setType {arg : BlockArgumentPtr} (inBounds : arg.InBounds ctx) :
    arg.setType! ctx newType = arg.setType ctx newType inBounds := by
  grind [setType, setType!]

def setFirstUse (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newFirstUse : Option OpOperandPtr) (argIn : arg.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with firstUse := newFirstUse }

def setFirstUse! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newFirstUse : Option OpOperandPtr) :
    IRContext OpInfo :=
  let oldResult := arg.get! ctx
  arg.set! ctx {oldResult with firstUse := newFirstUse}

@[grind =_, eq_bang ←]
theorem setFirstUse!_eq_setFirstUse {arg : BlockArgumentPtr} (inBounds : arg.InBounds ctx) :
    arg.setFirstUse! ctx newFirstUse = arg.setFirstUse ctx newFirstUse inBounds := by
  grind [setFirstUse, setFirstUse!]

def setIndex (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newIndex : Nat) (argIn : arg.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with index := newIndex }

def setIndex! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newIndex : Nat) : IRContext OpInfo :=
  let oldResult := arg.get! ctx
  arg.set! ctx {oldResult with index := newIndex}

@[grind =_, eq_bang ←]
theorem setIndex!_eq_setIndex {arg : BlockArgumentPtr} (inBounds : arg.InBounds ctx) :
    arg.setIndex! ctx newIndex = arg.setIndex ctx newIndex inBounds := by
  grind [setIndex, setIndex!]

def setLoc (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newLoc : Location) (argIn : arg.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with loc := newLoc }

def setLoc! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newLoc : Location) : IRContext OpInfo :=
  let oldResult := arg.get! ctx
  arg.set! ctx {oldResult with loc := newLoc}

@[grind =_, eq_bang ←]
theorem setLoc!_eq_setLoc {arg : BlockArgumentPtr} (inBounds : arg.InBounds ctx) :
    arg.setLoc! ctx newLoc = arg.setLoc ctx newLoc inBounds := by
  grind [setLoc, setLoc!]

def setOwner (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newOwner : BlockPtr) (argIn : arg.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with owner := newOwner }

def setOwner! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (newOwner : BlockPtr) : IRContext OpInfo :=
  let oldResult := arg.get! ctx
  arg.set! ctx {oldResult with owner := newOwner}

@[grind =_, eq_bang ←]
theorem setOwner!_eq_setOwner {arg : BlockArgumentPtr} (inBounds : arg.InBounds ctx) :
    arg.setOwner! ctx newOwner = arg.setOwner ctx newOwner inBounds := by
  grind [setOwner, setOwner!]

end BlockArgumentPtr

namespace ValuePtr

def setType (arg : ValuePtr) (ctx : IRContext OpInfo) (newType : TypeAttr) (argIn : arg.InBounds ctx := by grind) : IRContext OpInfo :=
  match arg with
  | opResult ptr => ptr.setType ctx newType
  | blockArgument ptr => ptr.setType ctx newType

def setType! (arg : ValuePtr) (ctx : IRContext OpInfo) (newType : TypeAttr) : IRContext OpInfo :=
  match arg with
  | opResult ptr => ptr.setType! ctx newType
  | blockArgument ptr => ptr.setType! ctx newType

@[grind =_, eq_bang ←]
theorem setType!_eq_setType {arg : ValuePtr} (inBounds : arg.InBounds ctx) :
    arg.setType! ctx newType = arg.setType ctx newType inBounds := by
  grind [setType, setType!, cases ValuePtr]

def setFirstUse (arg : ValuePtr) (ctx : IRContext OpInfo) (newFirstUse : Option OpOperandPtr) (argIn : arg.InBounds ctx := by grind) : IRContext OpInfo :=
  match arg with
  | opResult ptr => ptr.setFirstUse ctx newFirstUse
  | blockArgument ptr => ptr.setFirstUse ctx newFirstUse

def setFirstUse! (arg : ValuePtr) (ctx : IRContext OpInfo) (newFirstUse : Option OpOperandPtr) : IRContext OpInfo :=
  match arg with
  | opResult ptr => ptr.setFirstUse! ctx newFirstUse
  | blockArgument ptr => ptr.setFirstUse! ctx newFirstUse

@[grind =_, eq_bang ←]
theorem setFirstUse!_eq_setFirstUse {arg : ValuePtr} (inBounds : arg.InBounds ctx) :
    arg.setFirstUse! ctx newFirstUse = arg.setFirstUse ctx newFirstUse inBounds := by
  grind [setFirstUse, setFirstUse!, cases ValuePtr]

@[simp, grind =]
theorem setFirstUse_OpResultPtr (ptr : OpResultPtr) (ctx : IRContext OpInfo)
    (ptrIn : (opResult ptr).InBounds ctx) (newFirstUse : Option OpOperandPtr) :
    (opResult ptr).setFirstUse ctx newFirstUse ptrIn = ptr.setFirstUse ctx newFirstUse := by
  unfold setFirstUse; grind

@[simp, grind =]
theorem setFirstUse_BlockArgumentPtr (ptr : BlockArgumentPtr) (ctx : IRContext OpInfo)
    (ptrIn : (blockArgument ptr).InBounds ctx) (newFirstUse : Option OpOperandPtr) :
    (blockArgument ptr).setFirstUse ctx newFirstUse ptrIn = ptr.setFirstUse ctx newFirstUse := by
  unfold setFirstUse; rfl

@[simp, grind =]
theorem setType_OpResultPtr (ptr : OpResultPtr) (ctx : IRContext OpInfo)
    (ptrIn : (opResult ptr).InBounds ctx) (newType : TypeAttr) :
    (opResult ptr).setType ctx newType ptrIn = ptr.setType ctx newType := by
  unfold setType; rfl

@[simp, grind =]
theorem setType_BlockArgumentPtr (ptr : BlockArgumentPtr) (ctx : IRContext OpInfo)
    (ptrIn : (blockArgument ptr).InBounds ctx) (newType : TypeAttr) :
    (blockArgument ptr).setType ctx newType ptrIn = ptr.setType ctx newType := by
  unfold setType; rfl

end ValuePtr

namespace OpOperandPtrPtr

def set (ptrPtr : OpOperandPtrPtr) (ctx : IRContext OpInfo) (newValue : Option OpOperandPtr) (ptrPtrIn : ptrPtr.InBounds ctx := by grind) : IRContext OpInfo :=
  match ptrPtr with
  | operandNextUse ptr =>
    ptr.setNextUse ctx newValue
  | valueFirstUse val =>
    val.setFirstUse ctx newValue

def set! (ptrPtr : OpOperandPtrPtr) (ctx : IRContext OpInfo) (newValue : Option OpOperandPtr) : IRContext OpInfo :=
  match ptrPtr with
  | operandNextUse ptr =>
    ptr.setNextUse! ctx newValue
  | valueFirstUse val =>
    val.setFirstUse! ctx newValue

@[grind =_, eq_bang ←]
theorem set!_eq_set {ptrPtr : OpOperandPtrPtr} (inBounds : ptrPtr.InBounds ctx) :
    ptrPtr.set! ctx newValue = ptrPtr.set ctx newValue inBounds := by
  grind [set, set!, cases OpOperandPtrPtr]

@[simp]
theorem set_operandNextUse (ptr : OpOperandPtr) (ctx : IRContext OpInfo) (newValue : Option OpOperandPtr) (ptrIn : (operandNextUse ptr).InBounds ctx) :
    (operandNextUse ptr).set ctx newValue ptrIn = ptr.setNextUse ctx newValue := by
  unfold set; rfl

@[simp]
theorem set_valueFirstUse (ptr : ValuePtr) (ctx : IRContext OpInfo) (ptrIn : (valueFirstUse ptr).InBounds ctx) (newValue : Option OpOperandPtr) :
    (valueFirstUse ptr).set ctx newValue ptrIn = ptr.setFirstUse ctx newValue := by
  unfold set; rfl

end OpOperandPtrPtr

namespace RegionPtr

def set (ptr : RegionPtr) (ctx : IRContext OpInfo) (newRegion : Region) : IRContext OpInfo :=
  {ctx with regions := ctx.regions.insert ptr newRegion}

def setParent (region : RegionPtr) (ctx : IRContext OpInfo) (newParent : Option OperationPtr)
    (inBounds : region.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldRegion := region.get ctx (by grind)
  region.set ctx { oldRegion with parent := newParent}

def setParent! (region : RegionPtr) (ctx : IRContext OpInfo) (newParent : OperationPtr) : IRContext OpInfo :=
  let oldRegion := region.get! ctx
  region.set ctx {oldRegion with parent := newParent}

@[grind =_, eq_bang ←]
theorem setParent!_eq_setParent {region : RegionPtr} (inBounds : region.InBounds ctx) :
    region.setParent! ctx newParent = region.setParent ctx newParent inBounds := by
  grind [setParent, setParent!]

def setFirstBlock (region : RegionPtr) (ctx : IRContext OpInfo) (newFirstBlock : Option BlockPtr)
    (inBounds : region.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldRegion := region.get ctx (by grind)
  region.set ctx { oldRegion with firstBlock := newFirstBlock}

def setFirstBlock! (region : RegionPtr) (ctx : IRContext OpInfo) (newFirstBlock : Option BlockPtr) : IRContext OpInfo :=
  let oldRegion := region.get! ctx
  region.set ctx {oldRegion with firstBlock := newFirstBlock}

@[grind =_, eq_bang ←]
theorem setFirstBlock!_eq_setFirstBlock {region : RegionPtr} (inBounds : region.InBounds ctx) :
    region.setFirstBlock! ctx newFirstBlock = region.setFirstBlock ctx newFirstBlock inBounds := by
  grind [setFirstBlock, setFirstBlock!]

def setLastBlock (region : RegionPtr) (ctx : IRContext OpInfo) (newLastBlock : Option BlockPtr)
    (inBounds : region.InBounds ctx := by grind) : IRContext OpInfo :=
  let oldRegion := region.get ctx (by grind)
  region.set ctx { oldRegion with lastBlock := newLastBlock}

def setLastBlock! (region : RegionPtr) (ctx : IRContext OpInfo) (newLastBlock : Option BlockPtr) : IRContext OpInfo :=
  let oldRegion := region.get! ctx
  region.set ctx {oldRegion with lastBlock := newLastBlock}

@[grind =_, eq_bang ←]
theorem setLastBlock!_eq_setLastBlock {region : RegionPtr} (inBounds : region.InBounds ctx) :
    region.setLastBlock! ctx newLastBlock = region.setLastBlock ctx newLastBlock inBounds := by
  grind [setLastBlock, setLastBlock!]

def allocEmpty (ctx : IRContext OpInfo) : Option (IRContext OpInfo × RegionPtr) :=
  let newRegionPtr : RegionPtr := ⟨ctx.nextID⟩
  let region := Region.empty
  let ctx := { ctx with nextID := ctx.nextID + 1}
  if _ : ctx.regions.contains newRegionPtr then none else
  let ctx := newRegionPtr.set ctx region
  (ctx, newRegionPtr)

-- `inBounds` is currently unused, but we keep it as we intend to switch to a different data
-- structure that will require it in the future.
set_option linter.unusedVariables false in
def dealloc (region : RegionPtr) (ctx : IRContext OpInfo)
    (inBounds : region.InBounds ctx := by grind) : IRContext OpInfo :=
  { ctx with regions := ctx.regions.erase region }

end RegionPtr

namespace BlockOperandPtrPtr

def set (ptrPtr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) (newValue : Option BlockOperandPtr) (ptrPtrIn : ptrPtr.InBounds ctx := by grind) : IRContext OpInfo :=
  match ptrPtr with
  | blockOperandNextUse ptr => ptr.setNextUse ctx newValue
  | blockFirstUse val => val.setFirstUse ctx newValue

def set! (ptrPtr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) (newValue : Option BlockOperandPtr) :
    IRContext OpInfo :=
  match ptrPtr with
  | blockOperandNextUse ptr => ptr.setNextUse! ctx newValue
  | blockFirstUse val => val.setFirstUse! ctx newValue

@[grind =_, eq_bang ←]
theorem set!_eq_set {ptrPtr : BlockOperandPtrPtr} (inBounds : ptrPtr.InBounds ctx) :
    ptrPtr.set! ctx newValue = ptrPtr.set ctx newValue inBounds := by
  grind [set, set!, cases BlockOperandPtrPtr]

@[simp, grind =]
theorem set_operandNextUse_eq {ptr : BlockOperandPtr} {ptrIn : ptr.InBounds ctx} {newValue : Option BlockOperandPtr} :
    (blockOperandNextUse ptr).set ctx newValue = ptr.setNextUse ctx newValue := by
  rfl

@[simp, grind =]
theorem set_blockFirstUse_eq {ptr : BlockPtr} {ptrIn : ptr.InBounds ctx} {newValue : Option BlockOperandPtr} :
    (blockFirstUse ptr).set ctx newValue = ptr.setFirstUse ctx newValue := by
  rfl

end BlockOperandPtrPtr

def IRContext.empty (OpInfo : Type) [IsOpCode OpInfo] : IRContext OpInfo := {
    nextID := 0,
    operations := Std.HashMap.emptyWithCapacity,
    blocks := Std.HashMap.emptyWithCapacity,
    regions := Std.HashMap.emptyWithCapacity,
  }

/--
  Macro to mark all get/set defitinions as local grind lemmas
  This should only be used inside `Core/`, as the other files in this folder
  should define all the necessary lemmas without having to unfold these definitions.
-/
macro "setup_grind_with_get_set_definitions" : command => `(
  attribute [local grind cases] ValuePtr OpOperandPtr GenericPtr BlockOperandPtr OpResultPtr BlockArgumentPtr BlockOperandPtrPtr OpOperandPtrPtr
  attribute [local grind] IRContext.empty
  attribute [local grind] OpOperandPtr.setNextUse OpOperandPtr.setBack OpOperandPtr.setOwner OpOperandPtr.setValue OpOperandPtr.set
  attribute [local grind] OpOperandPtrPtr.set OpOperandPtrPtr.get!
  attribute [local grind] ValuePtr.getFirstUse! ValuePtr.getFirstUse ValuePtr.setFirstUse ValuePtr.setType ValuePtr.getType ValuePtr.getType!
  attribute [local grind] OpResultPtr.get! OpResultPtr.setFirstUse OpResultPtr.set OpResultPtr.setType
  attribute [local grind] BlockArgumentPtr.get! BlockArgumentPtr.setFirstUse BlockArgumentPtr.set BlockArgumentPtr.setType BlockArgumentPtr.setLoc
  attribute [local grind] OperationPtr.setOperands OperationPtr.setBlockOperands OperationPtr.setResults OperationPtr.pushResult OperationPtr.setRegions OperationPtr.pushRegion OperationPtr.setProperties OperationPtr.setAttributes OperationPtr.pushOperand OperationPtr.pushBlockOperand OperationPtr.allocEmpty OperationPtr.dealloc OperationPtr.setNextOp OperationPtr.setPrevOp OperationPtr.setParent OperationPtr.getNumResults! OperationPtr.getNumOperands! OperationPtr.getNumRegions! OperationPtr.getRegion! OperationPtr.getNumSuccessors! OperationPtr.getProperties! OperationPtr.set OperationPtr.getOperands! OperationPtr.getOpType!
  attribute [local grind] Operation.empty
  attribute [local grind] BlockPtr.get! BlockPtr.setParent BlockPtr.setFirstUse BlockPtr.setFirstOp BlockPtr.setLastOp BlockPtr.setNextBlock BlockPtr.setPrevBlock BlockPtr.allocEmpty BlockPtr.dealloc Block.empty BlockPtr.getNumArguments! BlockPtr.set BlockPtr.setArguments BlockPtr.pushArgument
  attribute [local grind =] Option.maybe_def
  attribute [local grind] OpOperandPtr.get! BlockOperandPtr.get! OpResultPtr.get! BlockArgumentPtr.get! OperationPtr.get!
  attribute [local grind] BlockOperandPtr.setBack BlockOperandPtr.setNextUse BlockOperandPtr.setOwner BlockOperandPtr.setValue BlockOperandPtr.set
  attribute [local grind] BlockOperandPtrPtr.get!
  attribute [local grind] RegionPtr.get! RegionPtr.setParent RegionPtr.setFirstBlock RegionPtr.setLastBlock RegionPtr.set RegionPtr.allocEmpty RegionPtr.dealloc
)

end Veir
