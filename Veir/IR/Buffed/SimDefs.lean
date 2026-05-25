module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Layout
public import Veir.Prelude
public import Veir.IR.Buffed.Layout
public import Veir.IR.Fields

import Veir.IR.Fields

/-!
# Simulation pointer structures and the `Sim` refinement predicate

This module holds the definitions that `@[buffed]` (in `Meta`) refers to via name literals: the
`Sim.IRContext` structure together with the `Sim` refinement predicate and its prerequisites
(`toFlat`/`toM`/`toO`/`range`, the `IsRepr`/`Matches` families), plus the `impl`/`spec` pointer-pair
structures. `Meta` imports `SimDefs`, and `Sim` imports `Meta`, so these have to live before `Meta`
in the import graph rather than in `Sim` itself.
-/

open Veir.Buffed

public section

-- TODO: Move in prelude?
instance : HAdd Nat (Std.Rco Int) (Std.Rco Nat) where
  hAdd x y := (x + y.lower).toNat...(x + y.upper).toNat

namespace Veir

variable [HasOpInfo OpInfo]

/-! ## Translate a high-level pointer to a flat address. -/

def OperationPtr.toFlat (ptr : OperationPtr) := ptr.id

def BlockPtr.toFlat (ptr : BlockPtr) := ptr.id

def RegionPtr.toFlat (ptr : RegionPtr) := ptr.id

def OpResultPtr.toFlat (ptr : OpResultPtr) (ctx : IRContext OpInfo) :=
  (OfNat.ofNat ptr.op.toFlat + (Buffed.Operation.Offsets.results ptr.op ctx).toInt).toNat +
  ptr.index * Buffed.OpResult.size.toNat

def OpOperandPtr.toFlat (ptr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  (OfNat.ofNat ptr.op.toFlat + (Buffed.Operation.Offsets.operands ptr.op ctx).toInt).toNat +
  ptr.index * Buffed.OpOperand.size.toNat

def BlockOperandPtr.toFlat (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  (OfNat.ofNat ptr.op.toFlat + (Buffed.Operation.Offsets.blockOperands ptr.op ctx).toInt).toNat +
  ptr.index * Buffed.BlockOperand.size.toNat

def BlockArgumentPtr.toFlat (ptr : BlockArgumentPtr) :=
  (OfNat.ofNat ptr.block.toFlat + Buffed.Block.Offsets.arguments.toInt).toNat +
  ptr.index * Buffed.BlockArgument.size.toNat

def ValuePtr.toFlat (ptr : ValuePtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .opResult ptr => ptr.toFlat ctx
  | .blockArgument ptr => ptr.toFlat

def OpOperandPtrPtr.toFlat (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse ptr => ptr.toFlat ctx + Buffed.OpOperand.Offsets.nextUse.toInt.toNat
  | .valueFirstUse ptr => ptr.toFlat ctx + Buffed.ValueImpl.Offsets.firstUse.toInt.toNat

def BlockOperandPtrPtr.toFlat (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse ptr => ptr.toFlat ctx + Buffed.BlockOperand.Offsets.nextUse.toInt.toNat
  | .blockFirstUse ptr => ptr.toFlat + Buffed.Block.Offsets.firstUse.toInt.toNat

/-! ## A pointer is representable if it fits in 63 bits. -/

@[grind] def OperationPtr.IsRepr (ptr : OperationPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind] def BlockPtr.IsRepr (ptr : BlockPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind] def RegionPtr.IsRepr (ptr : RegionPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

/-! ## Translate a high-level pointer to a buffed address. -/

def OperationPtr.toM (ptr : OperationPtr) : OperationMPtr := ptr.toFlat.toUInt64
def OperationPtr.toO (ptr : Option OperationPtr) : OperationOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

def BlockPtr.toM (ptr : BlockPtr) : BlockMPtr := ptr.toFlat.toUInt64
def BlockPtr.toO (ptr : Option BlockPtr) : BlockOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

def RegionPtr.toM (ptr : RegionPtr) : RegionMPtr := ptr.toFlat.toUInt64
def RegionPtr.toO (ptr : Option RegionPtr) : RegionOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

def OpResultPtr.toM (ptr : OpResultPtr) (ctx : IRContext OpInfo) : OpResultMPtr :=
  (ptr.toFlat ctx).toUInt64
def OpResultPtr.toO (ptr : Option OpResultPtr) (ctx : IRContext OpInfo) : OpResultOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

def BlockArgumentPtr.toM (ptr : BlockArgumentPtr) : BlockArgumentMPtr :=
  ptr.toFlat.toUInt64
def BlockArgumentPtr.toO (ptr : Option BlockArgumentPtr) : BlockArgumentOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

def OpOperandPtr.toM (ptr : OpOperandPtr) (ctx : IRContext OpInfo) : OpOperandMPtr :=
  (ptr.toFlat ctx).toUInt64
def OpOperandPtr.toO (ptr : Option OpOperandPtr) (ctx : IRContext OpInfo) : OpOperandOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

def BlockOperandPtr.toM (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperandMPtr :=
  (ptr.toFlat ctx).toUInt64
def BlockOperandPtr.toO (ptr : Option BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperandOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

def ValuePtr.toM (ptr : ValuePtr) (ctx : IRContext OpInfo) : ValueImplMPtr :=
  (ptr.toFlat ctx).toUInt64
def ValuePtr.toO (ptr : Option ValuePtr) (ctx : IRContext OpInfo) : ValueImplOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

@[simp, grind =]
theorem ValuePtr.toM_opResult {ctx : IRContext OpInfo} : (ValuePtr.opResult res).toM ctx = res.toM ctx := by rfl

@[simp, grind =]
theorem ValuePtr.toM_blockArgument {ctx : IRContext OpInfo} : (ValuePtr.blockArgument arg).toM ctx = arg.toM := by rfl

def OpOperandPtrPtr.toM (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  (ptr.toFlat ctx).toUInt64

def BlockOperandPtrPtr.toM (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  (ptr.toFlat ctx).toUInt64

def GenericPtr.toM (ptr : GenericPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  match ptr with
  | .operation ptr => ptr.toM
  | .block ptr => ptr.toM
  | .region ptr => ptr.toM
  | .opResult ptr => ptr.toM ctx
  | .blockArgument ptr => ptr.toM
  | .opOperand ptr => ptr.toM ctx
  | .blockOperand ptr => ptr.toM ctx
  | .blockOperandPtr ptr => ptr.toM ctx
  | .value ptr => ptr.toM ctx
  | .opOperandPtr ptr => ptr.toM ctx

def GenericPtr.toO (ptr : Option GenericPtr) (ctx : IRContext OpInfo) : GenericOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

/-! ## Range of a pointer -/

def OperationPtr.range (op : OperationPtr) (ctx : IRContext OpInfo) :=
  op.toFlat + (Buffed.Operation.range op ctx)

def BlockPtr.range (bl : BlockPtr) (ctx : IRContext OpInfo) :=
  bl.toFlat + Buffed.Block.range bl ctx

def RegionPtr.range (rg : RegionPtr) :=
  rg.toFlat + Buffed.Region.range

def OpResultPtr.range (res : OpResultPtr) (ctx : IRContext OpInfo) :=
  res.toFlat ctx + Buffed.OpResult.range

def BlockArgumentPtr.range (arg : BlockArgumentPtr) :=
  arg.toFlat + Buffed.BlockArgument.range

def OpOperandPtr.range (opr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlat ctx + Buffed.OpOperand.range

def BlockOperandPtr.range (opr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlat ctx + Buffed.BlockOperand.range

def ValuePtr.range (val : ValuePtr) (ctx : IRContext OpInfo) :=
  match val with
  | .opResult res => res.range ctx
  | .blockArgument arg => arg.range

def OpOperandPtrPtr.range (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse opr => opr.range ctx
  | .valueFirstUse val => val.range ctx

def BlockOperandPtrPtr.range (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse opr => opr.range ctx
  | .blockFirstUse bl => bl.range ctx

def GenericPtr.range (ptr : GenericPtr) (ctx : IRContext OpInfo) : Std.Rco Nat :=
  match ptr with
  | .operation op => op.range ctx
  | .block bl => bl.range ctx
  | .region rg => rg.range
  | .opResult res => res.range ctx
  | .opOperand opr => opr.range ctx
  | .blockOperand opr => opr.range ctx
  | .blockOperandPtr ptr => ptr.range ctx
  | .blockArgument arg => arg.range
  | .value val => val.range ctx
  | .opOperandPtr ptr => ptr.range ctx

/-! ## An object is representable if all its fields are representable. -/

@[grind]
structure Operation.ReprIndices (val : OperationPtr) (ctx : IRContext OpInfo) where
  results : val.getNumResults! ctx ≤ countCard
  operands : val.getNumOperands! ctx ≤ countCard
  blockOperands : val.getNumSuccessors! ctx ≤ countCard
  regions : val.getNumRegions! ctx ≤ countCard

@[grind]
structure Block.ReprIndices (val : BlockPtr) (ctx : IRContext OpInfo) where
  arguments : val.getNumArguments! ctx ≤ countCard

@[grind]
structure IRContext.IsRepr (ctx : IRContext OpInfo) where
  operations (op : OperationPtr) (hin : op.InBounds ctx) : op.IsRepr
  operations_indices (op : OperationPtr) (hin : op.InBounds ctx) : Operation.ReprIndices op ctx
  blocks (blk : BlockPtr) (hin : blk.InBounds ctx) : blk.IsRepr
  blocks_indices (blk : BlockPtr) (hin : blk.InBounds ctx) : Block.ReprIndices blk ctx
  regions (rg : RegionPtr) (hin : rg.InBounds ctx) : rg.IsRepr

/-! ## Other pointer representations -/

@[grind] def OpResultPtr.IsRepr (ptr : OpResultPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def OpOperandPtr.IsRepr (ptr : OpOperandPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def BlockOperandPtr.IsRepr (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def BlockArgumentPtr.IsRepr (ptr : BlockArgumentPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind] def ValuePtr.IsRepr (ptr : ValuePtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def OpOperandPtrPtr.IsRepr (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind] def BlockOperandPtrPtr.IsRepr (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

/-! ## Sim Pointers -/

@[grind] -- TODO: finer grained grind strategy
structure Sim.OperationPtr where
  impl : OperationMPtr
  spec : Veir.OperationPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionOperationPtr where
  impl : OperationOPtr
  spec : Option Veir.OperationPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.BlockPtr where
  impl : BlockMPtr
  spec : Veir.BlockPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionBlockPtr where
  impl : BlockOPtr
  spec : Option Veir.BlockPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.RegionPtr where
  impl : RegionMPtr
  spec : Veir.RegionPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionRegionPtr where
  impl : RegionOPtr
  spec : Option Veir.RegionPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OpResultPtr where
  impl : OpResultMPtr
  spec : Veir.OpResultPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.BlockArgumentPtr where
  impl : BlockArgumentMPtr
  spec : Veir.BlockArgumentPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OpOperandPtr where
  impl : OpOperandMPtr
  spec : Veir.OpOperandPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionOpOperandPtr where
  impl : OpOperandOPtr
  spec : Option Veir.OpOperandPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionOpResultPtr where
  impl : OpResultOPtr
  spec : Option Veir.OpResultPtr

@[grind] -- TODO: finer grained grind strategy
structure Sim.BlockOperandPtr where
  impl : BlockOperandMPtr
  spec : Veir.BlockOperandPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionBlockOperandPtr where
  impl : BlockOperandOPtr
  spec : Option Veir.BlockOperandPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.ValuePtr where
  impl : ValueImplMPtr
  spec : Veir.ValuePtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OpOperandPtrPtr where
  impl : OpOperandPtrMPtr
  spec : Veir.OpOperandPtrPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionBlockArgumentPtr where
  impl : BlockArgumentOPtr
  spec : Option Veir.BlockArgumentPtr

@[grind] -- TODO: finer grained grind strategy
structure Sim.BlockOperandPtrPtr where
  impl : BlockOperandPtrMPtr
  spec : Veir.BlockOperandPtrPtr
deriving Inhabited

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionValuePtr where
  impl : ValueImplOPtr
  spec : Option Veir.ValuePtr

@[grind] -- TODO: finer grained grind strategy
structure Sim.GenericPtr where
  impl : GenericMPtr
  spec : Veir.GenericPtr

@[grind]
def Sim.GenericPtr.fromBlock (ptr : BlockPtr) : GenericPtr :=
  ⟨ptr.impl, .block ptr.spec⟩
@[grind]
def Sim.GenericPtr.fromOperation (ptr : OperationPtr) : GenericPtr :=
  ⟨ptr.impl, .operation ptr.spec⟩
@[grind]
def Sim.GenericPtr.fromOpResult (ptr : OpResultPtr) : GenericPtr :=
  ⟨ptr.impl, .opResult ptr.spec⟩
@[grind]
def Sim.GenericPtr.fromOpOperand (ptr : OpOperandPtr) : GenericPtr :=
  ⟨ptr.impl, .opOperand ptr.spec⟩
@[grind]
def Sim.GenericPtr.fromBlockOperand (ptr : BlockOperandPtr) : GenericPtr :=
  ⟨ptr.impl, .blockOperand ptr.spec⟩
@[grind]
def Sim.GenericPtr.fromBlockOperandPtr (ptr : BlockOperandPtrPtr) : GenericPtr :=
  ⟨ptr.impl, .blockOperandPtr ptr.spec⟩
@[grind]
def Sim.GenericPtr.fromBlockArgument (ptr : BlockArgumentPtr) : GenericPtr :=
  ⟨ptr.impl, .blockArgument ptr.spec⟩
@[grind]
def Sim.GenericPtr.fromRegion (ptr : RegionPtr) : GenericPtr :=
  ⟨ptr.impl, .region ptr.spec⟩
@[grind]
def Sim.GenericPtr.fromValue (ptr : ValuePtr) : GenericPtr :=
  ⟨ptr.impl, .value ptr.spec⟩
@[grind]
def Sim.GenericPtr.fromOpOperandPtr (ptr : OpOperandPtrPtr) : GenericPtr :=
  ⟨ptr.impl, .opOperandPtr ptr.spec⟩

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionGenericPtr where
  impl : GenericOPtr
  spec : Option Veir.GenericPtr

@[grind]
def Sim.OptionGenericPtr.fromBlock (ptr : OptionBlockPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .block⟩
@[grind]
def Sim.OptionGenericPtr.fromOperation (ptr : OptionOperationPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .operation⟩
@[grind]
def Sim.OptionGenericPtr.fromOpResult (ptr : OptionOpResultPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .opResult⟩
@[grind]
def Sim.OptionGenericPtr.fromOpOperand (ptr : OptionOpOperandPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map  .opOperand⟩
@[grind]
def Sim.OptionGenericPtr.fromBlockOperand (ptr : OptionBlockOperandPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .blockOperand⟩
@[grind]
def Sim.OptionGenericPtr.fromBlockArgument (ptr : OptionBlockArgumentPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .blockArgument⟩
@[grind]
def Sim.OptionGenericPtr.fromRegion (ptr : OptionRegionPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .region⟩
@[grind]
def Sim.OptionGenericPtr.fromValue (ptr : OptionValuePtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .value⟩

/-! ## Refinement for Sim Pointers -/

variable (OpInfo) [HasOpInfo OpInfo] in
structure Sim.RawIRContext where
  buf : IRBufContext OpInfo
  spec : Veir.IRContext OpInfo

@[grind] -- TODO: finer grained grind strategy
def Sim.OperationPtr.Sim (ptr : Sim.OperationPtr) :=
  ptr.spec.toM = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OptionOperationPtr.Sim (ptr : Sim.OptionOperationPtr) :=
  OperationPtr.toO ptr.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.BlockPtr.Sim (ptr : Sim.BlockPtr) :=
  ptr.spec.toM = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OptionBlockPtr.Sim (ptr : Sim.OptionBlockPtr) :=
  BlockPtr.toO ptr.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.RegionPtr.Sim (ptr : Sim.RegionPtr) :=
  ptr.spec.toM = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OptionRegionPtr.Sim (ptr : Sim.OptionRegionPtr) :=
  RegionPtr.toO ptr.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OpResultPtr.Sim (ptr : Sim.OpResultPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OptionOpResultPtr.Sim (ptr : Sim.OptionOpResultPtr) (ctx : Sim.RawIRContext OpInfo) :=
  OpResultPtr.toO ptr.spec ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.BlockArgumentPtr.Sim (ptr : Sim.BlockArgumentPtr) :=
  ptr.spec.toM = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OptionBlockArgumentPtr.Sim (ptr : Sim.OptionBlockArgumentPtr) :=
  BlockArgumentPtr.toO ptr.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OpOperandPtr.Sim (ptr : Sim.OpOperandPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OptionOpOperandPtr.Sim (ptr : Sim.OptionOpOperandPtr) (ctx : Sim.RawIRContext OpInfo) :=
  OpOperandPtr.toO ptr.spec ctx.spec = ptr.impl
@[grind] -- TODO: finer grained grind strategy
def Sim.BlockOperandPtr.Sim (ptr : Sim.BlockOperandPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OptionBlockOperandPtr.Sim (ptr : Sim.OptionBlockOperandPtr) (ctx : Sim.RawIRContext OpInfo) :=
  BlockOperandPtr.toO ptr.spec ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.ValuePtr.Sim (ptr : Sim.ValuePtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OptionValuePtr.Sim (ptr : Sim.OptionValuePtr) (ctx : Sim.RawIRContext OpInfo) :=
  ValuePtr.toO ptr.spec ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OpOperandPtrPtr.Sim (ptr : Sim.OpOperandPtrPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.BlockOperandPtrPtr.Sim (ptr : Sim.BlockOperandPtrPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.GenericPtr.Sim (ptr : Sim.GenericPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

@[grind] -- TODO: finer grained grind strategy
def Sim.OptionGenericPtr.Sim (ptr : Sim.OptionGenericPtr) (ctx : Sim.RawIRContext OpInfo) :=
  GenericPtr.toO ptr.spec ctx.spec = ptr.impl

/-! ## Refinement predicate. -/

structure OpResultPtr.Matches (ctx : Sim.RawIRContext OpInfo) (res : OpResultPtr) (ib : res.InBounds ctx.spec) where
  typee : ctx.buf.attributes[(res.toM ctx.spec).readType! ctx.buf |>.toNat]? = some (res.get! ctx.spec).type
  firstUse : Sim.OptionOpOperandPtr.Sim ⟨(res.toM ctx.spec).readFirstUse! ctx.buf, (res.get! ctx.spec).firstUse⟩ ctx
  index : (res.get! ctx.spec).index = ((res.toM ctx.spec).readIndex! ctx.buf).toNat
  owner : Sim.OperationPtr.Sim ⟨(res.toM ctx.spec).readOwner! ctx.buf, (res.get! ctx.spec).owner⟩

structure BlockOperandPtr.Matches (ctx : Sim.RawIRContext OpInfo) (oper : BlockOperandPtr) (ib : oper.InBounds ctx.spec) where
  nextUse : Sim.OptionBlockOperandPtr.Sim ⟨BlockOperandMPtr.readNextUse! ctx.buf (oper.toM ctx.spec), (oper.get! ctx.spec).nextUse⟩ ctx
  back : Sim.BlockOperandPtrPtr.Sim ⟨BlockOperandMPtr.readBack! ctx.buf (oper.toM ctx.spec), (oper.get! ctx.spec).back⟩ ctx
  owner : Sim.OperationPtr.Sim ⟨BlockOperandMPtr.readOwner! ctx.buf (oper.toM ctx.spec), (oper.get! ctx.spec).owner⟩
  value : Sim.BlockPtr.Sim ⟨BlockOperandMPtr.readValue! ctx.buf (oper.toM ctx.spec), (oper.get! ctx.spec).value⟩

structure BlockArgumentPtr.Matches (ctx : Sim.RawIRContext OpInfo) (arg : BlockArgumentPtr) (ib : arg.InBounds ctx.spec) where
  type : ctx.buf.attributes[arg.toM.readType! ctx.buf |>.toNat]? = some (arg.get! ctx.spec).type
  firstUse : Sim.OptionOpOperandPtr.Sim ⟨arg.toM.readFirstUse! ctx.buf, (arg.get! ctx.spec).firstUse⟩ ctx
  index : (arg.get! ctx.spec).index = (arg.toM.readIndex! ctx.buf).toNat
  owner : Sim.BlockPtr.Sim ⟨arg.toM.readOwner! ctx.buf, (arg.get! ctx.spec).owner⟩
  -- `loc` is not implemented yet

structure BlockPtr.MatchesBase (ctx : Sim.RawIRContext OpInfo) (block : BlockPtr) (ib : block.InBounds ctx.spec) where
  firstUse : Sim.OptionBlockOperandPtr.Sim ⟨BlockMPtr.readFirstUse! ctx.buf block.toM, (block.get! ctx.spec).firstUse⟩ ctx
  prev : Sim.OptionBlockPtr.Sim ⟨BlockMPtr.readPrev! ctx.buf block.toM, (block.get! ctx.spec).prev⟩
  next : Sim.OptionBlockPtr.Sim ⟨BlockMPtr.readNext! ctx.buf block.toM, (block.get! ctx.spec).next⟩
  parent : Sim.OptionRegionPtr.Sim ⟨BlockMPtr.readParent! ctx.buf block.toM, (block.get! ctx.spec).parent⟩
  firstOp : Sim.OptionOperationPtr.Sim ⟨BlockMPtr.readFirstOp! ctx.buf block.toM, (block.get! ctx.spec).firstOp⟩
  lastOp : Sim.OptionOperationPtr.Sim ⟨BlockMPtr.readLastOp! ctx.buf block.toM, (block.get! ctx.spec).lastOp⟩

structure BlockPtr.MatchesArguments (ctx : Sim.RawIRContext OpInfo) (res : BlockPtr) where
  numArguments : (res.get! ctx.spec).capArguments = (BlockMPtr.readNumArguments! ctx.buf (res.toM)).toNat
  arguments (arg : BlockArgumentPtr) (ib : arg.InBounds ctx.spec) : arg.block = res → arg.Matches ctx ib

structure BlockPtr.Matches (ctx : Sim.RawIRContext OpInfo) (block : BlockPtr) (ib : block.InBounds ctx.spec) extends
  BlockPtr.MatchesBase ctx block ib,
  BlockPtr.MatchesArguments ctx block

structure OpOperandPtr.Matches (ctx : Sim.RawIRContext OpInfo) (oper : OpOperandPtr) (ib : oper.InBounds ctx.spec) where
  nextUse : Sim.OptionOpOperandPtr.Sim ⟨OpOperandMPtr.readNextUse! ctx.buf (oper.toM ctx.spec), (oper.get! ctx.spec).nextUse⟩ ctx
  back : Sim.OpOperandPtrPtr.Sim ⟨OpOperandMPtr.readBack! ctx.buf (oper.toM ctx.spec), (oper.get! ctx.spec).back⟩ ctx
  owner : Sim.OperationPtr.Sim ⟨OpOperandMPtr.readOwner! ctx.buf (oper.toM ctx.spec), (oper.get! ctx.spec).owner⟩
  value : Sim.ValuePtr.Sim ⟨OpOperandMPtr.readValue! ctx.buf (oper.toM ctx.spec), (oper.get! ctx.spec).value⟩ ctx

structure RegionPtr.Matches (ctx : Sim.RawIRContext OpInfo) (reg : RegionPtr)  (ib : reg.InBounds ctx.spec) where
  firstBlock : Sim.OptionBlockPtr.Sim ⟨RegionMPtr.readFirstBlock! ctx.buf reg.toM, (reg.get! ctx.spec).firstBlock⟩
  lastBlock : Sim.OptionBlockPtr.Sim ⟨RegionMPtr.readLastBlock! ctx.buf reg.toM, (reg.get! ctx.spec).lastBlock⟩
  parent : Sim.OptionOperationPtr.Sim ⟨RegionMPtr.readParent! ctx.buf reg.toM, (reg.get! ctx.spec).parent⟩

structure OperationPtr.MatchesBase (ctx : Sim.RawIRContext OpInfo) (op : OperationPtr) (ib : op.InBounds ctx.spec) where
  prev : Sim.OptionOperationPtr.Sim ⟨op.toM.readPrev! ctx.buf, (op.get! ctx.spec).prev⟩
  next : Sim.OptionOperationPtr.Sim ⟨op.toM.readNext! ctx.buf, (op.get! ctx.spec).next⟩
  parent : Sim.OptionBlockPtr.Sim ⟨op.toM.readParent! ctx.buf, (op.get! ctx.spec).parent⟩
  opType : (op.get! ctx.spec).opType = Operation.decodeOpInfo (op.toM.readOpType! ctx.buf)
  attrs : ctx.buf.attributes[op.toM.readAttrs! ctx.buf |>.toNat]? = some (op.get! ctx.spec).attrs
  -- TODO: properties

structure OperationPtr.MatchesResults (ctx : Sim.RawIRContext OpInfo) (op : OperationPtr) (ib : op.InBounds ctx.spec) where
  numResults : (op.get! ctx.spec).capResults = (op.toM.readNumResults! ctx.buf).toNat
  results (res : OpResultPtr) (hin : res.InBounds ctx.spec) : res.op = op → res.Matches ctx hin

structure OperationPtr.MatchesBlockOperands (ctx : Sim.RawIRContext OpInfo) (op : OperationPtr) (ib : op.InBounds ctx.spec) where
  numBlockOperands : (op.get! ctx.spec).capBlockOperands = (op.toM.readNumBlockOperands! ctx.buf).toNat
  blockOperands (bo : BlockOperandPtr) (hin : bo.InBounds ctx.spec) : bo.op = op → bo.Matches ctx hin

structure OperationPtr.MatchesRegions (ctx : Sim.RawIRContext OpInfo) (op : OperationPtr) where
  numRegions : (op.get! ctx.spec).capRegions = (op.toM.readNumRegions! ctx.buf).toNat
  regions (rg : RegionPtr) (hin : idx < (op.getNumRegions! ctx.spec)) :
    Sim.RegionPtr.Sim ⟨op.toM.readNthRegion! ctx.buf idx.toUInt64, op.getRegion! ctx.spec idx⟩

structure OperationPtr.MatchesOperands (ctx : Sim.RawIRContext OpInfo) (op : OperationPtr) where
  numOperands : (op.get! ctx.spec).capOperands = (op.toM.readNumOperands! ctx.buf).toNat
  operands (oper : OpOperandPtr) (hin : oper.InBounds ctx.spec) : oper.op = op → oper.Matches ctx hin

structure OperationPtr.Matches (ctx : Sim.RawIRContext OpInfo) (op : OperationPtr) (ib : op.InBounds ctx.spec) extends
  OperationPtr.MatchesBase ctx op ib,
  OperationPtr.MatchesBlockOperands ctx op ib,
  OperationPtr.MatchesRegions ctx op,
  OperationPtr.MatchesOperands ctx op,
  OperationPtr.MatchesResults ctx op ib

/-
TODO: this is not necessary: we only need to know
1. top-level allocs are not overlapping
2. composite pointers point inside the range of the top-level allocations.
-/
def GenericPtr.MayOverlap (ptr₁ ptr₂ : GenericPtr) : Prop :=
  match ptr₁, ptr₂ with
  | .operation ptr₁, .opOperand ptr₂ => ptr₁ = ptr₂.op
  | .opOperand ptr₁, .operation ptr₂ => ptr₁.op = ptr₂
  | .operation ptr₁, .opResult ptr₂ => ptr₁ = ptr₂.op
  | .opResult ptr₁, .operation ptr₂ => ptr₁.op = ptr₂
  | .blockOperand ptr₁, .operation ptr₂ => ptr₁.op = ptr₂
  | .operation ptr₁, .blockOperand ptr₂ => ptr₁ = ptr₂.op
  | .block ptr₁, .blockArgument ptr₂ => ptr₁ = ptr₂.block
  | .blockArgument ptr₁, .block ptr₂ => ptr₁.block = ptr₂
  | _, _ => False

inductive TopLevelPtr where
| operation (ptr : Veir.OperationPtr)
| block (ptr : Veir.BlockPtr)
| region (ptr : Veir.RegionPtr)

def TopLevelPtr.InBounds (ptr : TopLevelPtr) (ctx : IRContext OpInfo) : Prop :=
  match ptr with
  | .block ptr => ptr.InBounds ctx
  | .operation ptr => ptr.InBounds ctx
  | .region ptr => ptr.InBounds ctx

def TopLevelPtr.range (ptr : TopLevelPtr) (ctx : IRContext OpInfo) : Std.Rco Nat :=
  match ptr with
  | .operation op => op.range ctx
  | .block bl => bl.range ctx
  | .region rg => rg.range

namespace TopLevelPtr
section top_level_ptr

variable {ctx : IRContext OpInfo}

@[simp, grind _=_] theorem iff_block (ptr : BlockPtr) : (block ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind _=_] theorem iff_operation (ptr : OperationPtr) : (operation ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind _=_] theorem iff_region (ptr : RegionPtr) : (region ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]

end top_level_ptr
end TopLevelPtr

/-
TODO:
Actually I think `repr` can be deduced from `in_bounds`!
-/
structure Sim (ctx : Sim.RawIRContext OpInfo) where
  fieldsInBounds : ctx.spec.FieldsInBounds
  /-- All the values are representable. -/
  repr : ctx.spec.IsRepr
  /-- Allocated addresses do not go beyond the buffer size. -/
  in_bounds (ptr : TopLevelPtr) (ib : ptr.InBounds ctx.spec) :
    IsIncluded (ptr.range ctx.spec) ctx.buf.mem.range
  /-- The allocations are disjoint. -/
  disjoint_allocs (ptr₁ ptr₂ : TopLevelPtr) (ib₁ : ptr₁.InBounds ctx.spec) (ib₂ : ptr₂.InBounds ctx.spec) (hneq : ptr₁ ≠ ptr₂) :
    IsDisjoint (ptr₁.range ctx.spec) (ptr₂.range ctx.spec)
  /-- The buffer contains the encodings of all the operations. -/
  encoding_op (op : OperationPtr) (ib : op.InBounds ctx.spec) :
    op.Matches ctx ib
  /-- The buffer contains the encodings of all the blocks. -/
  encoding_block (blk : BlockPtr) (ib : blk.InBounds ctx.spec) :
    blk.Matches ctx ib
  /-- The buffer contains the encodings of all the regions. -/
  encoding_region (rg : RegionPtr) (ib : rg.InBounds ctx.spec) :
    rg.Matches ctx ib

variable (OpInfo) [HasOpInfo OpInfo] in
structure Sim.IRContext where
  buf : IRBufContext OpInfo
  spec : Veir.IRContext OpInfo
  sim : Sim ⟨buf, spec⟩

attribute [local grind =]
  Veir.OperationPtr.inBounds_def Veir.BlockPtr.inBounds_def Veir.RegionPtr.inBounds_def Veir.BlockArgumentPtr.inBounds_def
  Veir.OpOperandPtr.inBounds_def Veir.BlockOperandPtr.inBounds_def Veir.OpResultPtr.inBounds_def
attribute [local grind cases] ValuePtr.InBounds OpOperandPtrPtr.InBounds BlockOperandPtrPtr.InBounds
instance : Inhabited (Sim.IRContext OpInfo) where
  default := ⟨default, default, by
    constructor <;> simp
    · grind
    · simp only [IRContext.default_def]; grind
    all_goals
    · simp only [IRContext.default_def]
      intros ptr
      cases ptr <;> grind⟩

@[grind]
def Sim.IRContext.inner (ctx : IRContext OpInfo) : RawIRContext OpInfo := ⟨ctx.buf, ctx.spec⟩

@[grind .]
theorem Sim.IRContext.isRepr (ctx : IRContext OpInfo) : ctx.spec.IsRepr := ctx.sim.repr

@[grind! .]
theorem Sim.IRContext.fieldsInBounds (ctx : IRContext OpInfo) : ctx.spec.FieldsInBounds := ctx.sim.fieldsInBounds

end Veir
