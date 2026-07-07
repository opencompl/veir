module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Layout
public import Veir.Prelude
public import Veir.IR.Buffed.Layout
public import Veir.IR.Fields
public import Veir.IR.LayoutUnchanged

import all Veir.IR.Buffed.RawAccessors

open Veir.Buffed

public section

namespace Veir

variable [HasOpInfo OpInfo]

/-! ## Translate a high-level pointer to a flat address. -/

@[grind, layout_simp]
def OperationPtr.toFlat (ptr : OperationPtr) := ptr.id

@[grind, layout_simp]
def BlockPtr.toFlat (ptr : BlockPtr) := ptr.id

@[grind, layout_simp]
def RegionPtr.toFlat (ptr : RegionPtr) := ptr.id

def OpResultPtr.toFlat (ptr : OpResultPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.results ptr.op ctx).toInt).toNat +
  ptr.index * Buffed.OpResult.size.toNat
@[layout_grind, layout_simp]
def OpResultPtr.toFlatNat (ptr : OpResultPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.resultsInt ptr.op ctx)).toNat +
  ptr.index * Buffed.OpResult.sizeNat

def OpOperandPtr.toFlat (ptr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.operands ptr.op ctx).toInt).toNat +
  ptr.index * Buffed.OpOperand.size.toNat
@[layout_grind, layout_simp]
def OpOperandPtr.toFlatNat (ptr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.operandsInt ptr.op ctx)).toNat +
  ptr.index * Buffed.OpOperand.sizeNat

def BlockOperandPtr.toFlat (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.blockOperands ptr.op ctx).toInt).toNat +
  ptr.index * Buffed.BlockOperand.size.toNat
@[layout_grind, layout_simp]
def BlockOperandPtr.toFlatNat (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.blockOperandsInt ptr.op ctx)).toNat +
  ptr.index * Buffed.BlockOperand.sizeNat

def BlockArgumentPtr.toFlat (ptr : BlockArgumentPtr) :=
  (ptr.block.toFlat + Buffed.Block.Offsets.arguments.toInt).toNat +
  ptr.index * Buffed.BlockArgument.size.toNat
@[layout_grind, layout_simp]
def BlockArgumentPtr.toFlatNat (ptr : BlockArgumentPtr) :=
  (ptr.block.toFlat + Buffed.Block.Offsets.argumentsInt).toNat +
  ptr.index * Buffed.BlockArgument.sizeNat

def ValuePtr.toFlat (ptr : ValuePtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .opResult ptr => ptr.toFlat ctx
  | .blockArgument ptr => ptr.toFlat
@[layout_grind, layout_simp]
def ValuePtr.toFlatNat (ptr : ValuePtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .opResult ptr => ptr.toFlatNat ctx
  | .blockArgument ptr => ptr.toFlatNat

def OpOperandPtrPtr.toFlat (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse ptr => ptr.toFlat ctx + Buffed.OpOperand.Offsets.nextUse.toInt.toNat
  | .valueFirstUse ptr => ptr.toFlat ctx + Buffed.ValueImpl.Offsets.firstUse.toInt.toNat
@[layout_grind, layout_simp]
def OpOperandPtrPtr.toFlatNat (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse ptr => ptr.toFlatNat ctx + Buffed.OpOperand.Offsets.nextUseInt.toNat
  | .valueFirstUse ptr => ptr.toFlatNat ctx + Buffed.ValueImpl.Offsets.firstUseInt.toNat

def BlockOperandPtrPtr.toFlat (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse ptr => ptr.toFlat ctx + Buffed.BlockOperand.Offsets.nextUse.toInt.toNat
  | .blockFirstUse ptr => ptr.toFlat + Buffed.Block.Offsets.firstUse.toInt.toNat
@[layout_grind, layout_simp]
def BlockOperandPtrPtr.toFlatNat (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse ptr => ptr.toFlatNat ctx + Buffed.BlockOperand.Offsets.nextUseInt.toNat
  | .blockFirstUse ptr => ptr.toFlat + Buffed.Block.Offsets.firstUseInt.toNat

/-! ## A pointer is representable if it fits in 63 bits. -/

@[grind] def OperationPtr.IsRepr (ptr : OperationPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind] def BlockPtr.IsRepr (ptr : BlockPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind] def RegionPtr.IsRepr (ptr : RegionPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

/-! ## Translate a high-level pointer to a buffed address. -/

@[layout_grind]
def OperationPtr.toM (ptr : OperationPtr) : OperationMPtr := ptr.toFlat.toUInt64
@[layout_grind, layout_simp]
def OperationPtr.toO (ptr : Option OperationPtr) : OperationOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

@[layout_grind, layout_simp]
def BlockPtr.toM (ptr : BlockPtr) : BlockMPtr := ptr.toFlat.toUInt64
@[layout_grind, layout_simp]
def BlockPtr.toO (ptr : Option BlockPtr) : BlockOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

@[layout_grind, layout_simp]
def RegionPtr.toM (ptr : RegionPtr) : RegionMPtr := ptr.toFlat.toUInt64
@[layout_grind, layout_simp]
def RegionPtr.toO (ptr : Option RegionPtr) : RegionOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

@[layout_grind, layout_simp]
def OpResultPtr.toM (ptr : OpResultPtr) (ctx : IRContext OpInfo) : OpResultMPtr :=
  (ptr.toFlat ctx).toUInt64
@[layout_grind, layout_simp]
def OpResultPtr.toO (ptr : Option OpResultPtr) (ctx : IRContext OpInfo) : OpResultOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

@[layout_grind, layout_simp]
def BlockArgumentPtr.toM (ptr : BlockArgumentPtr) : BlockArgumentMPtr :=
  ptr.toFlat.toUInt64
@[layout_grind, layout_simp]
def BlockArgumentPtr.toO (ptr : Option BlockArgumentPtr) : BlockArgumentOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

@[layout_grind, layout_simp]
def OpOperandPtr.toM (ptr : OpOperandPtr) (ctx : IRContext OpInfo) : OpOperandMPtr :=
  (ptr.toFlat ctx).toUInt64
@[layout_grind, layout_simp]
def OpOperandPtr.toO (ptr : Option OpOperandPtr) (ctx : IRContext OpInfo) : OpOperandOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

@[layout_grind, layout_simp]
def BlockOperandPtr.toM (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperandMPtr :=
  (ptr.toFlat ctx).toUInt64
@[layout_grind, layout_simp]
def BlockOperandPtr.toO (ptr : Option BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperandOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

@[layout_grind, layout_simp]
def ValuePtr.toM (ptr : ValuePtr) (ctx : IRContext OpInfo) : ValueImplMPtr :=
  (ptr.toFlat ctx).toUInt64
@[layout_grind, layout_simp]
def ValuePtr.toO (ptr : Option ValuePtr) (ctx : IRContext OpInfo) : ValueImplOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

@[simp, grind =]
theorem ValuePtr.toM_opResult {ctx : IRContext OpInfo} : (ValuePtr.opResult res).toM ctx = res.toM ctx := by rfl

@[simp, grind =]
theorem ValuePtr.toM_blockArgument {ctx : IRContext OpInfo} : (ValuePtr.blockArgument arg).toM ctx = arg.toM := by rfl

@[layout_grind, layout_simp]
def OpOperandPtrPtr.toM (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  (ptr.toFlat ctx).toUInt64

@[layout_grind, layout_simp]
def BlockOperandPtrPtr.toM (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  (ptr.toFlat ctx).toUInt64

@[layout_grind, layout_simp]
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

@[layout_grind, layout_simp]
def GenericPtr.toO (ptr : Option GenericPtr) (ctx : IRContext OpInfo) : GenericOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

/-! ## Range of a pointer -/

def OperationPtr.range (op : OperationPtr) (ctx : IRContext OpInfo) :=
  op.toFlat + (Buffed.Operation.range op ctx)

abbrev OperationPtr.rangeInt (op : OperationPtr) (ctx : IRContext OpInfo) :=
  op.toFlat + (Buffed.Operation.rangeInt op ctx)

def BlockPtr.range (bl : BlockPtr) (ctx : IRContext OpInfo) :=
  bl.toFlat + Buffed.Block.range bl ctx

@[layout_grind, layout_simp]
def BlockPtr.rangeInt (bl : BlockPtr) (ctx : IRContext OpInfo) :=
  bl.toFlat + Buffed.Block.rangeInt bl ctx

def RegionPtr.range (rg : RegionPtr) :=
  rg.toFlat + Buffed.Region.range

@[layout_grind, layout_simp]
def RegionPtr.rangeInt (rg : RegionPtr) :=
  rg.toFlat + Buffed.Region.rangeInt

def OpResultPtr.range (res : OpResultPtr) (ctx : IRContext OpInfo) :=
  res.toFlat ctx + Buffed.OpResult.range

@[layout_grind, layout_simp]
def OpResultPtr.rangeInt (res : OpResultPtr) (ctx : IRContext OpInfo) :=
  res.toFlatNat ctx + Buffed.OpResult.rangeInt

def BlockArgumentPtr.range (arg : BlockArgumentPtr) :=
  arg.toFlat + Buffed.BlockArgument.range

@[layout_grind, layout_simp]
def BlockArgumentPtr.rangeInt (arg : BlockArgumentPtr) :=
  arg.toFlatNat + Buffed.BlockArgument.rangeInt

def OpOperandPtr.range (opr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlat ctx + Buffed.OpOperand.range

@[layout_grind, layout_simp]
def OpOperandPtr.rangeInt (opr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlatNat ctx + Buffed.OpOperand.rangeInt

def BlockOperandPtr.range (opr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlat ctx + Buffed.BlockOperand.range

@[layout_grind, layout_simp]
def BlockOperandPtr.rangeInt (opr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlatNat ctx + Buffed.BlockOperand.rangeInt

def ValuePtr.range (val : ValuePtr) (ctx : IRContext OpInfo) :=
  match val with
  | .opResult res => res.range ctx
  | .blockArgument arg => arg.range

@[layout_grind, layout_simp]
def ValuePtr.rangeInt (val : ValuePtr) (ctx : IRContext OpInfo) :=
  match val with
  | .opResult res => res.rangeInt ctx
  | .blockArgument arg => arg.rangeInt

def OpOperandPtrPtr.range (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse opr => opr.range ctx
  | .valueFirstUse val => val.range ctx

@[layout_grind, layout_simp]
def OpOperandPtrPtr.rangeInt (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse opr => opr.rangeInt ctx
  | .valueFirstUse val => val.rangeInt ctx

def BlockOperandPtrPtr.range (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse opr => opr.range ctx
  | .blockFirstUse bl => bl.range ctx

@[layout_grind, layout_simp]
def BlockOperandPtrPtr.rangeInt (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse opr => opr.rangeInt ctx
  | .blockFirstUse bl => bl.rangeInt ctx

def GenericPtr.range (ptr : GenericPtr) (ctx : IRContext OpInfo) : Std.Rco Int :=
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

@[layout_grind, layout_simp]
def GenericPtr.rangeInt (ptr : GenericPtr) (ctx : IRContext OpInfo) : Std.Rco Int :=
  match ptr with
  | .operation op => op.rangeInt ctx
  | .block bl => bl.rangeInt ctx
  | .region rg => rg.rangeInt
  | .opResult res => res.rangeInt ctx
  | .opOperand opr => opr.rangeInt ctx
  | .blockOperand opr => opr.rangeInt ctx
  | .blockOperandPtr ptr => ptr.rangeInt ctx
  | .blockArgument arg => arg.rangeInt
  | .value val => val.rangeInt ctx
  | .opOperandPtr ptr => ptr.rangeInt ctx

/-! ### Range and LayoutUnchanged -/

@[grind ., simp]
theorem LayoutPreserved.same_operationPtr_range {ctx ctx' : IRContext OpInfo} (ptr : OperationPtr) (ptrIb : ptr.InBounds ctx) :
    ctx.LayoutPreserved ctx' → ptr.range ctx = ptr.range ctx' := by
  simp only [OperationPtr.range]
  cbv
  intros lu
  cases lu.ops ptr ptrIb
  simp [*]

@[grind ., simp]
theorem LayoutPreserved.same_blockPtr_range {ctx ctx' : IRContext OpInfo} (ptr : BlockPtr) (ptrIb : ptr.InBounds ctx) :
    ctx.LayoutPreserved ctx' → ptr.range ctx = ptr.range ctx' := by
  simp only [BlockPtr.range]
  cbv
  intros lu
  have := lu.blocks ptr ptrIb
  unfold BlockPtr.LayoutPreserved at this
  simp [*]

/-! ## An object is representable if all its fields are representable. -/

@[grind]
structure Operation.ReprIndices (val : OperationPtr) (ctx : IRContext OpInfo) where
  results : (val.get! ctx).capResults ≤ countCard
  operands : (val.get! ctx).capOperands ≤ countCard
  blockOperands : (val.get! ctx).capBlockOperands ≤ countCard
  regions : (val.get! ctx).capRegions ≤ countCard
  capResults : val.getNumResults! ctx ≤ (val.get! ctx).capResults
  capOperands : val.getNumOperands! ctx ≤ (val.get! ctx).capOperands
  capBlockOperands : val.getNumSuccessors! ctx ≤ (val.get! ctx).capBlockOperands
  capRegions : val.getNumRegions! ctx ≤ (val.get! ctx).capRegions

@[grind]
structure Block.ReprIndices (val : BlockPtr) (ctx : IRContext OpInfo) where
  arguments : (val.get! ctx).capArguments ≤ countCard
  capArguments : val.getNumArguments! ctx ≤ (val.get! ctx).capArguments

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

@[unfold_pointers]
structure Sim.OperationPtr where
  impl : OperationMPtr
  spec : Veir.OperationPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.OptionOperationPtr where
  impl : OperationOPtr
  spec : Option Veir.OperationPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.BlockPtr where
  impl : BlockMPtr
  spec : Veir.BlockPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.OptionBlockPtr where
  impl : BlockOPtr
  spec : Option Veir.BlockPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.RegionPtr where
  impl : RegionMPtr
  spec : Veir.RegionPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.OptionRegionPtr where
  impl : RegionOPtr
  spec : Option Veir.RegionPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.OpResultPtr where
  impl : OpResultMPtr
  spec : Veir.OpResultPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.BlockArgumentPtr where
  impl : BlockArgumentMPtr
  spec : Veir.BlockArgumentPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.OpOperandPtr where
  impl : OpOperandMPtr
  spec : Veir.OpOperandPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.OptionOpOperandPtr where
  impl : OpOperandOPtr
  spec : Option Veir.OpOperandPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.OptionOpResultPtr where
  impl : OpResultOPtr
  spec : Option Veir.OpResultPtr

@[unfold_pointers]
structure Sim.BlockOperandPtr where
  impl : BlockOperandMPtr
  spec : Veir.BlockOperandPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.OptionBlockOperandPtr where
  impl : BlockOperandOPtr
  spec : Option Veir.BlockOperandPtr
deriving Inhabited

@[unfold_pointers]
structure Sim.ValuePtr where
  impl : ValueImplMPtr
  spec : Veir.ValuePtr
deriving Inhabited

structure Sim.OpOperandPtrPtr where
  impl : OpOperandPtrMPtr
  spec : Veir.OpOperandPtrPtr
deriving Inhabited

structure Sim.OptionBlockArgumentPtr where
  impl : BlockArgumentOPtr
  spec : Option Veir.BlockArgumentPtr

structure Sim.BlockOperandPtrPtr where
  impl : BlockOperandPtrMPtr
  spec : Veir.BlockOperandPtrPtr
deriving Inhabited

structure Sim.OptionValuePtr where
  impl : ValueImplOPtr
  spec : Option Veir.ValuePtr

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
  opType : op.getOpType! ctx.spec = Operation.decodeOpInfo (op.toM.readOpType! ctx.buf)
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
  regions  idx (hin : idx < (op.getNumRegions! ctx.spec)) :
    Sim.RegionPtr.Sim ⟨op.toM.readNthRegion! ctx.buf idx.toUInt64, op.getRegion! ctx.spec idx⟩

structure OperationPtr.MatchesOperands (ctx : Sim.RawIRContext OpInfo) (op : OperationPtr) where
  numOperands : (op.get! ctx.spec).capOperands = (op.toM.readNumOperands! ctx.buf).toNat
  operands (oper : OpOperandPtr) (hin : oper.InBounds ctx.spec) : oper.op = op → oper.Matches ctx hin

structure OperationPtr.Capacities (ctx : IRContext OpInfo) (op : OperationPtr) where

structure OperationPtr.Matches (ctx : Sim.RawIRContext OpInfo) (op : OperationPtr) (ib : op.InBounds ctx.spec) extends
  OperationPtr.MatchesBase ctx op ib,
  OperationPtr.MatchesBlockOperands ctx op ib,
  OperationPtr.MatchesRegions ctx op,
  OperationPtr.MatchesOperands ctx op,
  OperationPtr.MatchesResults ctx op ib,
  OperationPtr.Capacities ctx.spec op

@[simp, grind]
def TopLevelPtr.range (ptr : TopLevelPtr) (ctx : IRContext OpInfo) : Std.Rco Int :=
  match ptr with
  | .operation op => op.range ctx
  | .block bl => bl.range ctx
  | .region rg => rg.range

structure Sim (ctx : Sim.RawIRContext OpInfo) where
  /-- All the fields are in bounds -/
  fieldsInBounds : ctx.spec.FieldsInBounds
  /-- All the values are representable. -/
  repr : ctx.spec.IsRepr
  /-- Allocated addresses do not go beyond the buffer size. -/
  in_bounds (ptr : TopLevelPtr) (ib : ptr.InBounds ctx.spec) :
    IsIncludedIN (ptr.range ctx.spec) ctx.buf.mem.range
  /-- The allocations are disjoint. -/
  disjoint_allocs (ptr₁ ptr₂ : TopLevelPtr) (ib₁ : ptr₁.InBounds ctx.spec) (ib₂ : ptr₂.InBounds ctx.spec) (hneq : ptr₁ ≠ ptr₂) :
    IsDisjointI (ptr₁.range ctx.spec) (ptr₂.range ctx.spec)
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

-- A bunch of lemmas, we should move them at some point.

axiom Operation.propertySize_lt (oi : OpInfo) : (Operation.propertySize oi).toNat < UInt32.size

@[grind .] theorem Operation.propertySize_pos  (oi : OpInfo) : 0 ≤ (Operation.propertySize oi).toInt64.toInt := by sorry
@[grind .] theorem Operation.propertySize_lt_Int (oi : OpInfo) : (Operation.propertySize oi).toInt64.toInt < 4294967296 := by sorry

theorem _root_.UInt64.toNat_add_of_le_size (x y : UInt64) (hle : x.toNat + y.toNat < UInt64.size) : (x + y).toNat = x.toNat + y.toNat := by
  exact UInt64.add_toNat_lt hle

section operation_sizes_and_offsets

@[simp, grind =]
theorem Buffed.Operation.Sizes.results_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (op : OperationPtr) (ib : op.InBounds ctx) :
    (Sizes.results op ctx).toNat = Sizes.resultsNat op ctx := by
  have := repr.operations_indices op (by grind) |>.results
  simp
  grind

@[simp, grind =]
theorem Buffed.Operation.Sizes.properties_ideal {ctx : IRContext OpInfo} (op : OperationPtr) :
    (Sizes.properties op ctx).toNat = Sizes.propertiesNat op ctx := by
  rfl

@[simp, grind =]
theorem Buffed.Operation.Sizes.blockOperands_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (op : OperationPtr) (ib : op.InBounds ctx) :
    (Sizes.blockOperands op ctx).toNat = Sizes.blockOperandsNat op ctx := by
  have := repr.operations_indices op (by grind) |>.results
  simp
  grind

@[simp, grind =]
theorem Buffed.Operation.Sizes.regions_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (op : OperationPtr) (ib : op.InBounds ctx) :
    (Sizes.regions op ctx).toNat = Sizes.regionsNat op ctx := by
  have := repr.operations_indices op (by grind) |>.results
  simp
  grind

@[simp, grind =]
theorem Buffed.Operation.Sizes.operands_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (op : OperationPtr) (ib : op.InBounds ctx) :
    (Sizes.operands op ctx).toNat = Sizes.operandsNat op ctx := by
  have := repr.operations_indices op (by grind) |>.results
  simp
  grind

@[simp, grind _=_]
theorem Buffed.Operation.Sizes.sizeBase_ideal :
    Operation.sizeBase.toNat = Operation.sizeBaseNat := rfl

@[simp, grind =]
theorem Buffed.Operation.Sizes.size_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (op : OperationPtr) (ib : op.InBounds ctx) :
    (Operation.size op ctx).toNat = Operation.sizeNat op ctx := by
  have := @Operation.propertySize_lt
  grind

@[grind =]
theorem Int64.add_toInt_lt {a b : Int64} (h₁ : a.toInt + b.toInt < Int64.maxValue.toInt) (h₁ : Int64.minValue.toInt < a.toInt + b.toInt) :
    ((a + b).toInt = a.toInt + b.toInt) := by
  simp only [Int64.toInt_add, Nat.reducePow]
  grind

@[grind =]
theorem Int64.add_toInt_lt' {a : Int64} {b : UInt64} (h : b.toNat < Int64.maxNatValue) (h₁ : a.toInt + b.toNat < Int64.maxValue.toInt) (h₂ : Int64.minValue.toInt < a.toInt + b.toNat) :
    ((a + b).toInt = a.toInt + b.toNat) := by
  rw [UInt64.add_int64_l_def]
  have : b.toInt64.toInt = b.toNat := by
    unfold UInt64.toInt64 Int64.toInt UInt64.toNat Int64.toBitVec at *
    grind
  grind [add_toInt_lt]

@[grind =]
theorem UInt64.uint64_add_int64_toInt_lt {a : UInt64} {b : Int64}
  (hnneg : 0 ≤ a.toNat + b.toInt)
  (hxx : a.toNat < Int64.maxValue.toInt) :
    ((a + b).toInt = a.toNat + b.toInt) := by
  rcases b with ⟨b⟩
  have : a.toNat < 2^64 := UInt64.toNat_lt a
  have : b.toNat < 2^64 := UInt64.toNat_lt b
  rw [UInt64.add_int64_r_def]
  rw [Int64.toUInt64_add]
  simp
  simp only [Int64.toInt]
  rw [Int64.toBitVec]
  simp only
  rw [UInt64.toInt]
  rw [UInt64.toNat]
  simp
  by_cases hlt : ↑a.toNat + ↑b.toNat < 2 ^ 64
  · simp_all
    rw [Int.emod_eq_of_lt]
    · congr
      rw [UInt64.toNat]
      rw [Int64.toInt] at *
      rw [Int64.toBitVec] at *
      simp at *
      rw [BitVec.toInt_eq_toNat_cond]
      split
      · rfl
      · grind [UInt64.toNat]
    · grind
    · grind
  · rw [← Int.sub_emod_right]
    rw [Int.emod_eq_of_lt]
    · rw [BitVec.toInt_eq_toNat_cond]
      have : b.toBitVec.toNat = b.toNat := by rfl
      grind
    · grind
    · have : b.toBitVec.toNat = b.toNat := by rfl
      grind

@[grind =]
theorem UInt64.uint64_add_int64_toNat_lt {a : UInt64} {b : Int64}
  (hnneg : 0 ≤ a.toNat + b.toInt)
  (h₁ : a.toNat < Int64.maxValue.toInt) :
    (a + b).toNat = (a.toNat + b.toInt).toNat := by
  rw [UInt64.add_int64_r_def]
  rw [Int64.toUInt64_add]
  simp only [UInt64.toUInt64_toInt64]
  rw [← UInt64.uint64_add_int64_toInt_lt]
  · rfl
  · grind
  · grind


@[simp, grind =]
theorem Buffed.Operation.Offsets.results_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (op : OperationPtr) (ib : op.InBounds ctx) :
    (Offsets.results op ctx).toInt = Offsets.resultsInt op ctx := by
  have := repr.operations_indices op (by grind) |>.results
  simp [UInt64.add_int64_l_def]
  grind

@[simp, grind =]
theorem Buffed.Operation.Offsets.properties_ideal :
    Offsets.properties.toInt = Offsets.propertiesInt := by
  rfl

@[simp, grind =]
theorem Buffed.Operation.Offsets.operands_ideal {ctx : IRContext OpInfo} (op : OperationPtr) :
    (Offsets.operands op ctx).toInt = Offsets.operandsInt op ctx := by
  have := Operation.propertySize_lt (op.getOpType! ctx)
  unfold operands operandsInt
  grind

@[layout_simp, grind =]
theorem Buffed.Operation.Offsets.blockOperands_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (op : OperationPtr) (ib : op.InBounds ctx) :
    (Offsets.blockOperands op ctx).toInt = Offsets.blockOperandsInt op ctx := by
  have := Operation.propertySize_lt (op.getOpType! ctx)
  have := repr.operations_indices op (by grind) |>.results
  unfold blockOperands blockOperandsInt
  rw [Int64.add_toInt_lt'] <;> (try rw [operands_ideal]) <;> grind

@[simp, grind =]
theorem Buffed.Operation.Offsets.regions_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (op : OperationPtr) (ib : op.InBounds ctx) :
    (Offsets.regions op ctx).toInt = Offsets.regionsInt op ctx := by
  have := Operation.propertySize_lt (op.getOpType! ctx)
  have := repr.operations_indices op (by grind) |>.results
  unfold regions regionsInt
  rw [Int64.add_toInt_lt'] <;> (try rw [blockOperands_ideal]) <;> grind


@[simp, grind =]
theorem Buffed.Operation.Offsets.after_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (op : OperationPtr) (ib : op.InBounds ctx) :
    (Offsets.after op ctx).toInt = Offsets.afterInt op ctx := by
  have := Operation.propertySize_lt (op.getOpType! ctx)
  unfold after afterInt
  rw [Int64.add_toInt_lt'] <;> (try rw [regions_ideal]) <;> grind

end operation_sizes_and_offsets

section block_sizes_and_offsets

@[simp, grind =]
theorem Buffed.Block.Sizes.arguments_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {bl : BlockPtr} (ib : bl.InBounds ctx) :
    (Sizes.arguments bl ctx).toNat = Sizes.argumentsNat bl ctx := by
  have := repr.blocks_indices bl (by grind) |>.arguments
  simp
  grind

@[simp, grind _=_]
theorem Buffed.Block.Sizes.sizeBase_ideal :
    Block.sizeBase.toNat = Block.sizeBaseNat := rfl

@[simp, grind =]
theorem Buffed.Block.Sizes.size_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (bl : BlockPtr) (ib : bl.InBounds ctx) :
    (Block.size bl ctx).toNat = Block.sizeNat bl ctx := by
  have := repr.blocks_indices bl (by grind) |>.arguments
  grind

@[simp, grind =]
theorem Buffed.Block.Offsets.after_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (bl : BlockPtr) (ib : bl.InBounds ctx) :
    (Offsets.after bl ctx).toInt = Offsets.afterInt bl ctx := by
  have := repr.blocks_indices bl (by grind) |>.arguments
  unfold after afterInt
  grind

end block_sizes_and_offsets

section compute_ideal

@[simp, grind =]
theorem OperationPtr.computeOperationSize_ideal
    (_ : numResults.toNat < countCard)
    (_ : numOperands.toNat < countCard)
    (_ : numBlockOperands.toNat < countCard)
    (_ : numRegions.toNat < countCard)
    (_ : propSize.toNat < countCard) :
  (Buffed.OperationMPtr.computeOperationSize numResults numOperands numBlockOperands numRegions propSize).toNat =
    Operation.sizeBaseNat + propSize.toNat +
    (OpResult.sizeNat * numResults.toNat) + (OpOperand.sizeNat * numOperands.toNat) +
    (BlockOperand.sizeNat * numBlockOperands.toNat) + (ptrSizeNat * numRegions.toNat) := by
  simp [Buffed.OperationMPtr.computeOperationSize]
  grind
-- TODO: BlockMPtr.computeBlockSize

theorem OperationPtr.computeOperandOffset_eq (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim) h :
    op.impl.computeOperandsOffset ctx.buf h = Operation.Offsets.operands op.spec ctx.spec := by
  have hop := ctx.sim.encoding_op op.spec hib
  simp only [Sim.OperationPtr.Sim] at hsim
  simp [Veir.Buffed.OperationMPtr.computeOperandsOffset, Operation.Offsets.operands, Operation.Offsets.properties]
  rw [← hsim, ← hop.opType]

@[layout_simp, layout_grind =]
theorem OperationPtr.computeOperandOffset_ideal (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim) h :
    (op.impl.computeOperandsOffset ctx.buf h).toInt = Operation.Offsets.operandsInt op.spec ctx.spec := by
  rw [OperationPtr.computeOperandOffset_eq ctx op hib hsim, Buffed.Operation.Offsets.operands_ideal]

theorem OperationPtr.computeResultsOffset_eq (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim) h :
    op.impl.computeResultsOffset ctx.buf h = Operation.Offsets.results op.spec ctx.spec := by
  have hnum := ctx.sim.encoding_op op.spec hib |>.numResults
  simp only [Sim.OperationPtr.Sim] at hsim
  simp only [Veir.Buffed.OperationMPtr.computeResultsOffset, Operation.Offsets.results,
    Operation.Sizes.results, OperationMPtr.readNumResults_eq_readNumResults!]
  grind [UInt64.add_int64_l_def, UInt64.toInt64_mul, Int64.neg_mul, Int64.zero_add]

@[layout_simp, layout_grind =]
theorem OperationPtr.computeResultsOffset_ideal (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim) h :
    (op.impl.computeResultsOffset ctx.buf h).toInt = Operation.Offsets.resultsInt op.spec ctx.spec := by
  rw [OperationPtr.computeResultsOffset_eq ctx op hib hsim,
    Buffed.Operation.Offsets.results_ideal ctx.isRepr _ hib]

theorem OperationPtr.computeBlockOperandsOffset_eq (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim) h :
    op.impl.computeBlockOperandsOffset ctx.buf h = Operation.Offsets.blockOperands op.spec ctx.spec := by
  have hop := ctx.sim.encoding_op op.spec hib |>.numOperands
  simp only [Veir.Buffed.OperationMPtr.computeBlockOperandsOffset, Operation.Offsets.blockOperands]
  rw [OperationPtr.computeOperandOffset_eq ctx op hib hsim]
  congr 1
  simp only [Operation.Sizes.operands, OperationMPtr.readNumOperands_eq_readNumOperands!]
  grind

@[layout_simp, layout_grind =]
theorem OperationPtr.computeBlockOperandsOffset_ideal (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim) h :
    (op.impl.computeBlockOperandsOffset ctx.buf h).toInt = Operation.Offsets.blockOperandsInt op.spec ctx.spec := by
  rw [OperationPtr.computeBlockOperandsOffset_eq ctx op hib hsim,
    Buffed.Operation.Offsets.blockOperands_ideal ctx.isRepr _ hib]

theorem OperationPtr.computeRegionsOffset_eq (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim) h :
    op.impl.computeRegionsOffset ctx.buf h = Operation.Offsets.regions op.spec ctx.spec := by
  have hop := ctx.sim.encoding_op op.spec hib |>.numBlockOperands
  simp only [Sim.OperationPtr.Sim] at hsim
  simp only [Veir.Buffed.OperationMPtr.computeRegionsOffset, Operation.Offsets.regions]
  rw [OperationPtr.computeBlockOperandsOffset_eq ctx op hib hsim]
  congr 1
  grind

@[layout_simp, layout_grind =]
theorem OperationPtr.computeRegionsOffset_ideal (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim) h :
    (op.impl.computeRegionsOffset ctx.buf h).toInt = Operation.Offsets.regionsInt op.spec ctx.spec := by
  rw [OperationPtr.computeRegionsOffset_eq ctx op hib hsim,
    Buffed.Operation.Offsets.regions_ideal ctx.isRepr _ hib]

/-! Bang versions -/

@[layout_simp, layout_grind =]
theorem OperationPtr.computeOperandsOffset!_ideal (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim)
    (h : (op.impl + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤ ctx.buf.size) :
    (op.impl.computeOperandsOffset! ctx.buf).toInt = Operation.Offsets.operandsInt op.spec ctx.spec := by
  rw [← OperationMPtr.computeOperandsOffset_eq_computeOperandsOffset! (h := h)]
  exact OperationPtr.computeOperandOffset_ideal ctx op hib hsim h

@[layout_simp, layout_grind =]
theorem OperationPtr.computeResultsOffset!_ideal (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim)
    (h : (op.impl + Operation.Offsets.numResults).toInt + Operation.Sizes.numResults.toInt ≤ ctx.buf.size) :
    (op.impl.computeResultsOffset! ctx.buf).toInt = Operation.Offsets.resultsInt op.spec ctx.spec := by
  rw [← OperationMPtr.computeResultsOffset_eq_computeResultsOffset! (h := h)]
  exact OperationPtr.computeResultsOffset_ideal ctx op hib hsim h

@[layout_simp, layout_grind =]
theorem OperationPtr.computeBlockOperandsOffset!_ideal (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim)
    (h : (op.impl + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ ctx.buf.size) :
    (op.impl.computeBlockOperandsOffset! ctx.buf).toInt = Operation.Offsets.blockOperandsInt op.spec ctx.spec := by
  rw [← OperationMPtr.computeBlockOperandsOffset_eq_computeBlockOperandsOffset! (h := h)]
  exact OperationPtr.computeBlockOperandsOffset_ideal ctx op hib hsim h

@[layout_simp, layout_grind =]
theorem OperationPtr.computeRegionsOffset!_ideal (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim)
    (h : (op.impl + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ ctx.buf.size) :
    (op.impl.computeRegionsOffset! ctx.buf).toInt = Operation.Offsets.regionsInt op.spec ctx.spec := by
  rw [← OperationMPtr.computeRegionsOffset_eq_computeRegionsOffset! (h := h)]
  exact OperationPtr.computeRegionsOffset_ideal ctx op hib hsim h

theorem BlockPtr.computeArgumentOffset_eq (idx : UInt64) :
    BlockMPtr.computeArgumentOffset idx = Block.Offsets.arguments + BlockArgument.size * idx := by
  simp [Veir.Buffed.BlockMPtr.computeArgumentOffset]

theorem BlockPtr.computeArgumentOffset_ideal (ctx : Sim.IRContext OpInfo) (bl : Sim.BlockPtr) (idx : UInt64)
    (hib : bl.spec.InBounds ctx.spec) (hidx : idx.toNat < (bl.spec.get! ctx.spec).capArguments) :
    (BlockMPtr.computeArgumentOffset idx).toInt =
      Block.Offsets.argumentsInt + BlockArgument.sizeNat * idx.toNat := by
  have hcap := ctx.isRepr.blocks_indices bl.spec (by grind) |>.arguments
  have hidx' : idx.toNat < 4294967296 := by simp only [countCard, UInt32.size] at hcap; omega
  have hmul : (BlockArgument.size * idx).toNat = BlockArgument.sizeNat * idx.toNat := by
    rw [UInt64.toNat_mul, show BlockArgument.size.toNat = 32 from rfl,
      show BlockArgument.sizeNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
  rw [BlockPtr.computeArgumentOffset_eq]
  unfold Block.Offsets.arguments Block.Offsets.argumentsInt
  rw [Int64.add_toInt_lt'] <;> grind

end compute_ideal

/-! ### toFlat -/

@[layout_simp, layout_grind =]
theorem OpResultPtr.toFlat_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (res : OpResultPtr) (ib : res.InBounds ctx) :
    res.toFlat ctx = res.toFlatNat ctx := by
  have := repr.operations_indices res.op (by grind) |>.results
  unfold toFlat toFlatNat
  unfold Operation.Offsets.results
  unfold Operation.Sizes.results
  unfold Operation.Offsets.resultsInt
  unfold Operation.Sizes.resultsNat
  simp [UInt64.add_int64_l_def]
  grind

@[layout_simp, layout_grind =]
theorem OpOperandPtr.toFlat_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (oper : OpOperandPtr) (ib : oper.InBounds ctx) :
    oper.toFlat ctx = oper.toFlatNat ctx := by
  have := repr.operations_indices oper.op (by grind) |>.operands
  unfold toFlat toFlatNat
  grind

@[layout_simp, layout_grind =]
theorem BlockOperandPtr.toFlat_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (oper : BlockOperandPtr) (ib : oper.InBounds ctx) :
    oper.toFlat ctx = oper.toFlatNat ctx := by
  have := repr.operations_indices oper.op (by grind) |>.blockOperands
  unfold toFlat toFlatNat
  rw [Buffed.Operation.Offsets.blockOperands_ideal] <;> grind

@[layout_simp, grind .]
theorem BlockArgumentPtr.toFlat_ideal (arg : BlockArgumentPtr) :
    arg.toFlat = arg.toFlatNat := by
  unfold toFlat toFlatNat
  grind

@[layout_simp, layout_grind =]
theorem ValuePtr.toFlat_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (val : ValuePtr) (ib : val.InBounds ctx) :
    val.toFlat ctx = val.toFlatNat ctx := by
  cases val with
  | opResult ptr => simpa [toFlat, toFlatNat] using ptr.toFlat_ideal repr (by grind)
  | blockArgument ptr => simpa [toFlat, toFlatNat] using ptr.toFlat_ideal

@[layout_simp, layout_grind =]
theorem OpOperandPtrPtr.toFlat_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (ptr : OpOperandPtrPtr) (ib : ptr.InBounds ctx) :
    ptr.toFlat ctx = ptr.toFlatNat ctx := by
  cases ptr with
  | operandNextUse ptr => simp [toFlat, toFlatNat, ptr.toFlat_ideal repr (by grind)]
  | valueFirstUse ptr => simp only [toFlat, toFlatNat, ptr.toFlat_ideal repr (by grind)]; rfl

@[layout_simp, layout_grind =]
theorem BlockOperandPtrPtr.toFlat_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) (ptr : BlockOperandPtrPtr) (ib : ptr.InBounds ctx) :
    ptr.toFlat ctx = ptr.toFlatNat ctx := by
  cases ptr with
  | blockOperandNextUse ptr => simp [toFlat, toFlatNat, ptr.toFlat_ideal repr (by grind)]
  | blockFirstUse ptr => simp [toFlat, toFlatNat]

/-! ### Ranges -/

@[layout_simp, grind =]
theorem OperationPtr.range_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {op : OperationPtr} (ib : op.InBounds ctx) :
    op.range ctx = op.rangeInt ctx := by
  unfold range rangeInt
  congr
  unfold Operation.range Operation.rangeInt
  congr
  · grind only [= Operation.Offsets.results_ideal]
  · grind only [= Operation.Offsets.after_ideal]

@[layout_simp, grind =]
theorem OpOperandPtr.range_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {op : OpOperandPtr} (ib : op.InBounds ctx) :
    op.range ctx = op.rangeInt ctx := by
  unfold range rangeInt
  congr
  grind [layout_grind]

@[layout_simp, grind =]
theorem OpResultPtr.range_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {op : OpResultPtr} (ib : op.InBounds ctx) :
    op.range ctx = op.rangeInt ctx := by
  unfold range rangeInt
  congr
  grind [layout_grind]

@[layout_simp, grind =]
theorem BlockArgumentPtr.range_ideal {op : BlockArgumentPtr} :
    op.range = op.rangeInt := by
  simp only [range, rangeInt, op.toFlat_ideal]
  congr 1

@[layout_simp, grind =]
theorem BlockOperandPtr.range_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {op : BlockOperandPtr} (ib : op.InBounds ctx) :
    op.range ctx = op.rangeInt ctx := by
  unfold range rangeInt
  congr
  grind [layout_grind]

@[layout_simp, grind =]
theorem BlockPtr.range_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {bl : BlockPtr} (ib : bl.InBounds ctx) :
    bl.range ctx = bl.rangeInt ctx := by
  unfold range rangeInt
  congr
  unfold Block.range Block.rangeInt
  congr
  grind only [= Buffed.Block.Offsets.after_ideal]

@[layout_simp, grind =]
theorem RegionPtr.range_ideal {rg : RegionPtr} : rg.range = rg.rangeInt := by
  simp only [range, rangeInt]
  congr 1

@[layout_simp, grind =]
theorem ValuePtr.range_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {val : ValuePtr} (ib : val.InBounds ctx) :
    val.range ctx = val.rangeInt ctx := by
  cases val with
  | opResult ptr => simpa [range, rangeInt] using ptr.range_ideal repr (by grind)
  | blockArgument ptr => simpa [range, rangeInt] using ptr.range_ideal

@[layout_simp, grind =]
theorem OpOperandPtrPtr.range_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {ptr : OpOperandPtrPtr} (ib : ptr.InBounds ctx) :
    ptr.range ctx = ptr.rangeInt ctx := by
  cases ptr with
  | operandNextUse ptr => simpa [range, rangeInt] using ptr.range_ideal repr (by grind)
  | valueFirstUse ptr => simpa [range, rangeInt] using ptr.range_ideal repr (by grind)

@[layout_simp, grind =]
theorem BlockOperandPtrPtr.range_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {ptr : BlockOperandPtrPtr} (ib : ptr.InBounds ctx) :
    ptr.range ctx = ptr.rangeInt ctx := by
  cases ptr with
  | blockOperandNextUse ptr => simpa [range, rangeInt] using ptr.range_ideal repr (by grind)
  | blockFirstUse ptr => simpa [range, rangeInt] using ptr.range_ideal repr (by grind)

@[layout_simp, grind =]
theorem GenericPtr.range_ideal {ctx : IRContext OpInfo} (repr : ctx.IsRepr) {ptr : GenericPtr} (ib : ptr.InBounds ctx) :
    ptr.range ctx = ptr.rangeInt ctx := by
  cases ptr with
  | operation op => simpa [range, rangeInt] using op.range_ideal repr (by grind)
  | block bl => simpa [range, rangeInt] using bl.range_ideal repr (by grind)
  | region rg => simpa [range, rangeInt] using rg.range_ideal
  | opResult res => simpa [range, rangeInt] using res.range_ideal repr (by grind)
  | opOperand opr => simpa [range, rangeInt] using opr.range_ideal repr (by grind)
  | blockOperand opr => simpa [range, rangeInt] using opr.range_ideal repr (by grind)
  | blockOperandPtr ptr => simpa [range, rangeInt] using ptr.range_ideal repr (by grind)
  | blockArgument arg => simpa [range, rangeInt] using arg.range_ideal
  | value val => simpa [range, rangeInt] using val.range_ideal repr (by grind)
  | opOperandPtr ptr => simpa [range, rangeInt] using ptr.range_ideal repr (by grind)

theorem OpOperandPtr.range_included_op_range {ctx : Veir.IRContext OpInfo} (repr : ctx.IsRepr) (ptr : OpOperandPtr) (ib : ptr.InBounds ctx) :
    IsIncludedI (ptr.range ctx) (ptr.op.range ctx) := by
  rw [OperationPtr.range_ideal (by grind) (by grind)]
  rw [OpOperandPtr.range_ideal (by grind) (by grind)]
  simp only [layout_simp]
  grind

theorem OpResultPtr.range_included_op_range {ctx : Sim.IRContext OpInfo} (ptr : OpResultPtr) (ib : ptr.InBounds ctx.spec) :
    IsIncludedI (ptr.range ctx.spec) (ptr.op.range ctx.spec) := by
  have hop : ptr.op.InBounds ctx.spec := by grind
  have := ctx.sim.repr.operations_indices ptr.op hop |>.capResults
  have := ctx.sim.repr.operations_indices ptr.op hop |>.capOperands
  have := ctx.sim.repr.operations_indices ptr.op hop |>.capRegions
  have := ctx.sim.repr.operations_indices ptr.op hop |>.capBlockOperands
  have := Veir.OperationPtr.getNumResults!_eq_getNumResults (ctx := ctx.spec) (op := ptr.op) hop
  have := ctx.sim.in_bounds (.operation ptr.op) (by grind)
  rw [OperationPtr.range_ideal (by grind) (by grind)]
  rw [OpResultPtr.range_ideal (by grind) (by grind)]
  simp only [rangeInt, toFlatNat, OperationPtr.toFlat, add_nat_range_def]
  grind

theorem BlockOperandPtr.range_included_op_range {ctx : Veir.IRContext OpInfo} (repr : ctx.IsRepr) (ptr : BlockOperandPtr) (ib : ptr.InBounds ctx) :
    IsIncludedI (ptr.range ctx) (ptr.op.range ctx) := by
  rw [OperationPtr.range_ideal (by grind) (by grind)]
  rw [BlockOperandPtr.range_ideal (by grind) (by grind)]
  simp only [layout_simp]
  grind

theorem BlockArgumentPtr.range_included_block_range {ctx : Veir.IRContext OpInfo} (repr : ctx.IsRepr) (ptr : BlockArgumentPtr) (ib : ptr.InBounds ctx) :
    IsIncludedI (ptr.range) (ptr.block.range ctx) := by
  have hbl : ptr.block.InBounds ctx := by grind
  have := repr.blocks_indices ptr.block hbl |>.capArguments
  have := repr.blocks_indices ptr.block hbl |>.arguments
  have hnum := Veir.BlockPtr.getNumArguments!_eq_getNumArguments (ctx := ctx) (block := ptr.block) hbl
  rw [BlockPtr.range_ideal repr hbl]
  rw [BlockArgumentPtr.range_ideal]
  simp only [BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockPtr.rangeInt,
    BlockPtr.toFlat, Block.rangeInt, add_nat_range_def]
  grind

/-- The byte range of the `idx`-th region slot lies inside `op`'s byte range,
    provided `idx < capRegions`. Stated as an `Int` interval so it can feed the
    `read64!_blit64_disjoint` premise once `computeRegionsOffset!` has been rewritten
    to its ideal (`regionsInt`) form. -/
theorem OperationPtr.nthRegion_range_included_op_range (ctx : Sim.IRContext OpInfo) (op : OperationPtr)
    (idx : UInt64) (hidx : idx.toNat < (op.get! ctx.spec).capRegions) (ib : op.InBounds ctx.spec) :
    IsIncludedI
      ((op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat))
        ...(op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) + ptrSizeNat))
      (op.rangeInt ctx.spec) := by
  have hin := ctx.sim.in_bounds (.operation op) (by grind)
  have htoM : (op.toM.toNat : Int) = op.id := by
    simp only [OperationPtr.toM, OperationPtr.toFlat]
    have : (op.id : Nat) < 2 ^ 63 := by grind [OperationPtr.range]
    grind [UInt64.toNat_ofNat]
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat,
    Operation.Offsets.regionsInt, Operation.Offsets.afterInt, Operation.Offsets.resultsInt,
    Operation.Sizes.regionsNat, add_nat_range_def, IsIncludedI]
  refine ⟨?_, ?_⟩ <;> grind

end Veir
