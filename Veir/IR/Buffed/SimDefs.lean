module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Layout
public import Veir.Prelude
public import Veir.IR.Buffed.Layout
public import Veir.IR.Fields
public import Veir.IR.LayoutUnchanged

import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.Layout

set_option linter.unusedSectionVars false

open Veir.Buffed

public section

namespace Veir

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]

/-! ## Translate a high-level pointer to a flat address. -/

@[expose, layout_simp]
def OperationPtr.toFlat (ptr : OperationPtr) := ptr.id

@[grind =]
theorem OperationPtr.toFlat_def (ptr : OperationPtr) : ptr.toFlat = ptr.id := rfl

@[expose, layout_simp]
def BlockPtr.toFlat (ptr : BlockPtr) := ptr.id

@[grind =]
theorem BlockPtr.toFlat_def (ptr : BlockPtr) : ptr.toFlat = ptr.id := rfl

@[expose, layout_simp]
def RegionPtr.toFlat (ptr : RegionPtr) := ptr.id

@[grind =]
theorem RegionPtr.toFlat_def (ptr : RegionPtr) : ptr.toFlat = ptr.id := rfl

@[expose]
def OpResultPtr.toFlat (ptr : OpResultPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.results ptr.op ctx).toInt).toNat +
  ptr.index * Buffed.OpResult.size.toNat
@[expose, layout_grind, layout_simp]
def OpResultPtr.toFlatNat (ptr : OpResultPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.resultsInt ptr.op ctx)).toNat +
  ptr.index * Buffed.OpResult.sizeNat

@[expose]
def OpOperandPtr.toFlat (ptr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.operands ptr.op ctx).toInt).toNat +
  ptr.index * Buffed.OpOperand.size.toNat
@[expose, layout_grind, layout_simp]
def OpOperandPtr.toFlatNat (ptr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.operandsInt ptr.op ctx)).toNat +
  ptr.index * Buffed.OpOperand.sizeNat

@[expose]
def BlockOperandPtr.toFlat (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.blockOperands ptr.op ctx).toInt).toNat +
  ptr.index * Buffed.BlockOperand.size.toNat
@[expose, layout_grind, layout_simp]
def BlockOperandPtr.toFlatNat (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  (ptr.op.toFlat + (Buffed.Operation.Offsets.blockOperandsInt ptr.op ctx)).toNat +
  ptr.index * Buffed.BlockOperand.sizeNat

@[expose]
def BlockArgumentPtr.toFlat (ptr : BlockArgumentPtr) :=
  (ptr.block.toFlat + Buffed.Block.Offsets.arguments.toInt).toNat +
  ptr.index * Buffed.BlockArgument.size.toNat
@[expose, layout_grind, layout_simp]
def BlockArgumentPtr.toFlatNat (ptr : BlockArgumentPtr) :=
  (ptr.block.toFlat + Buffed.Block.Offsets.argumentsInt).toNat +
  ptr.index * Buffed.BlockArgument.sizeNat

@[expose]
def ValuePtr.toFlat (ptr : ValuePtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .opResult ptr => ptr.toFlat ctx
  | .blockArgument ptr => ptr.toFlat
@[expose, layout_grind, layout_simp]
def ValuePtr.toFlatNat (ptr : ValuePtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .opResult ptr => ptr.toFlatNat ctx
  | .blockArgument ptr => ptr.toFlatNat

@[expose]
def OpOperandPtrPtr.toFlat (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse ptr => ptr.toFlat ctx + Buffed.OpOperand.Offsets.nextUse.toInt.toNat
  | .valueFirstUse ptr => ptr.toFlat ctx + Buffed.ValueImpl.Offsets.firstUse.toInt.toNat
@[expose, layout_grind, layout_simp]
def OpOperandPtrPtr.toFlatNat (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse ptr => ptr.toFlatNat ctx + Buffed.OpOperand.Offsets.nextUseInt.toNat
  | .valueFirstUse ptr => ptr.toFlatNat ctx + Buffed.ValueImpl.Offsets.firstUseInt.toNat

@[expose]
def BlockOperandPtrPtr.toFlat (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse ptr => ptr.toFlat ctx + Buffed.BlockOperand.Offsets.nextUse.toInt.toNat
  | .blockFirstUse ptr => ptr.toFlat + Buffed.Block.Offsets.firstUse.toInt.toNat
@[expose, layout_grind, layout_simp]
def BlockOperandPtrPtr.toFlatNat (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse ptr => ptr.toFlatNat ctx + Buffed.BlockOperand.Offsets.nextUseInt.toNat
  | .blockFirstUse ptr => ptr.toFlat + Buffed.Block.Offsets.firstUseInt.toNat

/-! ## A pointer is representable if it fits in 63 bits. -/

@[expose] def OperationPtr.IsRepr (ptr : OperationPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind =]
theorem OperationPtr.IsRepr_def (ptr : OperationPtr) : ptr.IsRepr ↔ ptr.toFlat ≤ Int64.maxNatValue := .rfl

@[expose] def BlockPtr.IsRepr (ptr : BlockPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind =]
theorem BlockPtr.IsRepr_def (ptr : BlockPtr) : ptr.IsRepr ↔ ptr.toFlat ≤ Int64.maxNatValue := .rfl

@[expose] def RegionPtr.IsRepr (ptr : RegionPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind =]
theorem RegionPtr.IsRepr_def (ptr : RegionPtr) : ptr.IsRepr ↔ ptr.toFlat ≤ Int64.maxNatValue := .rfl

/-! ## Translate a high-level pointer to a buffed address. -/

@[expose, layout_grind]
def OperationPtr.toM (ptr : OperationPtr) : OperationMPtr := ptr.toFlat.toUInt64
@[expose, layout_grind, layout_simp]
def OperationPtr.toO (ptr : Option OperationPtr) : OperationOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

@[expose, layout_grind, layout_simp]
def BlockPtr.toM (ptr : BlockPtr) : BlockMPtr := ptr.toFlat.toUInt64
@[expose, layout_grind, layout_simp]
def BlockPtr.toO (ptr : Option BlockPtr) : BlockOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

@[expose, layout_grind, layout_simp]
def RegionPtr.toM (ptr : RegionPtr) : RegionMPtr := ptr.toFlat.toUInt64
@[expose, layout_grind, layout_simp]
def RegionPtr.toO (ptr : Option RegionPtr) : RegionOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

@[expose, layout_grind, layout_simp]
def OpResultPtr.toM (ptr : OpResultPtr) (ctx : IRContext OpInfo) : OpResultMPtr :=
  (ptr.toFlat ctx).toUInt64
@[expose, layout_grind, layout_simp]
def OpResultPtr.toO (ptr : Option OpResultPtr) (ctx : IRContext OpInfo) : OpResultOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

@[expose, layout_grind, layout_simp]
def BlockArgumentPtr.toM (ptr : BlockArgumentPtr) : BlockArgumentMPtr :=
  ptr.toFlat.toUInt64
@[expose, layout_grind, layout_simp]
def BlockArgumentPtr.toO (ptr : Option BlockArgumentPtr) : BlockArgumentOPtr :=
  match ptr with
  | some ptr => ptr.toM
  | none => .none

@[expose, layout_grind, layout_simp]
def OpOperandPtr.toM (ptr : OpOperandPtr) (ctx : IRContext OpInfo) : OpOperandMPtr :=
  (ptr.toFlat ctx).toUInt64
@[expose, layout_grind, layout_simp]
def OpOperandPtr.toO (ptr : Option OpOperandPtr) (ctx : IRContext OpInfo) : OpOperandOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

@[expose, layout_grind, layout_simp]
def BlockOperandPtr.toM (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperandMPtr :=
  (ptr.toFlat ctx).toUInt64
@[expose, layout_grind, layout_simp]
def BlockOperandPtr.toO (ptr : Option BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperandOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

@[expose, layout_grind, layout_simp]
def ValuePtr.toM (ptr : ValuePtr) (ctx : IRContext OpInfo) : ValueImplMPtr :=
  (ptr.toFlat ctx).toUInt64
@[expose, layout_grind, layout_simp]
def ValuePtr.toO (ptr : Option ValuePtr) (ctx : IRContext OpInfo) : ValueImplOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

@[simp, grind =]
theorem ValuePtr.toM_opResult {ctx : IRContext OpInfo} : (ValuePtr.opResult res).toM ctx = res.toM ctx := by rfl

@[simp, grind =]
theorem ValuePtr.toM_blockArgument {ctx : IRContext OpInfo} : (ValuePtr.blockArgument arg).toM ctx = arg.toM := by rfl

@[expose, layout_grind, layout_simp]
def OpOperandPtrPtr.toM (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  (ptr.toFlat ctx).toUInt64

@[expose, layout_grind, layout_simp]
def BlockOperandPtrPtr.toM (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) : GenericMPtr :=
  (ptr.toFlat ctx).toUInt64

@[expose, layout_grind, layout_simp]
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

@[expose, layout_grind, layout_simp]
def GenericPtr.toO (ptr : Option GenericPtr) (ctx : IRContext OpInfo) : GenericOPtr :=
  match ptr with
  | some ptr => ptr.toM ctx
  | none => .none

/-! ## Range of a pointer -/

@[expose]
def OperationPtr.range (op : OperationPtr) (ctx : IRContext OpInfo) :=
  op.toFlat + (Buffed.Operation.range op ctx)

abbrev OperationPtr.rangeInt (op : OperationPtr) (ctx : IRContext OpInfo) :=
  op.toFlat + (Buffed.Operation.rangeInt op ctx)

@[expose]
def BlockPtr.range (bl : BlockPtr) (ctx : IRContext OpInfo) :=
  bl.toFlat + Buffed.Block.range bl ctx

@[expose, layout_grind, layout_simp]
def BlockPtr.rangeInt (bl : BlockPtr) (ctx : IRContext OpInfo) :=
  bl.toFlat + Buffed.Block.rangeInt bl ctx

@[expose]
def RegionPtr.range (rg : RegionPtr) :=
  rg.toFlat + Buffed.Region.range

@[expose, layout_grind, layout_simp]
def RegionPtr.rangeInt (rg : RegionPtr) :=
  rg.toFlat + Buffed.Region.rangeInt

@[expose]
def OpResultPtr.range (res : OpResultPtr) (ctx : IRContext OpInfo) :=
  res.toFlat ctx + Buffed.OpResult.range

@[expose, layout_grind, layout_simp]
def OpResultPtr.rangeInt (res : OpResultPtr) (ctx : IRContext OpInfo) :=
  res.toFlatNat ctx + Buffed.OpResult.rangeInt

@[expose]
def BlockArgumentPtr.range (arg : BlockArgumentPtr) :=
  arg.toFlat + Buffed.BlockArgument.range

@[expose, layout_grind, layout_simp]
def BlockArgumentPtr.rangeInt (arg : BlockArgumentPtr) :=
  arg.toFlatNat + Buffed.BlockArgument.rangeInt

@[expose]
def OpOperandPtr.range (opr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlat ctx + Buffed.OpOperand.range

@[expose, layout_grind, layout_simp]
def OpOperandPtr.rangeInt (opr : OpOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlatNat ctx + Buffed.OpOperand.rangeInt

@[expose]
def BlockOperandPtr.range (opr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlat ctx + Buffed.BlockOperand.range

@[expose, layout_grind, layout_simp]
def BlockOperandPtr.rangeInt (opr : BlockOperandPtr) (ctx : IRContext OpInfo) :=
  opr.toFlatNat ctx + Buffed.BlockOperand.rangeInt

@[expose]
def ValuePtr.range (val : ValuePtr) (ctx : IRContext OpInfo) :=
  match val with
  | .opResult res => res.range ctx
  | .blockArgument arg => arg.range

@[expose, layout_grind, layout_simp]
def ValuePtr.rangeInt (val : ValuePtr) (ctx : IRContext OpInfo) :=
  match val with
  | .opResult res => res.rangeInt ctx
  | .blockArgument arg => arg.rangeInt

@[expose]
def OpOperandPtrPtr.range (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse opr => opr.range ctx
  | .valueFirstUse val => val.range ctx

@[expose, layout_grind, layout_simp]
def OpOperandPtrPtr.rangeInt (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .operandNextUse opr => opr.rangeInt ctx
  | .valueFirstUse val => val.rangeInt ctx

@[expose]
def BlockOperandPtrPtr.range (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse opr => opr.range ctx
  | .blockFirstUse bl => bl.range ctx

@[expose, layout_grind, layout_simp]
def BlockOperandPtrPtr.rangeInt (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :=
  match ptr with
  | .blockOperandNextUse opr => opr.rangeInt ctx
  | .blockFirstUse bl => bl.rangeInt ctx

@[expose]
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

@[expose, layout_grind, layout_simp]
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

@[expose] def OpResultPtr.IsRepr (ptr : OpResultPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind =]
theorem OpResultPtr.IsRepr_def (ptr : OpResultPtr) (ctx : IRContext OpInfo) :
    ptr.IsRepr ctx ↔ ptr.toFlat ctx ≤ Int64.maxNatValue := .rfl

@[expose] def OpOperandPtr.IsRepr (ptr : OpOperandPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind =]
theorem OpOperandPtr.IsRepr_def (ptr : OpOperandPtr) (ctx : IRContext OpInfo) :
    ptr.IsRepr ctx ↔ ptr.toFlat ctx ≤ Int64.maxNatValue := .rfl

@[expose] def BlockOperandPtr.IsRepr (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind =]
theorem BlockOperandPtr.IsRepr_def (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) :
    ptr.IsRepr ctx ↔ ptr.toFlat ctx ≤ Int64.maxNatValue := .rfl

@[expose] def BlockArgumentPtr.IsRepr (ptr : BlockArgumentPtr) : Prop :=
  ptr.toFlat ≤ Int64.maxNatValue

@[grind =]
theorem BlockArgumentPtr.IsRepr_def (ptr : BlockArgumentPtr) :
    ptr.IsRepr ↔ ptr.toFlat ≤ Int64.maxNatValue := .rfl

@[expose] def ValuePtr.IsRepr (ptr : ValuePtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind =]
theorem ValuePtr.IsRepr_def (ptr : ValuePtr) (ctx : IRContext OpInfo) :
    ptr.IsRepr ctx ↔ ptr.toFlat ctx ≤ Int64.maxNatValue := .rfl

@[expose] def OpOperandPtrPtr.IsRepr (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind =]
theorem OpOperandPtrPtr.IsRepr_def (ptr : OpOperandPtrPtr) (ctx : IRContext OpInfo) :
    ptr.IsRepr ctx ↔ ptr.toFlat ctx ≤ Int64.maxNatValue := .rfl

@[expose] def BlockOperandPtrPtr.IsRepr (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) : Prop :=
  ptr.toFlat ctx ≤ Int64.maxNatValue

@[grind =]
theorem BlockOperandPtrPtr.IsRepr_def (ptr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) :
    ptr.IsRepr ctx ↔ ptr.toFlat ctx ≤ Int64.maxNatValue := .rfl

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

@[expose]
def Sim.GenericPtr.fromBlock (ptr : BlockPtr) : GenericPtr :=
  ⟨ptr.impl, .block ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromBlock_def (ptr : BlockPtr) : Sim.GenericPtr.fromBlock ptr = ⟨ptr.impl, .block ptr.spec⟩ := rfl
@[expose]
def Sim.GenericPtr.fromOperation (ptr : OperationPtr) : GenericPtr :=
  ⟨ptr.impl, .operation ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromOperation_def (ptr : OperationPtr) : Sim.GenericPtr.fromOperation ptr = ⟨ptr.impl, .operation ptr.spec⟩ := rfl
@[expose]
def Sim.GenericPtr.fromOpResult (ptr : OpResultPtr) : GenericPtr :=
  ⟨ptr.impl, .opResult ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromOpResult_def (ptr : OpResultPtr) : Sim.GenericPtr.fromOpResult ptr = ⟨ptr.impl, .opResult ptr.spec⟩ := rfl
@[expose]
def Sim.GenericPtr.fromOpOperand (ptr : OpOperandPtr) : GenericPtr :=
  ⟨ptr.impl, .opOperand ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromOpOperand_def (ptr : OpOperandPtr) : Sim.GenericPtr.fromOpOperand ptr = ⟨ptr.impl, .opOperand ptr.spec⟩ := rfl
@[expose]
def Sim.GenericPtr.fromBlockOperand (ptr : BlockOperandPtr) : GenericPtr :=
  ⟨ptr.impl, .blockOperand ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromBlockOperand_def (ptr : BlockOperandPtr) : Sim.GenericPtr.fromBlockOperand ptr = ⟨ptr.impl, .blockOperand ptr.spec⟩ := rfl
@[expose]
def Sim.GenericPtr.fromBlockOperandPtr (ptr : BlockOperandPtrPtr) : GenericPtr :=
  ⟨ptr.impl, .blockOperandPtr ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromBlockOperandPtr_def (ptr : BlockOperandPtrPtr) : Sim.GenericPtr.fromBlockOperandPtr ptr = ⟨ptr.impl, .blockOperandPtr ptr.spec⟩ := rfl
@[expose]
def Sim.GenericPtr.fromBlockArgument (ptr : BlockArgumentPtr) : GenericPtr :=
  ⟨ptr.impl, .blockArgument ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromBlockArgument_def (ptr : BlockArgumentPtr) : Sim.GenericPtr.fromBlockArgument ptr = ⟨ptr.impl, .blockArgument ptr.spec⟩ := rfl
@[expose]
def Sim.GenericPtr.fromRegion (ptr : RegionPtr) : GenericPtr :=
  ⟨ptr.impl, .region ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromRegion_def (ptr : RegionPtr) : Sim.GenericPtr.fromRegion ptr = ⟨ptr.impl, .region ptr.spec⟩ := rfl
@[expose]
def Sim.GenericPtr.fromValue (ptr : ValuePtr) : GenericPtr :=
  ⟨ptr.impl, .value ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromValue_def (ptr : ValuePtr) : Sim.GenericPtr.fromValue ptr = ⟨ptr.impl, .value ptr.spec⟩ := rfl
@[expose]
def Sim.GenericPtr.fromOpOperandPtr (ptr : OpOperandPtrPtr) : GenericPtr :=
  ⟨ptr.impl, .opOperandPtr ptr.spec⟩

@[grind =]
theorem Sim.GenericPtr.fromOpOperandPtr_def (ptr : OpOperandPtrPtr) : Sim.GenericPtr.fromOpOperandPtr ptr = ⟨ptr.impl, .opOperandPtr ptr.spec⟩ := rfl

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionGenericPtr where
  impl : GenericOPtr
  spec : Option Veir.GenericPtr

@[expose]
def Sim.OptionGenericPtr.fromBlock (ptr : OptionBlockPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .block⟩

@[grind =]
theorem Sim.OptionGenericPtr.fromBlock_def (ptr : OptionBlockPtr) : Sim.OptionGenericPtr.fromBlock ptr = ⟨ptr.impl, ptr.spec.map .block⟩ := rfl
@[expose]
def Sim.OptionGenericPtr.fromOperation (ptr : OptionOperationPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .operation⟩

@[grind =]
theorem Sim.OptionGenericPtr.fromOperation_def (ptr : OptionOperationPtr) : Sim.OptionGenericPtr.fromOperation ptr = ⟨ptr.impl, ptr.spec.map .operation⟩ := rfl
@[expose]
def Sim.OptionGenericPtr.fromOpResult (ptr : OptionOpResultPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .opResult⟩

@[grind =]
theorem Sim.OptionGenericPtr.fromOpResult_def (ptr : OptionOpResultPtr) : Sim.OptionGenericPtr.fromOpResult ptr = ⟨ptr.impl, ptr.spec.map .opResult⟩ := rfl
@[expose]
def Sim.OptionGenericPtr.fromOpOperand (ptr : OptionOpOperandPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map  .opOperand⟩

@[grind =]
theorem Sim.OptionGenericPtr.fromOpOperand_def (ptr : OptionOpOperandPtr) : Sim.OptionGenericPtr.fromOpOperand ptr = ⟨ptr.impl, ptr.spec.map  .opOperand⟩ := rfl
@[expose]
def Sim.OptionGenericPtr.fromBlockOperand (ptr : OptionBlockOperandPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .blockOperand⟩

@[grind =]
theorem Sim.OptionGenericPtr.fromBlockOperand_def (ptr : OptionBlockOperandPtr) : Sim.OptionGenericPtr.fromBlockOperand ptr = ⟨ptr.impl, ptr.spec.map .blockOperand⟩ := rfl
@[expose]
def Sim.OptionGenericPtr.fromBlockArgument (ptr : OptionBlockArgumentPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .blockArgument⟩

@[grind =]
theorem Sim.OptionGenericPtr.fromBlockArgument_def (ptr : OptionBlockArgumentPtr) : Sim.OptionGenericPtr.fromBlockArgument ptr = ⟨ptr.impl, ptr.spec.map .blockArgument⟩ := rfl
@[expose]
def Sim.OptionGenericPtr.fromRegion (ptr : OptionRegionPtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .region⟩

@[grind =]
theorem Sim.OptionGenericPtr.fromRegion_def (ptr : OptionRegionPtr) : Sim.OptionGenericPtr.fromRegion ptr = ⟨ptr.impl, ptr.spec.map .region⟩ := rfl
@[expose]
def Sim.OptionGenericPtr.fromValue (ptr : OptionValuePtr) : OptionGenericPtr :=
  ⟨ptr.impl, ptr.spec.map .value⟩

@[grind =]
theorem Sim.OptionGenericPtr.fromValue_def (ptr : OptionValuePtr) : Sim.OptionGenericPtr.fromValue ptr = ⟨ptr.impl, ptr.spec.map .value⟩ := rfl

/-! ## Refinement for Sim Pointers -/

variable (OpInfo) [HasOpInfo OpInfo] in
structure Sim.RawIRContext where
  buf : IRBufContext OpInfo
  spec : Veir.IRContext OpInfo

def Sim.OperationPtr.Sim (ptr : Sim.OperationPtr) :=
  ptr.spec.toM = ptr.impl

def Sim.OptionOperationPtr.Sim (ptr : Sim.OptionOperationPtr) :=
  OperationPtr.toO ptr.spec = ptr.impl

def Sim.BlockPtr.Sim (ptr : Sim.BlockPtr) :=
  ptr.spec.toM = ptr.impl

def Sim.OptionBlockPtr.Sim (ptr : Sim.OptionBlockPtr) :=
  BlockPtr.toO ptr.spec = ptr.impl

def Sim.RegionPtr.Sim (ptr : Sim.RegionPtr) :=
  ptr.spec.toM = ptr.impl

def Sim.OptionRegionPtr.Sim (ptr : Sim.OptionRegionPtr) :=
  RegionPtr.toO ptr.spec = ptr.impl

def Sim.OpResultPtr.Sim (ptr : Sim.OpResultPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

def Sim.OptionOpResultPtr.Sim (ptr : Sim.OptionOpResultPtr) (ctx : Sim.RawIRContext OpInfo) :=
  OpResultPtr.toO ptr.spec ctx.spec = ptr.impl

def Sim.BlockArgumentPtr.Sim (ptr : Sim.BlockArgumentPtr) :=
  ptr.spec.toM = ptr.impl

def Sim.OptionBlockArgumentPtr.Sim (ptr : Sim.OptionBlockArgumentPtr) :=
  BlockArgumentPtr.toO ptr.spec = ptr.impl

def Sim.OpOperandPtr.Sim (ptr : Sim.OpOperandPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

def Sim.OptionOpOperandPtr.Sim (ptr : Sim.OptionOpOperandPtr) (ctx : Sim.RawIRContext OpInfo) :=
  OpOperandPtr.toO ptr.spec ctx.spec = ptr.impl
def Sim.BlockOperandPtr.Sim (ptr : Sim.BlockOperandPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

def Sim.OptionBlockOperandPtr.Sim (ptr : Sim.OptionBlockOperandPtr) (ctx : Sim.RawIRContext OpInfo) :=
  BlockOperandPtr.toO ptr.spec ctx.spec = ptr.impl

def Sim.ValuePtr.Sim (ptr : Sim.ValuePtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

def Sim.OptionValuePtr.Sim (ptr : Sim.OptionValuePtr) (ctx : Sim.RawIRContext OpInfo) :=
  ValuePtr.toO ptr.spec ctx.spec = ptr.impl

def Sim.OpOperandPtrPtr.Sim (ptr : Sim.OpOperandPtrPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

def Sim.BlockOperandPtrPtr.Sim (ptr : Sim.BlockOperandPtrPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

def Sim.GenericPtr.Sim (ptr : Sim.GenericPtr) (ctx : Sim.RawIRContext OpInfo) :=
  ptr.spec.toM ctx.spec = ptr.impl

def Sim.OptionGenericPtr.Sim (ptr : Sim.OptionGenericPtr) (ctx : Sim.RawIRContext OpInfo) :=
  GenericPtr.toO ptr.spec ctx.spec = ptr.impl

/-! ### Equation bricks for the `Sim` predicates.

These let modules that do not `import all` this file (where the `Sim` bodies are opaque)
still convert between `ptr.Sim` and its defining equation: `Sim_def` is the `grind`-facing
iff, `.out` the term-level projection used by the proof macros. -/

@[grind =]
theorem Sim.OperationPtr.Sim_def (ptr : Sim.OperationPtr) :
    ptr.Sim ↔ ptr.spec.toM = ptr.impl := .rfl
theorem Sim.OperationPtr.Sim.out {ptr : Sim.OperationPtr} (h : ptr.Sim) :
    ptr.spec.toM = ptr.impl := h

@[grind =]
theorem Sim.OptionOperationPtr.Sim_def (ptr : Sim.OptionOperationPtr) :
    ptr.Sim ↔ OperationPtr.toO ptr.spec = ptr.impl := .rfl
theorem Sim.OptionOperationPtr.Sim.out {ptr : Sim.OptionOperationPtr} (h : ptr.Sim) :
    OperationPtr.toO ptr.spec = ptr.impl := h

@[grind =]
theorem Sim.BlockPtr.Sim_def (ptr : Sim.BlockPtr) :
    ptr.Sim ↔ ptr.spec.toM = ptr.impl := .rfl
theorem Sim.BlockPtr.Sim.out {ptr : Sim.BlockPtr} (h : ptr.Sim) :
    ptr.spec.toM = ptr.impl := h

@[grind =]
theorem Sim.OptionBlockPtr.Sim_def (ptr : Sim.OptionBlockPtr) :
    ptr.Sim ↔ BlockPtr.toO ptr.spec = ptr.impl := .rfl
theorem Sim.OptionBlockPtr.Sim.out {ptr : Sim.OptionBlockPtr} (h : ptr.Sim) :
    BlockPtr.toO ptr.spec = ptr.impl := h

@[grind =]
theorem Sim.RegionPtr.Sim_def (ptr : Sim.RegionPtr) :
    ptr.Sim ↔ ptr.spec.toM = ptr.impl := .rfl
theorem Sim.RegionPtr.Sim.out {ptr : Sim.RegionPtr} (h : ptr.Sim) :
    ptr.spec.toM = ptr.impl := h

@[grind =]
theorem Sim.OptionRegionPtr.Sim_def (ptr : Sim.OptionRegionPtr) :
    ptr.Sim ↔ RegionPtr.toO ptr.spec = ptr.impl := .rfl
theorem Sim.OptionRegionPtr.Sim.out {ptr : Sim.OptionRegionPtr} (h : ptr.Sim) :
    RegionPtr.toO ptr.spec = ptr.impl := h

@[grind =]
theorem Sim.OpResultPtr.Sim_def (ptr : Sim.OpResultPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ ptr.spec.toM ctx.spec = ptr.impl := .rfl
theorem Sim.OpResultPtr.Sim.out {ptr : Sim.OpResultPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    ptr.spec.toM ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.OptionOpResultPtr.Sim_def (ptr : Sim.OptionOpResultPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ OpResultPtr.toO ptr.spec ctx.spec = ptr.impl := .rfl
theorem Sim.OptionOpResultPtr.Sim.out {ptr : Sim.OptionOpResultPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    OpResultPtr.toO ptr.spec ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.BlockArgumentPtr.Sim_def (ptr : Sim.BlockArgumentPtr) :
    ptr.Sim ↔ ptr.spec.toM = ptr.impl := .rfl
theorem Sim.BlockArgumentPtr.Sim.out {ptr : Sim.BlockArgumentPtr} (h : ptr.Sim) :
    ptr.spec.toM = ptr.impl := h

@[grind =]
theorem Sim.OptionBlockArgumentPtr.Sim_def (ptr : Sim.OptionBlockArgumentPtr) :
    ptr.Sim ↔ BlockArgumentPtr.toO ptr.spec = ptr.impl := .rfl
theorem Sim.OptionBlockArgumentPtr.Sim.out {ptr : Sim.OptionBlockArgumentPtr} (h : ptr.Sim) :
    BlockArgumentPtr.toO ptr.spec = ptr.impl := h

@[grind =]
theorem Sim.OpOperandPtr.Sim_def (ptr : Sim.OpOperandPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ ptr.spec.toM ctx.spec = ptr.impl := .rfl
theorem Sim.OpOperandPtr.Sim.out {ptr : Sim.OpOperandPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    ptr.spec.toM ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.OptionOpOperandPtr.Sim_def (ptr : Sim.OptionOpOperandPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ OpOperandPtr.toO ptr.spec ctx.spec = ptr.impl := .rfl
theorem Sim.OptionOpOperandPtr.Sim.out {ptr : Sim.OptionOpOperandPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    OpOperandPtr.toO ptr.spec ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.BlockOperandPtr.Sim_def (ptr : Sim.BlockOperandPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ ptr.spec.toM ctx.spec = ptr.impl := .rfl
theorem Sim.BlockOperandPtr.Sim.out {ptr : Sim.BlockOperandPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    ptr.spec.toM ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.OptionBlockOperandPtr.Sim_def (ptr : Sim.OptionBlockOperandPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ BlockOperandPtr.toO ptr.spec ctx.spec = ptr.impl := .rfl
theorem Sim.OptionBlockOperandPtr.Sim.out {ptr : Sim.OptionBlockOperandPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    BlockOperandPtr.toO ptr.spec ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.ValuePtr.Sim_def (ptr : Sim.ValuePtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ ptr.spec.toM ctx.spec = ptr.impl := .rfl
theorem Sim.ValuePtr.Sim.out {ptr : Sim.ValuePtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    ptr.spec.toM ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.OptionValuePtr.Sim_def (ptr : Sim.OptionValuePtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ ValuePtr.toO ptr.spec ctx.spec = ptr.impl := .rfl
theorem Sim.OptionValuePtr.Sim.out {ptr : Sim.OptionValuePtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    ValuePtr.toO ptr.spec ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.OpOperandPtrPtr.Sim_def (ptr : Sim.OpOperandPtrPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ ptr.spec.toM ctx.spec = ptr.impl := .rfl
theorem Sim.OpOperandPtrPtr.Sim.out {ptr : Sim.OpOperandPtrPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    ptr.spec.toM ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.BlockOperandPtrPtr.Sim_def (ptr : Sim.BlockOperandPtrPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ ptr.spec.toM ctx.spec = ptr.impl := .rfl
theorem Sim.BlockOperandPtrPtr.Sim.out {ptr : Sim.BlockOperandPtrPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    ptr.spec.toM ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.GenericPtr.Sim_def (ptr : Sim.GenericPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ ptr.spec.toM ctx.spec = ptr.impl := .rfl
theorem Sim.GenericPtr.Sim.out {ptr : Sim.GenericPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    ptr.spec.toM ctx.spec = ptr.impl := h

@[grind =]
theorem Sim.OptionGenericPtr.Sim_def (ptr : Sim.OptionGenericPtr) (ctx : Sim.RawIRContext OpInfo) :
    ptr.Sim ctx ↔ GenericPtr.toO ptr.spec ctx.spec = ptr.impl := .rfl
theorem Sim.OptionGenericPtr.Sim.out {ptr : Sim.OptionGenericPtr} {ctx : Sim.RawIRContext OpInfo} (h : ptr.Sim ctx) :
    GenericPtr.toO ptr.spec ctx.spec = ptr.impl := h

/-! ## Refinement predicate. -/

structure OpResultPtr.Matches (ctx : Sim.RawIRContext OpInfo) (res : OpResultPtr) (ib : res.InBounds ctx.spec) where
  kind : (res.toM ctx.spec).readKind! ctx.buf = Buffed.ValueImpl.kindResult
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
  kind : arg.toM.readKind! ctx.buf = Buffed.ValueImpl.kindArgument
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
  opType : op.getOpType! ctx.spec = SerializableOpInfo.decode (op.toM.readOpType! ctx.buf)
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

@[expose, simp, grind]
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
  /-- Attribute-table slot 0 canonically holds the empty dictionary, so the zero-initialized `attrs` field of a freshly allocated operation denotes the empty dictionary. -/
  attr_empty : ctx.buf.attributes[0]? = some (.dictionaryAttr DictionaryAttr.empty)

variable (OpInfo) [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] in
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
    case attr_empty => simp [IRBufContext.default_def]
    all_goals
    · simp only [IRContext.default_def]
      intros ptr
      cases ptr <;> grind⟩

@[expose]
def Sim.IRContext.inner (ctx : IRContext OpInfo) : RawIRContext OpInfo := ⟨ctx.buf, ctx.spec⟩

@[grind =]
theorem Sim.IRContext.inner_def (ctx : IRContext OpInfo) : ctx.inner = ⟨ctx.buf, ctx.spec⟩ := rfl

@[grind .]
theorem Sim.IRContext.isRepr (ctx : IRContext OpInfo) : ctx.spec.IsRepr := ctx.sim.repr

@[grind! .]
theorem Sim.IRContext.fieldsInBounds (ctx : IRContext OpInfo) : ctx.spec.FieldsInBounds := ctx.sim.fieldsInBounds


theorem Operation.propertySize_lt (oi : OpInfo) : (Operation.propertySize oi).toNat < UInt32.size := by
  unfold Operation.propertySize
  grind

@[grind .] theorem Operation.propertySize_pos  (oi : OpInfo) : 0 ≤ (Operation.propertySize oi).toInt64.toInt := by
  have := Operation.propertySize_lt oi
  simp only [UInt64.toInt64, Int64.toInt, Int64.toBitVec, BitVec.toInt_eq_toNat_cond]
  grind [UInt64.toNat]
@[grind .] theorem Operation.propertySize_lt_Int (oi : OpInfo) : (Operation.propertySize oi).toInt64.toInt < 4294967296 := by
  have := Operation.propertySize_lt oi
  simp only [UInt64.toInt64, Int64.toInt, Int64.toBitVec, BitVec.toInt_eq_toNat_cond]
  grind [UInt64.toNat]

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
    (h : op.impl.toNat + Operation.sizeBaseNat ≤ ctx.buf.size) :
    (op.impl.computeBlockOperandsOffset! ctx.buf).toInt = Operation.Offsets.blockOperandsInt op.spec ctx.spec := by
  rw [← OperationMPtr.computeBlockOperandsOffset_eq_computeBlockOperandsOffset! (h := h)]
  exact OperationPtr.computeBlockOperandsOffset_ideal ctx op hib hsim h

@[layout_simp, layout_grind =]
theorem OperationPtr.computeRegionsOffset!_ideal (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hib : op.spec.InBounds ctx.spec) (hsim : op.Sim)
    (h : op.impl.toNat + Operation.sizeBaseNat ≤ ctx.buf.size) :
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
    rw [UInt64.toNat_mul, show BlockArgument.size.toNat = 40 from rfl,
      show BlockArgument.sizeNat = 40 from rfl, Nat.mod_eq_of_lt (by omega)]
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
theorem OpOperandPtr.range_ideal {ctx : IRContext OpInfo} (_repr : ctx.IsRepr) {op : OpOperandPtr} (_ib : op.InBounds ctx) :
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

/-- The byte range of the `idx`-th region slot lies inside `op`'s byte range, provided `idx < capRegions`. -/
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

/-- The byte range of the `idx`-th result slot lies inside `op`'s byte range, provided `idx < capResults`. -/
theorem OperationPtr.nthResult_range_included_op_range (ctx : Sim.IRContext OpInfo) (op : OperationPtr)
    (idx : UInt64) (hidx : idx.toNat < (op.get! ctx.spec).capResults) (ib : op.InBounds ctx.spec) :
    IsIncludedI
      ((op.toM.toNat + (Operation.Offsets.resultsInt op ctx.spec + OpResult.sizeNat * idx.toNat))
        ...(op.toM.toNat + (Operation.Offsets.resultsInt op ctx.spec + OpResult.sizeNat * idx.toNat) + OpResult.sizeNat))
      (op.rangeInt ctx.spec) := by
  have hin := ctx.sim.in_bounds (.operation op) (by grind)
  have htoM : (op.toM.toNat : Int) = op.id := by
    simp only [OperationPtr.toM, OperationPtr.toFlat]
    have : (op.id : Nat) < 2 ^ 63 := by grind [OperationPtr.range]
    grind [UInt64.toNat_ofNat]
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat,
    Operation.Offsets.afterInt, Operation.Offsets.resultsInt,
    Operation.Sizes.resultsNat, add_nat_range_def, IsIncludedI]
  refine ⟨?_, ?_⟩ <;> grind

/-- The byte range of the `idx`-th operand slot lies inside `op`'s byte range, provided `idx < capOperands`. -/
theorem OperationPtr.nthOperand_range_included_op_range (ctx : Sim.IRContext OpInfo) (op : OperationPtr)
    (idx : UInt64) (hidx : idx.toNat < (op.get! ctx.spec).capOperands) (ib : op.InBounds ctx.spec) :
    IsIncludedI
      ((op.toM.toNat + (Operation.Offsets.operandsInt op ctx.spec + OpOperand.sizeNat * idx.toNat))
        ...(op.toM.toNat + (Operation.Offsets.operandsInt op ctx.spec + OpOperand.sizeNat * idx.toNat) + OpOperand.sizeNat))
      (op.rangeInt ctx.spec) := by
  have hin := ctx.sim.in_bounds (.operation op) (by grind)
  have htoM : (op.toM.toNat : Int) = op.id := by
    simp only [OperationPtr.toM, OperationPtr.toFlat]
    have : (op.id : Nat) < 2 ^ 63 := by grind [OperationPtr.range]
    grind [UInt64.toNat_ofNat]
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat,
    Operation.Offsets.afterInt, Operation.Offsets.regionsInt, Operation.Offsets.blockOperandsInt,
    Operation.Offsets.operandsInt, Operation.Offsets.resultsInt,
    Operation.Sizes.operandsNat, Operation.Sizes.blockOperandsNat, Operation.Sizes.regionsNat,
    add_nat_range_def, IsIncludedI]
  refine ⟨?_, ?_⟩ <;> grind

/-- The byte range of the `idx`-th block-operand slot lies inside `op`'s byte range, provided `idx < capBlockOperands`. -/
theorem OperationPtr.nthBlockOperand_range_included_op_range (ctx : Sim.IRContext OpInfo) (op : OperationPtr)
    (idx : UInt64) (hidx : idx.toNat < (op.get! ctx.spec).capBlockOperands) (ib : op.InBounds ctx.spec) :
    IsIncludedI
      ((op.toM.toNat + (Operation.Offsets.blockOperandsInt op ctx.spec + BlockOperand.sizeNat * idx.toNat))
        ...(op.toM.toNat + (Operation.Offsets.blockOperandsInt op ctx.spec + BlockOperand.sizeNat * idx.toNat) + BlockOperand.sizeNat))
      (op.rangeInt ctx.spec) := by
  have hin := ctx.sim.in_bounds (.operation op) (by grind)
  have htoM : (op.toM.toNat : Int) = op.id := by
    simp only [OperationPtr.toM, OperationPtr.toFlat]
    have : (op.id : Nat) < 2 ^ 63 := by grind [OperationPtr.range]
    grind [UInt64.toNat_ofNat]
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat,
    Operation.Offsets.afterInt, Operation.Offsets.regionsInt, Operation.Offsets.blockOperandsInt,
    Operation.Offsets.resultsInt,
    Operation.Sizes.blockOperandsNat, Operation.Sizes.regionsNat,
    add_nat_range_def, IsIncludedI]
  refine ⟨?_, ?_⟩ <;> grind

/-- The byte range of the `idx`-th argument slot lies inside `bl`'s byte range, provided `idx < capArguments`. -/
theorem BlockPtr.nthArgument_range_included_block_range (ctx : Sim.IRContext OpInfo) (bl : BlockPtr)
    (idx : UInt64) (hidx : idx.toNat < (bl.get! ctx.spec).capArguments) (ib : bl.InBounds ctx.spec) :
    IsIncludedI
      ((bl.toM.toNat + (Block.Offsets.argumentsInt + BlockArgument.sizeNat * idx.toNat))
        ...(bl.toM.toNat + (Block.Offsets.argumentsInt + BlockArgument.sizeNat * idx.toNat) + BlockArgument.sizeNat))
      (bl.rangeInt ctx.spec) := by
  have hin := ctx.sim.in_bounds (.block bl) (by grind)
  have htoM : (bl.toM.toNat : Int) = bl.id := by
    simp only [BlockPtr.toM, BlockPtr.toFlat]
    have : (bl.id : Nat) < 2 ^ 63 := by grind [BlockPtr.range]
    grind [UInt64.toNat_ofNat]
  simp only [BlockPtr.rangeInt, Block.rangeInt, BlockPtr.toFlat,
    Block.Offsets.afterInt, Block.Offsets.argumentsInt,
    Block.Sizes.argumentsNat, add_nat_range_def, IsIncludedI]
  refine ⟨?_, ?_⟩ <;> grind

end Veir
