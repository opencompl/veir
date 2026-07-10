module

public import Veir.Prelude
public import Veir.IR.Basic
public import Veir.IR.LayoutUnchanged
public import Lean

/-! # Sizes of the different fields, in bytes. -/

public section

namespace Veir.Buffed

abbrev ptrSize : UInt64 := 8
abbrev ptrSizeNat : Nat := ptrSize.toNat
abbrev countSize : UInt64 := 8
abbrev countSizeNat : Nat := countSize.toNat
abbrev ptrCard : Nat := UInt64.size
abbrev countCard : Nat := UInt32.size

namespace ValueImpl
abbrev kindResult : UInt64 := 0
abbrev kindArgument : UInt64 := 1
namespace Sizes
abbrev kind : UInt64 := countSize
abbrev kindNat := countSizeNat
abbrev type : UInt64 := ptrSize
abbrev typeNat := ptrSizeNat
abbrev firstUse : UInt64 := ptrSize
abbrev firstUseNat := ptrSizeNat
end Sizes
abbrev size : UInt64 := ValueImpl.Sizes.kind + ValueImpl.Sizes.type + ValueImpl.Sizes.firstUse
abbrev sizeNat := ValueImpl.Sizes.kindNat + ValueImpl.Sizes.typeNat + ValueImpl.Sizes.firstUseNat
end ValueImpl

namespace OpResult
namespace Sizes
abbrev index : UInt64 := ptrSize
abbrev indexNat := ptrSizeNat
abbrev owner : UInt64 := ptrSize
abbrev ownerNat := ptrSizeNat
end Sizes
abbrev size : UInt64 := ValueImpl.size + Sizes.index + Sizes.owner
abbrev sizeNat := ValueImpl.sizeNat + Sizes.indexNat + Sizes.ownerNat
end OpResult

namespace BlockArgument
namespace Sizes
abbrev index : UInt64 := ptrSize
abbrev indexNat := ptrSizeNat
abbrev loc : UInt64 := 0
abbrev locNat : Nat := 0
abbrev owner : UInt64 := ptrSize
abbrev ownerNat := ptrSizeNat
end Sizes
abbrev size : UInt64 := ValueImpl.size + Sizes.index + Sizes.loc + Sizes.owner
abbrev sizeNat := ValueImpl.sizeNat + Sizes.indexNat + Sizes.locNat + Sizes.ownerNat
end BlockArgument

namespace OpOperand
namespace Sizes
abbrev nextUse : UInt64 := ptrSize
abbrev nextUseNat := ptrSizeNat
abbrev back : UInt64 := ptrSize
abbrev backNat := ptrSizeNat
abbrev owner : UInt64 := ptrSize
abbrev ownerNat := ptrSizeNat
abbrev value : UInt64 := ptrSize
abbrev valueNat := ptrSizeNat
end Sizes
abbrev size : UInt64 := Sizes.nextUse + Sizes.back + Sizes.owner + Sizes.value
abbrev sizeNat := Sizes.nextUseNat + Sizes.backNat + Sizes.ownerNat + Sizes.valueNat
end OpOperand

namespace BlockOperand
namespace Sizes
abbrev nextUse : UInt64 := ptrSize
abbrev nextUseNat := ptrSizeNat
abbrev back : UInt64 := ptrSize
abbrev backNat := ptrSizeNat
abbrev owner : UInt64 := ptrSize
abbrev ownerNat := ptrSizeNat
abbrev value : UInt64 := ptrSize
abbrev valueNat := ptrSizeNat
end Sizes
abbrev size : UInt64 := Sizes.nextUse + Sizes.back + Sizes.owner + Sizes.value
abbrev sizeNat := Sizes.nextUseNat + Sizes.backNat + Sizes.ownerNat + Sizes.valueNat
end BlockOperand

namespace Operation
variable [HasOpInfo OpInfo] (op : OperationPtr) (ctx : IRContext OpInfo)

-- Add this info to the typeclasses
def propertySize (opCode : OpInfo) : UInt64 := 8 -- sorry
@[inline] abbrev opInfoSize : Nat := 8

namespace Sizes
abbrev results : UInt64 := UInt64.ofNat (op.get! ctx).capResults * OpResult.size
abbrev resultsNat : Nat := (op.get! ctx).capResults * OpResult.sizeNat
abbrev numResults : UInt64 := countSize
abbrev numResultsNat := countSizeNat
abbrev prev : UInt64 := ptrSize
abbrev prevNat := ptrSizeNat
abbrev next : UInt64 := ptrSize
abbrev nextNat := ptrSizeNat
abbrev parent : UInt64 := ptrSize
abbrev parentNat := ptrSizeNat
abbrev opType : UInt64 := UInt64.ofNat opInfoSize
abbrev opTypeNat : Nat := opInfoSize
abbrev attrs : UInt64 := ptrSize
abbrev attrsNat := ptrSizeNat
abbrev properties : UInt64 := propertySize (op.getOpType! ctx)
abbrev propertiesNat : Nat := (propertySize (op.getOpType! ctx)).toNat
abbrev numBlockOperands : UInt64 := countSize
abbrev numBlockOperandsNat := countSizeNat
abbrev blockOperands : UInt64 := UInt64.ofNat (op.get! ctx).capBlockOperands * BlockOperand.size
abbrev blockOperandsNat : Nat := (op.get! ctx).capBlockOperands * BlockOperand.sizeNat
abbrev numRegions : UInt64 := countSize
abbrev numRegionsNat := countSizeNat
abbrev regions : UInt64 := UInt64.ofNat (op.get! ctx).capRegions * ptrSize
abbrev regionsNat : Nat := (op.get! ctx).capRegions * ptrSizeNat
abbrev numOperands : UInt64 := countSize
abbrev numOperandsNat := countSizeNat
abbrev operands : UInt64 := UInt64.ofNat (op.get! ctx).capOperands * BlockOperand.size
abbrev operandsNat : Nat := (op.get! ctx).capOperands * BlockOperand.sizeNat
end Sizes
abbrev sizeBase : UInt64 :=
  Sizes.numResults + Sizes.prev + Sizes.next + Sizes.parent + Sizes.opType + Sizes.attrs +
  Sizes.numRegions + Sizes.numBlockOperands + Sizes.numBlockOperands
abbrev sizeBaseNat : Nat :=
  Sizes.numResultsNat + Sizes.prevNat + Sizes.nextNat + Sizes.parentNat + Sizes.opTypeNat + Sizes.attrsNat +
  Sizes.numRegionsNat + Sizes.numBlockOperandsNat + Sizes.numBlockOperandsNat
abbrev size : UInt64 :=
  sizeBase + Sizes.results op ctx +
  Sizes.properties op ctx +  Sizes.blockOperands op ctx +
  Sizes.regions op ctx +  Sizes.operands op ctx
abbrev sizeNat : Nat :=
  sizeBaseNat + Sizes.resultsNat op ctx +
  Sizes.propertiesNat op ctx +  Sizes.blockOperandsNat op ctx +
  Sizes.regionsNat op ctx +  Sizes.operandsNat op ctx
end Operation

namespace Block
variable [HasOpInfo OpInfo] (bl : BlockPtr) (ctx : IRContext OpInfo)
namespace Sizes
abbrev firstUse : UInt64 := ptrSize
abbrev firstUseNat := ptrSizeNat
abbrev prev : UInt64 := ptrSize
abbrev prevNat := ptrSizeNat
abbrev next : UInt64 := ptrSize
abbrev nextNat := ptrSizeNat
abbrev parent : UInt64 := ptrSize
abbrev parentNat := ptrSizeNat
abbrev firstOp : UInt64 := ptrSize
abbrev firstOpNat := ptrSizeNat
abbrev lastOp : UInt64 := ptrSize
abbrev lastOpNat := ptrSizeNat
abbrev numArguments : UInt64 := countSize
abbrev numArgumentsNat := countSizeNat
abbrev arguments : UInt64 := UInt64.ofNat (bl.get! ctx).capArguments * BlockArgument.size
abbrev argumentsNat : Nat := (bl.get! ctx).capArguments * BlockArgument.sizeNat
end Sizes

abbrev sizeBase : UInt64 :=
  Sizes.firstUse + Sizes.prev + Sizes.next + Sizes.parent + Sizes.firstOp + Sizes.lastOp +
  Sizes.numArguments

abbrev sizeBaseNat : Nat :=
  Sizes.firstUseNat + Sizes.prevNat + Sizes.nextNat + Sizes.parentNat + Sizes.firstOpNat + Sizes.lastOpNat +
  Sizes.numArgumentsNat

abbrev size : UInt64 :=
  Sizes.firstUse + Sizes.prev + Sizes.next + Sizes.parent + Sizes.firstOp + Sizes.lastOp +
  Sizes.numArguments + Sizes.arguments bl ctx

abbrev sizeNat : Nat :=
  Sizes.firstUseNat + Sizes.prevNat + Sizes.nextNat + Sizes.parentNat + Sizes.firstOpNat + Sizes.lastOpNat +
  Sizes.numArgumentsNat + Sizes.argumentsNat bl ctx
end Block

namespace Region
namespace Sizes
abbrev firstBlock : UInt64 := ptrSize
abbrev firstBlockNat := ptrSizeNat
abbrev lastBlock : UInt64 := ptrSize
abbrev lastBlockNat := ptrSizeNat
abbrev parent : UInt64 := ptrSize
abbrev parentNat := ptrSizeNat
end Sizes

abbrev size : UInt64 := Sizes.firstBlock + Sizes.lastBlock + Sizes.parent
abbrev sizeNat := Sizes.firstBlockNat + Sizes.lastBlockNat + Sizes.parentNat
end Region

/-! # Offset of the different fields. -/

namespace ValueImpl
namespace Offsets
abbrev kind : Int64 := 0
abbrev kindInt : Int := 0
abbrev type : Int64 := (0 : Int64) + Sizes.kind
abbrev typeInt : Int := (0 : Int) + Sizes.kindNat
abbrev firstUse : Int64 := type + Sizes.type
abbrev firstUseInt : Int := typeInt + Sizes.typeNat
abbrev after : Int64 := firstUse + Sizes.firstUse
abbrev afterInt : Int := firstUseInt + Sizes.firstUseNat
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end ValueImpl

namespace OpResult
namespace Offsets
abbrev index : Int64 := (0 : Int64) + ValueImpl.size
abbrev indexInt : Int := (0 : Int) + ValueImpl.sizeNat
abbrev owner : Int64 := index + Sizes.index
abbrev ownerInt : Int := indexInt + Sizes.indexNat
abbrev after : Int64 := owner + Sizes.owner
abbrev afterInt : Int := ownerInt + Sizes.ownerNat
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end OpResult

namespace BlockArgument
namespace Offsets
abbrev index : Int64 := (0 : Int64) + ValueImpl.size
abbrev indexInt : Int := (0 : Int) + ValueImpl.sizeNat
abbrev loc : Int64 := index + Sizes.index
abbrev locInt : Int := indexInt + Sizes.indexNat
abbrev owner : Int64 := loc + Sizes.loc
abbrev ownerInt : Int := locInt + Sizes.locNat
abbrev after : Int64 := owner + Sizes.owner
abbrev afterInt : Int := ownerInt + Sizes.ownerNat
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end BlockArgument

namespace OpOperand
namespace Offsets
abbrev nextUse : Int64 := 0
abbrev nextUseInt : Int := 0
abbrev back : Int64 := nextUse + Sizes.nextUse
abbrev backInt : Int := nextUseInt + Sizes.nextUseNat
abbrev owner : Int64 := back + Sizes.back
abbrev ownerInt : Int := backInt + Sizes.backNat
abbrev value : Int64 := owner + Sizes.owner
abbrev valueInt : Int := ownerInt + Sizes.ownerNat
abbrev after : Int64 := value + Sizes.value
abbrev afterInt : Int := valueInt + Sizes.valueNat
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end OpOperand

namespace BlockOperand
namespace Offsets
abbrev nextUse : Int64 := 0
abbrev nextUseInt : Int := 0
abbrev back : Int64 := nextUse + Sizes.nextUse
abbrev backInt : Int := nextUseInt + Sizes.nextUseNat
abbrev owner : Int64 := back + Sizes.back
abbrev ownerInt : Int := backInt + Sizes.backNat
abbrev value : Int64 := owner + Sizes.owner
abbrev valueInt : Int := ownerInt + Sizes.ownerNat
abbrev after : Int64 := value + Sizes.value
abbrev afterInt : Int := valueInt + Sizes.valueNat
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end BlockOperand

namespace Operation
variable [HasOpInfo OpInfo] (op : OperationPtr) (ctx : IRContext OpInfo)
namespace Offsets
abbrev results : Int64 := -((0 : Int64) + Sizes.results op ctx)
abbrev resultsInt : Int := -((0 : Int) + Sizes.resultsNat op ctx)
abbrev numResults : Int64 := 0
abbrev numResultsInt : Int := 0
abbrev prev : Int64 := Offsets.numResults + Sizes.numResults
abbrev prevInt : Int := Offsets.numResultsInt + Sizes.numResultsNat
abbrev next : Int64 := Offsets.prev + Sizes.prev
abbrev nextInt : Int := Offsets.prevInt + Sizes.prevNat
abbrev parent : Int64 := Offsets.next + Sizes.next
abbrev parentInt : Int := Offsets.nextInt + Sizes.nextNat
abbrev opType : Int64 :=  Offsets.parent + Sizes.parent
abbrev opTypeInt : Int := Offsets.parentInt + Sizes.parentNat
abbrev numBlockOperands : Int64 := Offsets.opType + Sizes.opType
abbrev numBlockOperandsInt : Int := Offsets.opTypeInt + Sizes.opTypeNat
abbrev numRegions : Int64 := Offsets.numBlockOperands + Sizes.numBlockOperands
abbrev numRegionsInt : Int := Offsets.numBlockOperandsInt + Sizes.numBlockOperandsNat
abbrev numOperands : Int64 := Offsets.numRegions + Sizes.numRegions
abbrev numOperandsInt : Int := Offsets.numRegionsInt + Sizes.numRegionsNat
abbrev attrs : Int64 := Offsets.numOperands + Sizes.numOperands
abbrev attrsInt : Int := Offsets.numOperandsInt + Sizes.numOperandsNat
abbrev properties : Int64 := Offsets.attrs + Sizes.attrs
abbrev propertiesInt : Int := Offsets.attrsInt + Sizes.attrsNat
abbrev operands : Int64 := Offsets.properties + Sizes.properties op ctx
abbrev operandsInt : Int := Offsets.propertiesInt + Sizes.propertiesNat op ctx
abbrev blockOperands : Int64 := Offsets.operands op ctx + Sizes.operands op ctx
abbrev blockOperandsInt : Int := Offsets.operandsInt op ctx + Sizes.operandsNat op ctx
abbrev regions : Int64 := Offsets.blockOperands op ctx + Sizes.blockOperands op ctx
abbrev regionsInt : Int := Offsets.blockOperandsInt op ctx + Sizes.blockOperandsNat op ctx
abbrev after : Int64 := Offsets.regions op ctx + Sizes.regions op ctx
abbrev afterInt : Int := Offsets.regionsInt op ctx + Sizes.regionsNat op ctx
end Offsets
abbrev range : Std.Rco Int := (Offsets.results op ctx).toInt...(Offsets.after op ctx).toInt
abbrev rangeInt : Std.Rco Int := (Offsets.resultsInt op ctx)...(Offsets.afterInt op ctx)
end Operation

namespace Block
variable [HasOpInfo OpInfo] (bl : BlockPtr) (ctx : IRContext OpInfo)
namespace Offsets
abbrev firstUse : Int64 := 0
abbrev firstUseInt : Int := 0
abbrev prev : Int64 := firstUse + Sizes.firstUse
abbrev prevInt : Int := firstUseInt + Sizes.firstUseNat
abbrev next : Int64 := prev + Sizes.prev
abbrev nextInt : Int := prevInt + Sizes.prevNat
abbrev parent : Int64 := next + Sizes.next
abbrev parentInt : Int := nextInt + Sizes.nextNat
abbrev firstOp : Int64 := parent + Sizes.parent
abbrev firstOpInt : Int := parentInt + Sizes.parentNat
abbrev lastOp : Int64 := firstOp + Sizes.firstOp
abbrev lastOpInt : Int := firstOpInt + Sizes.firstOpNat
abbrev numArguments : Int64 := lastOp + Sizes.lastOp
abbrev numArgumentsInt : Int := lastOpInt + Sizes.lastOpNat
abbrev arguments : Int64 := numArguments + Sizes.numArguments
abbrev argumentsInt : Int := numArgumentsInt + Sizes.numArgumentsNat
abbrev after : Int64 := arguments + Sizes.arguments bl ctx
abbrev afterInt : Int := argumentsInt + Sizes.argumentsNat bl ctx
end Offsets
abbrev range : Std.Rco Int := 0...(Offsets.after bl ctx).toInt
abbrev rangeInt : Std.Rco Int := 0...(Offsets.afterInt bl ctx)
end Block

namespace Region
namespace Offsets
abbrev firstBlock : Int64 := 0
abbrev firstBlockInt : Int := 0
abbrev lastBlock : Int64 := firstBlock + Sizes.firstBlock
abbrev lastBlockInt : Int := firstBlockInt + Sizes.firstBlockNat
abbrev parent : Int64 := lastBlock + Sizes.lastBlock
abbrev parentInt : Int := lastBlockInt + Sizes.lastBlockNat
abbrev after : Int64 := parent + Sizes.parent
abbrev afterInt : Int := parentInt + Sizes.parentNat
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end Region

section layout_preservation

variable [HasOpInfo OpInfo] (op : OperationPtr) {ctx ctx' : IRContext OpInfo}

attribute [local grind] BlockPtr.LayoutPreserved OperationPtr.LayoutPreserved IRContext.LayoutPreserved

@[layout_grind ., layout_simp]
theorem Operation.Sizes.properties_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    properties op ctx = properties op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Sizes.properties_nat_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    propertiesNat op ctx = propertiesNat op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Operation.Sizes.results_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    results op ctx = results op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Sizes.results_nat_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    resultsNat op ctx = resultsNat op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Operation.Sizes.blockOperands_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    blockOperands op ctx = blockOperands op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Sizes.blockOperands_nat_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    blockOperandsNat op ctx = blockOperandsNat op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Operation.Sizes.regions_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    regions op ctx = regions op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Sizes.regions_nat_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    regionsNat op ctx = regionsNat op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Operation.Sizes.operands_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    operands op ctx = operands op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Sizes.operands_nat_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    operandsNat op ctx = operandsNat op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Block.Sizes.arguments_layoutPreserved {bl : BlockPtr} (ib : bl.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    arguments bl ctx = arguments bl ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Block.Sizes.arguments_nat_layoutPreserved {bl : BlockPtr} (ib : bl.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    argumentsNat bl ctx = argumentsNat bl ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Operation.Offsets.results_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    results op ctx = results op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Offsets.results_int_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    resultsInt op ctx = resultsInt op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Operation.Offsets.operands_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    operands op ctx = operands op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Offsets.operands_int_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    operandsInt op ctx = operandsInt op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Operation.Offsets.blockOperands_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    blockOperands op ctx = blockOperands op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Offsets.blockOperands_int_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    blockOperandsInt op ctx = blockOperandsInt op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Operation.Offsets.regions_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    regions op ctx = regions op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Offsets.regions_int_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    regionsInt op ctx = regionsInt op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Operation.Offsets.after_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    after op ctx = after op ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Operation.Offsets.after_int_layoutPreserved {op : OperationPtr} (ib : op.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    afterInt op ctx = afterInt op ctx' :=  by
  grind

@[layout_grind ., layout_simp]
theorem Block.Offsets.after_layoutPreserved {bl : BlockPtr} (ib : bl.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    after bl ctx = after bl ctx' :=  by
  grind
@[layout_grind ., layout_simp]
theorem Block.Offsets.after_int_layoutPreserved {bl : BlockPtr} (ib : bl.InBounds ctx) (hlay : ctx.LayoutPreserved ctx') :
    afterInt bl ctx = afterInt bl ctx' :=  by
  grind
