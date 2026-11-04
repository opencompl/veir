module

public import Veir.Prelude
public import Veir.IR.Basic
public import Veir.IR.LayoutUnchanged
public import Lean

/-! # Sizes of the different fields, in bytes.

Derived sizes and offsets are spelled as literals: the compiler does not constant-fold
`UInt64`/`Int64` arithmetic, so symbolic sums compile to runtime once-cell chains. -/

@[expose] public section

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
abbrev size : UInt64 := 24
abbrev sizeNat : Nat := 24
end ValueImpl

namespace OpResult
namespace Sizes
abbrev index : UInt64 := ptrSize
abbrev indexNat := ptrSizeNat
abbrev owner : UInt64 := ptrSize
abbrev ownerNat := ptrSizeNat
end Sizes
abbrev size : UInt64 := 40
abbrev sizeNat : Nat := 40
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
abbrev size : UInt64 := 40
abbrev sizeNat : Nat := 40
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
abbrev size : UInt64 := 32
abbrev sizeNat : Nat := 32
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
abbrev size : UInt64 := 32
abbrev sizeNat : Nat := 32
end BlockOperand

namespace Operation
variable [HasOpInfo OpInfo] (op : OperationPtr) (ctx : IRContext OpInfo)

@[inline]
def propertySize (opCode : OpInfo) : UInt64 := HasDialectOpInfo.propertySize opCode
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
abbrev sizeBase : UInt64 := 72
abbrev sizeBaseNat : Nat := 72
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

abbrev sizeBase : UInt64 := 56
abbrev sizeBaseNat : Nat := 56

abbrev size : UInt64 := 56 + Sizes.arguments bl ctx
abbrev sizeNat : Nat := 56 + Sizes.argumentsNat bl ctx
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

abbrev size : UInt64 := 24
abbrev sizeNat : Nat := 24
end Region

/-! # Offset of the different fields. -/

namespace ValueImpl
namespace Offsets
abbrev kind : Int64 := 0
abbrev kindInt : Int := 0
abbrev type : Int64 := 8
abbrev typeInt : Int := 8
abbrev firstUse : Int64 := 16
abbrev firstUseInt : Int := 16
abbrev after : Int64 := 24
abbrev afterInt : Int := 24
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end ValueImpl

namespace OpResult
namespace Offsets
abbrev index : Int64 := 24
abbrev indexInt : Int := 24
abbrev owner : Int64 := 32
abbrev ownerInt : Int := 32
abbrev after : Int64 := 40
abbrev afterInt : Int := 40
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end OpResult

namespace BlockArgument
namespace Offsets
abbrev index : Int64 := 24
abbrev indexInt : Int := 24
abbrev loc : Int64 := 32
abbrev locInt : Int := 32
abbrev owner : Int64 := 32
abbrev ownerInt : Int := 32
abbrev after : Int64 := 40
abbrev afterInt : Int := 40
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end BlockArgument

namespace OpOperand
namespace Offsets
abbrev nextUse : Int64 := 0
abbrev nextUseInt : Int := 0
abbrev back : Int64 := 8
abbrev backInt : Int := 8
abbrev owner : Int64 := 16
abbrev ownerInt : Int := 16
abbrev value : Int64 := 24
abbrev valueInt : Int := 24
abbrev after : Int64 := 32
abbrev afterInt : Int := 32
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
abbrev rangeInt : Std.Rco Int := 0...Offsets.afterInt
end OpOperand

namespace BlockOperand
namespace Offsets
abbrev nextUse : Int64 := 0
abbrev nextUseInt : Int := 0
abbrev back : Int64 := 8
abbrev backInt : Int := 8
abbrev owner : Int64 := 16
abbrev ownerInt : Int := 16
abbrev value : Int64 := 24
abbrev valueInt : Int := 24
abbrev after : Int64 := 32
abbrev afterInt : Int := 32
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
abbrev prev : Int64 := 8
abbrev prevInt : Int := 8
abbrev next : Int64 := 16
abbrev nextInt : Int := 16
abbrev parent : Int64 := 24
abbrev parentInt : Int := 24
abbrev opType : Int64 := 32
abbrev opTypeInt : Int := 32
abbrev numBlockOperands : Int64 := 40
abbrev numBlockOperandsInt : Int := 40
abbrev numRegions : Int64 := 48
abbrev numRegionsInt : Int := 48
abbrev numOperands : Int64 := 56
abbrev numOperandsInt : Int := 56
abbrev attrs : Int64 := 64
abbrev attrsInt : Int := 64
abbrev properties : Int64 := 72
abbrev propertiesInt : Int := 72
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
abbrev prev : Int64 := 8
abbrev prevInt : Int := 8
abbrev next : Int64 := 16
abbrev nextInt : Int := 16
abbrev parent : Int64 := 24
abbrev parentInt : Int := 24
abbrev firstOp : Int64 := 32
abbrev firstOpInt : Int := 32
abbrev lastOp : Int64 := 40
abbrev lastOpInt : Int := 40
abbrev numArguments : Int64 := 48
abbrev numArgumentsInt : Int := 48
abbrev arguments : Int64 := 56
abbrev argumentsInt : Int := 56
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
abbrev lastBlock : Int64 := 8
abbrev lastBlockInt : Int := 8
abbrev parent : Int64 := 16
abbrev parentInt : Int := 16
abbrev after : Int64 := 24
abbrev afterInt : Int := 24
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
