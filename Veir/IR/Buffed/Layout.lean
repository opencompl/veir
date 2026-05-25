module

public import Veir.IR.Basic

/-! # Sizes of the different fields, in bytes. -/

public section

instance : HAdd UInt64 Int64 UInt64 where
  hAdd x y := x.toInt64 + y |>.toUInt64
instance : HAdd Int64 UInt64 Int64 where
  hAdd x y := x + y.toInt64

theorem UInt64.add_int64_pos (x : UInt64) (y : Int64) : (x + y).toNat = x.toNat + y.toInt := by
  sorry

namespace Veir.Buffed

abbrev ptrSize : UInt64 := 8
abbrev countSize : UInt64 := 8
abbrev ptrCard : Nat := UInt64.size
abbrev countCard : Nat := UInt32.size

namespace ValueImpl
namespace Sizes
abbrev type : UInt64 := ptrSize
abbrev firstUse : UInt64 := ptrSize
end Sizes
abbrev size : UInt64 := ValueImpl.Sizes.type + ValueImpl.Sizes.firstUse
end ValueImpl

namespace OpResult
namespace Sizes
abbrev index : UInt64 := ptrSize
abbrev owner : UInt64 := ptrSize
end Sizes
abbrev size : UInt64 := ValueImpl.size + Sizes.index + Sizes.owner
end OpResult

namespace BlockArgument
namespace Sizes
abbrev index : UInt64 := ptrSize
abbrev loc : UInt64 := 0
abbrev owner : UInt64 := ptrSize
end Sizes
abbrev size : UInt64 := ValueImpl.size + Sizes.index + Sizes.loc + Sizes.owner
end BlockArgument

namespace OpOperand
namespace Sizes
abbrev nextUse : UInt64 := ptrSize
abbrev back : UInt64 := ptrSize
abbrev owner : UInt64 := ptrSize
abbrev value : UInt64 := ptrSize
end Sizes
abbrev size : UInt64 := Sizes.nextUse + Sizes.back + Sizes.owner + Sizes.value
end OpOperand

namespace BlockOperand
namespace Sizes
abbrev nextUse : UInt64 := ptrSize
abbrev back : UInt64 := ptrSize
abbrev owner : UInt64 := ptrSize
abbrev value : UInt64 := ptrSize
end Sizes
abbrev size : UInt64 := Sizes.nextUse + Sizes.back + Sizes.owner + Sizes.value
end BlockOperand

namespace Operation
variable [HasOpInfo OpInfo] (op : OperationPtr) (ctx : IRContext OpInfo)

-- Add this info to the typeclasses
def propertySize (opCode : OpInfo) : UInt64 := 8 -- sorry
@[inline] abbrev opInfoSize : Nat := 8
def decodeOpInfo (x : UInt32) : OpInfo := default --sorry

namespace Sizes
abbrev results : UInt64 := UInt64.ofNat (op.get! ctx).capResults * OpResult.size
abbrev numResults : UInt64 := countSize
abbrev prev : UInt64 := ptrSize
abbrev next : UInt64 := ptrSize
abbrev parent : UInt64 := ptrSize
abbrev opType : UInt64 := UInt64.ofNat opInfoSize
abbrev attrs : UInt64 := ptrSize
abbrev properties : UInt64 := propertySize (op.getOpType! ctx)
abbrev numBlockOperands : UInt64 := countSize
abbrev blockOperands : UInt64 := UInt64.ofNat (op.get! ctx).capBlockOperands * BlockOperand.size
abbrev numRegions : UInt64 := countSize
abbrev regions : UInt64 := UInt64.ofNat (op.get! ctx).capRegions * ptrSize
abbrev numOperands : UInt64 := countSize
abbrev operands : UInt64 := UInt64.ofNat (op.get! ctx).capOperands * BlockOperand.size
end Sizes
abbrev sizeBase : UInt64 :=
  Sizes.numResults + Sizes.prev + Sizes.next + Sizes.parent + Sizes.opType + Sizes.attrs +
  Sizes.numRegions + Sizes.numBlockOperands + Sizes.numBlockOperands
abbrev size : UInt64 :=
  sizeBase + Sizes.results op ctx +
  Sizes.properties op ctx +  Sizes.blockOperands op ctx +
  Sizes.regions op ctx +  Sizes.operands op ctx
end Operation

namespace Block
variable [HasOpInfo OpInfo] (bl : BlockPtr) (ctx : IRContext OpInfo)
namespace Sizes
abbrev firstUse : UInt64 := ptrSize
abbrev prev : UInt64 := ptrSize
abbrev next : UInt64 := ptrSize
abbrev parent : UInt64 := ptrSize
abbrev firstOp : UInt64 := ptrSize
abbrev lastOp : UInt64 := ptrSize
abbrev numArguments : UInt64 := countSize
abbrev arguments : UInt64 := UInt64.ofNat (bl.get! ctx).capArguments * BlockArgument.size
end Sizes

abbrev sizeBase : UInt64 :=
  Sizes.firstUse + Sizes.prev + Sizes.next + Sizes.parent + Sizes.firstOp + Sizes.lastOp +
  Sizes.numArguments

abbrev size : UInt64 :=
  Sizes.firstUse + Sizes.prev + Sizes.next + Sizes.parent + Sizes.firstOp + Sizes.lastOp +
  Sizes.numArguments + Sizes.arguments bl ctx
end Block

namespace Region
namespace Sizes
abbrev firstBlock : UInt64 := ptrSize
abbrev lastBlock : UInt64 := ptrSize
abbrev parent : UInt64 := ptrSize
end Sizes

abbrev size : UInt64 := Sizes.firstBlock + Sizes.lastBlock + Sizes.parent
end Region

/-! # Offset of the different fields. -/

namespace ValueImpl
namespace Offsets
abbrev type : Int64 := 0
abbrev firstUse : Int64 := type + Sizes.type
abbrev after : Int64 := firstUse + Sizes.firstUse
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
end ValueImpl

namespace OpResult
namespace Offsets
abbrev index : Int64 := (0 : Int64) + ValueImpl.size
abbrev owner : Int64 := index + Sizes.index
abbrev after : Int64 := owner + Sizes.owner
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
end OpResult

namespace BlockArgument
namespace Offsets
abbrev index : Int64 := (0 : Int64) + ValueImpl.size
abbrev loc : Int64 := index + Sizes.index
abbrev owner : Int64 := loc + Sizes.loc
abbrev after : Int64 := owner + Sizes.owner
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
end BlockArgument

namespace OpOperand
namespace Offsets
abbrev nextUse : Int64 := 0
abbrev back : Int64 := nextUse + Sizes.nextUse
abbrev owner : Int64 := back + Sizes.back
abbrev value : Int64 := owner + Sizes.owner
abbrev after : Int64 := value + Sizes.value
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
end OpOperand

namespace BlockOperand
namespace Offsets
abbrev nextUse : Int64 := 0
abbrev back : Int64 := nextUse + Sizes.nextUse
abbrev owner : Int64 := back + Sizes.back
abbrev value : Int64 := owner + Sizes.owner
abbrev after : Int64 := value + Sizes.value
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
end BlockOperand

namespace Operation
variable [HasOpInfo OpInfo] (op : OperationPtr) (ctx : IRContext OpInfo)
namespace Offsets
abbrev results : Int64 := -((0 : Int64) + Sizes.results op ctx)
abbrev numResults : Int64 := 0
abbrev prev : Int64 := Offsets.numResults + Sizes.numResults
abbrev next : Int64 := Offsets.prev + Sizes.prev
abbrev parent : Int64 := Offsets.next + Sizes.next
abbrev opType : Int64 :=  Offsets.parent + Sizes.parent
abbrev numBlockOperands : Int64 := Offsets.opType + Sizes.opType
abbrev numRegions : Int64 := Offsets.numBlockOperands + Sizes.numBlockOperands
abbrev numOperands : Int64 := Offsets.numRegions + Sizes.numRegions
abbrev attrs : Int64 := Offsets.numOperands + Sizes.numOperands
abbrev properties : Int64 := Offsets.attrs + Sizes.attrs
abbrev operands : Int64 := Offsets.properties + Sizes.properties op ctx
abbrev blockOperands : Int64 := Offsets.operands op ctx + Sizes.operands op ctx
abbrev regions : Int64 := Offsets.blockOperands op ctx + Sizes.blockOperands op ctx
abbrev after : Int64 := Offsets.regions op ctx + Sizes.regions op ctx
end Offsets
abbrev range : Std.Rco Int := (Offsets.results op ctx).toInt...(Offsets.after op ctx).toInt
end Operation

namespace Block
variable [HasOpInfo OpInfo] (bl : BlockPtr) (ctx : IRContext OpInfo)
namespace Offsets
abbrev firstUse : Int64 := 0
abbrev prev : Int64 := firstUse + Sizes.firstUse
abbrev next : Int64 := prev + Sizes.prev
abbrev parent : Int64 := next + Sizes.next
abbrev firstOp : Int64 := parent + Sizes.parent
abbrev lastOp : Int64 := firstOp + Sizes.firstOp
abbrev numArguments : Int64 := lastOp + Sizes.lastOp
abbrev arguments : Int64 := numArguments + Sizes.numArguments
abbrev after : Int64 := arguments + Sizes.arguments bl ctx
end Offsets
abbrev range : Std.Rco Int := 0...(Offsets.after bl ctx).toInt
end Block

namespace Region
namespace Offsets
abbrev firstBlock : Int64 := 0
abbrev lastBlock : Int64 := firstBlock + Sizes.firstBlock
abbrev parent : Int64 := lastBlock + Sizes.lastBlock
abbrev after : Int64 := parent + Sizes.parent
end Offsets
abbrev range : Std.Rco Int := 0...Offsets.after.toInt
end Region
