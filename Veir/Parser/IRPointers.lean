module

public import Veir.GlobalOpInfo
public import Veir.Rewriter.WellFormed.CreateIRContext

public section
namespace Veir.Parser.IR

abbrev RawContext := Sim.IRContext OpCode
abbrev Op := Sim.OperationPtr
abbrev Block := Sim.BlockPtr
abbrev Region := Sim.RegionPtr
abbrev Value := Sim.ValuePtr

/-- Unchecked accessors for the printer. Construction uses the proof-taking accessors in
`StaticIR`, `ResultLive`, and `ArgumentLive`. -/
@[inline]
def opResult (ctx : RawContext) (op : Op) (index : UInt64) : Value :=
  Sim.ValuePtr.fromOpResultPtr (op.getResultPtr! ctx index)

@[inline]
def blockArgument (ctx : RawContext) (block : Block) (index : UInt64) : Value :=
  Sim.ValuePtr.fromBlockArgumentPtr (block.getArgumentPtr! ctx index)

@[inline]
def valueType (ctx : RawContext) (value : Value) : Attribute :=
  ctx.buf.attributes[(Buffed.ValueImplMPtr.readType! ctx.buf value.impl).toNat]!

end Veir.Parser.IR
