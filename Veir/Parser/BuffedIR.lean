module

public import Veir.Rewriter.Basic
public import Veir.Rewriter.EraseContainers
public import Veir.GlobalOpInfo

/-!
# IR construction primitives for the parser

The parser carries `Sim` contexts and pointers directly. Their specification fields are
`Erased`, so construction preserves the specification without evaluating it at runtime.
Operand, successor, and region collections are ordinary arrays of simulated pointers.

As in the original parser and the benchmarks, the rewriter's proof obligations below are
not yet verified. Keeping those obligations here isolates this unverified construction
boundary from the lexer and parser. No generated implementations or dummy specifications
are needed.
-/

public section

namespace Veir.Parser.IR

open Veir

set_option warn.sorry false

abbrev Context := Sim.IRContext OpCode
abbrev Op := Sim.OperationPtr
abbrev Block := Sim.BlockPtr
abbrev Region := Sim.RegionPtr
abbrev Value := Sim.ValuePtr

/-- A fresh, empty context with its erased specification. -/
@[inline]
def empty : Context := Sim.IRContext.empty

/-- Create an operation, optionally inserting it at `ip`. -/
@[noinline]
def createOp (ctx : Context) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array Value) (blockOperands : Array Block) (regions : Array Region)
    (properties : propertiesOf opType) (ip : Option InsertPoint) : Option (Context × Op) :=
  Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties ip
    sorry sorry sorry sorry sorry sorry sorry

/-- Create a block with the given argument types, optionally inserting it at `ip`. -/
@[noinline]
def createBlock (ctx : Context) (argTypes : Array TypeAttr) (ip : Option BlockInsertPoint) :
    Option (Context × Block) :=
  Rewriter.createBlock ctx argTypes ip sorry sorry

/-- Insert a detached block at `ip`. -/
@[noinline]
def insertBlock (ctx : Context) (block : Block) (ip : BlockInsertPoint) : Option Context :=
  Rewriter.insertBlock? ctx block ip sorry sorry sorry sorry

/-- Create a detached region. -/
@[noinline]
def createRegion (ctx : Context) : Option (Context × Region) :=
  Rewriter.createRegion ctx

/-- Set the attribute dictionary of an operation. -/
@[noinline]
def setAttributes (ctx : Context) (op : Op) (attrs : DictionaryAttr) : Option Context :=
  Sim.OperationPtr.setAttributes ctx op attrs sorry

/-- Replace every use of `oldValue` by `newValue`. -/
@[noinline]
def replaceValue (ctx : Context) (oldValue newValue : Value) : Option Context :=
  Rewriter.replaceValue? ctx oldValue newValue sorry sorry sorry

/-- Erase an operation that has no regions and whose results have no uses. -/
@[noinline]
def eraseOp (ctx : Context) (op : Op) : Context :=
  Rewriter.eraseOp ctx op sorry sorry sorry sorry sorry

/-- Erase a detached block that has no operations and no uses. -/
@[noinline]
def eraseBlock (ctx : Context) (block : Block) : Context :=
  Rewriter.eraseBlock ctx block sorry sorry sorry

/-- Redirect every use of `oldBlock` to `newBlock`. Inspect the use list before mutating
    the context, so the loop does not retain an old buffer across each rewrite. -/
partial def replaceBlockUses (ctx : Context) (oldBlock newBlock : Block) : Context :=
  match (oldBlock.getFirstUse ctx sorry).toOption with
  | none => ctx
  | some use =>
    let ctx := use.removeFromCurrent ctx sorry sorry
    let ctx := use.setValue ctx newBlock sorry sorry
    let ctx := use.insertIntoCurrent ctx sorry sorry
    replaceBlockUses ctx oldBlock newBlock

/-- The `index`-th result of `op`, as a value with its erased specification. -/
@[inline]
def opResult (ctx : Context) (op : Op) (index : UInt64) : Value :=
  Sim.ValuePtr.fromOpResultPtr (op.getResultPtr! ctx index)

/-- The `index`-th argument of `block`, as a value with its erased specification. -/
@[inline]
def blockArgument (ctx : Context) (block : Block) (index : UInt64) : Value :=
  Sim.ValuePtr.fromBlockArgumentPtr (block.getArgumentPtr! ctx index)

/-- The type of a value. -/
@[inline]
def valueType (ctx : Context) (value : Value) : Attribute :=
  ctx.buf.attributes[(Buffed.ValueImplMPtr.readType! ctx.buf value.impl).toNat]!

end Veir.Parser.IR

end
