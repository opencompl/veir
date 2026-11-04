module

public import Veir.Parser.Scopes
public import Veir.Parser.Syntax

@[expose] public section
namespace Veir.Parser

structure ResolvedValues (before : StaticParserState) extends ParserStep before where
  values : Array IR.Value
  inBounds : ∀ v ∈ values, v.InBounds state.ctx.raw
  preserves : StaticIR.Preserves before.ctx.raw state.ctx.raw
  blocks : state.data.blocks = before.data.blocks
  suspended : state.data.blockScopes = before.data.blockScopes

def resolveOperandList (s : StaticParserState) (operands : List (Syntax.UnresolvedOperand × TypeAttr))
    (acc : Array IR.Value) : (∀ v ∈ acc, v.InBounds s.ctx.raw) →
    Except ParserError (ResolvedValues s) :=
  match operands with
  | [] => fun hacc => pure ⟨⟨s, ParserFrame.refl s⟩, acc, hacc, StaticIR.Preserves.refl s.ctx.raw, rfl, rfl⟩
  | (operand, ty) :: rest => fun hacc => do
    let value ← s.useValue operand.name operand.index ty operand.pos
    have hp : ∀ v ∈ acc.push value.pointer, v.InBounds value.state.ctx.raw := by
      intro v he
      rcases Array.mem_push.mp he with he | rfl
      · exact value.preserves.value (hacc v he)
      · exact value.inBounds
    let tail ← resolveOperandList value.state rest (acc.push value.pointer) hp
    return ⟨⟨tail.state, value.frame.trans tail.frame⟩, tail.values, tail.inBounds,
      value.preserves.trans tail.preserves, tail.blocks.trans value.blocks, tail.suspended.trans value.suspended⟩
termination_by operands.length

def BlockMention (data : MlirParserData) (block : IR.Block) : Prop :=
  ∃ name entry, data.blockEntry? 0 name = some entry ∧ entry.block = block

structure ResolvedSuccessors (before : StaticParserState) extends ParserStep before where
  blocks : Array IR.Block
  mentions : ∀ p ∈ blocks, BlockMention state.data p
  preserves : StaticIR.Preserves before.ctx.raw state.ctx.raw
  bindings : ∀ scope name entry, before.data.blockEntry? scope name = some entry →
    state.data.blockEntry? scope name = some entry
  suspended : state.data.blockScopes = before.data.blockScopes

def resolveSuccessorList (s : StaticParserState) (names : List (ByteArray × Location))
    (acc : Array IR.Block) : (∀ p ∈ acc, BlockMention s.data p) →
    Except ParserError (ResolvedSuccessors s) :=
  match names with
  | [] => fun hacc => pure ⟨⟨s, ParserFrame.refl s⟩, acc, hacc, StaticIR.Preserves.refl s.ctx.raw,
      fun _ _ _ h => h, rfl⟩
  | (name, loc) :: rest => fun hacc => do
    let block ← s.borrowBlock name loc
    have hp : ∀ p ∈ acc.push block.pointer, BlockMention block.state.data p := by
      intro p he
      rcases Array.mem_push.mp he with he | rfl
      · obtain ⟨n, e, he, hp⟩ := hacc p he
        exact ⟨n, e, block.bindings 0 n e he, hp⟩
      · obtain ⟨e, he, hp⟩ := block.named
        exact ⟨name, e, he, hp⟩
    let tail ← resolveSuccessorList block.state rest (acc.push block.pointer) hp
    return ⟨⟨tail.state, block.frame.trans tail.frame⟩, tail.blocks, tail.mentions,
      block.preserves.trans tail.preserves, fun scope n e he => tail.bindings scope n e (block.bindings scope n e he),
      tail.suspended.trans block.suspended⟩
termination_by names.length

namespace Syntax

def parseBlockName : SyntaxM (ByteArray × Location) := do
  let token ← parseToken .caretIdent "block name expected"
  let name := { token.slice with start := token.slice.start + 1 }.of (← getInput)
  return (name, token.slice.start)

def parseBlockNames : SyntaxM (Array (ByteArray × Location)) := do
  return (← parseOptionalDelimitedList .square parseBlockName).getD #[]

end Syntax
end Veir.Parser
