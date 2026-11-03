module

public import Veir.Buffered.Parser.ConstructionParser

public section
namespace Veir.Buffered.Parser

/-- The source bytes and historical operation locations. These locations confer no liveness
and are never used as a pointer-validation table. -/
structure SourceInfo where
  sourceName : String
  content : ByteArray
  opLocations : Std.HashMap Buffed.OperationMPtr Location

def SourceInfo.opLocation? (info : SourceInfo) (op : IR.Op) : Option Location :=
  info.opLocations[op.impl]?

/-- Parse directly into the registry-free context. Every construction input is justified by
an erased certificate from allocation, the live name tables, or a recursive action's frame.
Root liveness follows from its construction certificate; there is no final address lookup. -/
def parseSourceString (content : ByteArray) (sourceName : String := "<string>")
    (allowUnregisteredDialect : Bool := false) :
    Except String (StaticIR.Context × IR.Op × SourceInfo) := do
  match ParserState.fromInput content with
  | .error err => throw (err.format sourceName content)
  | .ok parser =>
    let state := StaticParserState.initial allowUnregisteredDialect
    let config : Veir.Buffered.AttrParser.AttrParserState := { allowUnregisteredDialect }
    match (Construction.topLevel state config).run parser with
    | .error err _ => throw (err.format sourceName content)
    | .ok (parsed, _) _ =>
      return (parsed.state.ctx, parsed.pointer,
        { sourceName, content, opLocations := parsed.state.data.opLocations })

/-- Successful parsing returns a structurally well-formed context and a live root. These
facts come from the parser's static result type, not runtime reference validation. This does
not assert MLIR type, dominance, or dialect correctness. -/
theorem parseSourceString_safe {content : ByteArray} {sourceName : String}
    {allowUnregisteredDialect : Bool} {ctx : StaticIR.Context} {op : IR.Op} {info : SourceInfo}
    (h : parseSourceString content sourceName allowUnregisteredDialect = .ok (ctx, op, info)) :
    ctx.spec.WellFormed ∧ op.InBounds ctx.toIRContext := by
  unfold parseSourceString at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h
      exact ⟨StaticIR.Context.wellFormed _, ParsedOperation.inBounds _⟩

end Veir.Buffered.Parser
