import Veir.Parser.MlirParser
import Veir.Parser.ParserError
import Veir.GlobalOpInfo

/-!
  Helpers shared by the VeIR command-line tools (`veir-opt`, `veir-interpret`,
  `veir2mir`) for reading an input program from a file or from standard input
  and parsing it into a well-formed IR context.

  When no file argument is given, the program is read from standard input.
 -/

open Veir.Parser
open Veir

namespace Veir.Input

/-- Read the input program from `filename`, or from standard input when it is
    `none`. -/
def getFileContent (filename : Option String) : ExceptT String IO ByteArray := do
  if let some f := filename then
    try
      return ← IO.FS.readBinFile f
    catch e =>
      throw s!"Error reading file '{f}': {e}"
  return ← IO.FS.Stream.readBinToEnd (←IO.getStdin)

/--
  The source input of a parsed program, along with the location of each parsed operation.
-/
structure SourceInfo where
  /-- The name of the source. -/
  sourceName : String
  /-- The content of the source. -/
  content : ByteArray
  /-- The location in `content` for each parsed operation. -/
  opLocations : Std.HashMap OperationPtr Parser.Location

/--
  Format a caret-style diagnostic about `op`.
  The location is <unknown location> if `op` was not parsed from the source.
-/
def SourceInfo.formatAt (info : SourceInfo) (op : OperationPtr) (severity msg : String) : String :=
  ParserError.formatLabel info.sourceName info.content severity info.opLocations[op]? msg

/-- Parse program bytes into a well-formed IR context and its top-level
    operation, formatting parse errors caret-style against `sourceName`. -/
def parseContent (content : ByteArray) (sourceName : String)
    (allowUnregisteredDialect : Bool) :
    ExceptT String IO (WfIRContext OpCode × OperationPtr × SourceInfo) := do
  let some (ctx, _) := WfIRContext.create OpCode
    | throw "Failed to create IR context"
  match ParserState.fromInput content with
  | .ok parser =>
    let state := MlirParserState.fromContext ctx allowUnregisteredDialect
    match parseTopLevelOp.run state parser with
    | .ok (op, state, _) =>
      return (state.ctx, op, { sourceName, content, opLocations := state.opLocations })
    | .error err =>
      throw (err.format sourceName content)
  | .error err =>
    throw (err.format sourceName content)

/-- Read and parse the input program, naming the source `<stdin>` when it comes
    from standard input. -/
def parseOperation (filename : Option String) (allowUnregisteredDialect : Bool := false) :
    ExceptT String IO (WfIRContext OpCode × OperationPtr × SourceInfo) := do
  let content ← getFileContent filename
  let sourceName := if let some f := filename then f else "<stdin>"
  parseContent content sourceName allowUnregisteredDialect

/-- Map positional CLI arguments to an input source: `[]` means standard input;
    a single argument names the input file. -/
def inputSourceOfArgs (positional : List String) : Except String (Option String) :=
  match positional with
  | [] => .ok none
  | [filename] => .ok (some filename)
  | _ => .error "Expected at most one positional argument for the input filename."

end Veir.Input
