module

/-
  # Source-location utilities and structured parse errors.

  This file contains the `ParserError` and `ParserErrorNote` type and related utilities for
  formatting this error into a clang/MLIR-style caret diagnostic that prints the offending
  source line with a `^` pointing to the error column.
-/

namespace Veir.Parser

public section

/-!
  ## ParserError and ParserErrorNote

  These two classes are used to represent structured parse errors with optional source locations.
  `ParserError` represents a primary error with an optional source location and a list of secondary
  notes. Each note is represented by a `ParserErrorNote`, which has its own message and source
  location.
-/

/-- A secondary diagnostic location attached to a `ParserError`. -/
structure ParserErrorNote where
  msg : String
  pos : Nat
deriving Inhabited, DecidableEq, Repr

/-- Structured parse error carrying an optional source location and notes. -/
structure ParserError where
  msg : String
  pos : Option Nat := none
  notes : List ParserErrorNote := []
deriving Inhabited, DecidableEq, Repr

def ParserError.addNote (e : ParserError) (pos : Nat) (msg : String) : ParserError :=
  { e with notes := e.notes ++ [{ msg, pos }] }

end

namespace ParserError

/-!
  ## Parser error formatting

  The following functions are used to format a `ParserError` into a human-readable diagnostic message
  that includes the source line and a caret pointing to the error location. The main public function is
  `ParserError.format`, which takes a `ParserError` and the source filename and content, and produces a
  formatted error string.
-/

/--
  Compute the 1-based line and 1-based column for `loc`.

  The line is one plus the number of `\n` bytes strictly before the offset.
  The column is the byte distance from the start of the current line, plus one.
  This assumes that only ASCII characters are present.
-/
def byteOffsetToLineCol (input : ByteArray) (loc : Nat) : Nat × Nat := Id.run do
  let offset := min loc input.size
  let mut line := 1
  let mut lineStart := 0
  for i in [0:offset] do
    if input.get! i == '\n'.toUInt8 then
      line := line + 1
      lineStart := i + 1
  return (line, offset - lineStart + 1)

/--
  The line containing `loc` in the source code: the bytes after the previous
  `\n` (or the start of input) up to the next `\n` (or end of input), decoded as
  UTF-8. Returns `none` if the bytes are not valid UTF-8.
-/
def lineContaining (input : ByteArray) (loc : Nat) : Option String := Id.run do
  let offset := min loc input.size
  let mut start := 0
  for i in [0:offset] do
    if input.get! i == '\n'.toUInt8 then
      start := i + 1
  let mut stop := input.size
  for i in [offset:input.size] do
    if input.get! i == '\n'.toUInt8 then
      stop := i
      break
  return String.fromUTF8? (input.extract start stop)

/--
  Emit a single diagnostic label:

  ```
  filename:line:col: <severity>: msg
  <source line>
  <caret line>
  ```

  `severity` is usually `"error"` or `"note"`. The caret line reuses the source
  line's prefix, replacing every non-tab character with a space while keeping
  tabs intact, so the `^` aligns with the offending column even on
  tab-indented lines.

  When the offending line cannot be decoded as UTF-8 (the parser only handles
  ASCII, so this means a stray non-ASCII byte), the source line and caret are
  replaced by an explanatory line, since neither can be rendered meaningfully.

  When `loc` is `none`, the header uses `<unknown location>` and no source line
  is printed.
-/
def formatLabel (filename : String) (input : ByteArray) (severity : String) (loc : Option Nat)
    (msg : String) : String :=
  match loc with
  | none => s!"<unknown location>: {severity}: {msg}"
  | some loc =>
    let (line, col) := byteOffsetToLineCol input loc
    let header := s!"{filename}:{line}:{col}: {severity}: {msg}"
    match lineContaining input loc with
    | some srcLine =>
      let prefixChars := srcLine.toList.take (col - 1)
      let caretPrefix := String.ofList (prefixChars.map (fun c => if c == '\t' then '\t' else ' '))
      s!"{header}\n{srcLine}\n{caretPrefix}^"
    | none =>
      s!"{header}\n    <source line not shown: it contains a non-ASCII byte>"

public section

/--
  Render one primary `error` label followed by a `note` label per entry in
  `e.notes`, each via `formatLabel`. The primary location is taken from `e.pos`.
-/
def format (e : ParserError) (filename : String) (input : ByteArray) : String :=
  let primary := formatLabel filename input "error" e.pos e.msg
  e.notes.foldl
    (fun acc note => acc ++ "\n" ++ formatLabel filename input "note" (some note.pos) note.msg)
    primary


end -- public section

end Veir.Parser.ParserError
