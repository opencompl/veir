module

/-
# Custom printing interface

Types for custom (non-generic) operation printing, plus the `HasCustomPrinting`
interface through which dialects expose their operations' custom printers.

This module sits below the printer machinery (`Veir/Printer.lean`): it only
contains the types, so that dialect printing modules can define custom
printers without depending on the printer itself, and so that the printer can
depend on the dialect modules without an import cycle.
-/

public import Veir.IR.OpCode
public import Veir.IR.Basic

namespace Veir

public section

/-- Options controlling printing. Mirrors MLIR's `AsmPrinter` options. -/
structure PrinterOptions where
  /-- If true, print every operation in generic form, ignoring custom printers. -/
  printGenericOpForm : Bool := false
deriving Inhabited, DecidableEq, Repr

namespace Printer

variable {OpCode : Type} [IsOpCode OpCode]

/--
Monadic printer. Threads the `IRContext` via `Reader` and the current
indentation level via `State`. Base monad is `IO` so that the printer can write
to the output stream. Custom printers run in this monad and call the helpers
below instead of raw `IO.print`.
-/
abbrev OpPrinter (OpCode : Type) [IsOpCode OpCode] :=
  ReaderT (IRContext OpCode) (StateT Nat IO)

namespace OpPrinter

/-- Run an `OpPrinter` action. -/
def run {G : Type} [IsOpCode G]
    (ctx : IRContext G) (indent : Nat) (action : OpPrinter G α) : IO α :=
  StateT.run' (ReaderT.run action ctx) indent

/-- The `IRContext` for the current print. -/
def getContext : OpPrinter OpCode (IRContext OpCode) :=
  read

/-- Current indentation level. -/
def getIndent : OpPrinter OpCode Nat :=
  get

/-- Print a raw string to the output stream. -/
def printString (s : String) : OpPrinter OpCode Unit := do
  (IO.print s : IO Unit)

/-- Print a newline. -/
def printNewline : OpPrinter OpCode Unit := do
  (IO.println "" : IO Unit)

/-- Increase indentation by one level. -/
def increaseIndent : OpPrinter OpCode Unit :=
  modify (· + 1)

/-- Decrease indentation by one level. -/
def decreaseIndent : OpPrinter OpCode Unit :=
  modify fun n => if n == 0 then 0 else n - 1

/-- Print `indent` levels of indentation (`  ` per level). -/
def printIndent : OpPrinter OpCode Unit := do
  let n ← (get : OpPrinter OpCode Nat)
  for _ in List.range n do
    printString "  "

/-- Print a newline and then the current indentation. -/
def printNewlineAndIndent : OpPrinter OpCode Unit := do
  printNewline
  printIndent

/-- Print an SSA value (`%x`, `%x#n`, or `%argN_M`). Uses the existing value name. -/
def printOperand (value : ValuePtr) : OpPrinter OpCode Unit := do
  let ctx ← read
  match value with
  | ValuePtr.opResult opResultPtr =>
    let opResult := opResultPtr.get! ctx
    let opStruct := opResult.owner.get! ctx
    if opStruct.results.size == 1 then
      printString s!"%{opResult.owner.id}"
    else
      printString s!"%{opResult.owner.id}#{opResult.index}"
  | ValuePtr.blockArgument blockArgPtr =>
    let blockArg := blockArgPtr.get! ctx
    printString s!"%arg{blockArg.owner.id}_{blockArg.index}"

/--
Print a region argument (`%argN_M : type`). `printOperand` and
`printRegionArgument` currently do the same, but they are split so that
future allocation / shadowing logic can differ. This mirrors
MLIR's `OpAsmPrinter::printRegionArgument` vs `printOperand`.
-/
def printRegionArgument (value : ValuePtr) : OpPrinter OpCode Unit :=
  printOperand value

/-- Print a successor block `^bb1`. Mirrors `OpAsmPrinter::printSuccessor`. -/
def printSuccessor (block : BlockPtr) : OpPrinter OpCode Unit := do
  printString s!"^{block.id}"

/-- Print an attribute dictionary ` { "k" = v }` if non-empty after eliding. -/
def printOptionalAttrDict (attrs : DictionaryAttr) (elided : Array String := #[]) : OpPrinter OpCode Unit := do
  let elidedBytes := elided.map (·.toUTF8)
  let filtered := attrs.entries.filter fun (k, _) => !elidedBytes.contains k
  if filtered.isEmpty then return
  printString " "
  printString s!"{DictionaryAttr.fromArray filtered}"

/-- Print ` attributes { ... }` if non-empty after eliding, like MLIR's `printOptionalAttrDictWithKeyword`. -/
def printOptionalAttrDictWithKeyword (attrs : DictionaryAttr) (elided : Array String := #[]) : OpPrinter OpCode Unit := do
  let elidedBytes := elided.map (·.toUTF8)
  let filtered := attrs.entries.filter fun (k, _) => !elidedBytes.contains k
  if filtered.isEmpty then return
  printString " attributes "
  printString s!"{DictionaryAttr.fromArray filtered}"

end OpPrinter

/--
Printing capabilities available to a custom (non-generic) operation printer.

A custom printer is defined outside of the recursive printer family (e.g., in
the dialect's printing module), so it cannot call `printRegion` directly;
instead it receives an `env` record with that entry point, mirroring MLIR's
`OpAsmPrinter::printRegion`. Leaf helpers like `printOperand` are also
exposed here for uniformity, but they are also available as `OpPrinter.*`
free functions.
-/
structure PrintEnv (OpCode : Type) [IsOpCode OpCode] where
  /-- Print an SSA value. -/
  printOperand : ValuePtr → OpPrinter OpCode Unit
  /-- Print a region argument (block argument). -/
  printRegionArgument : ValuePtr → OpPrinter OpCode Unit
  /-- Print a successor block. -/
  printSuccessor : BlockPtr → OpPrinter OpCode Unit
  /-- Print an attribute dictionary if non-empty. -/
  printOptionalAttrDict : DictionaryAttr → Array String → OpPrinter OpCode Unit
  /-- Print `attributes` keyword and dictionary if non-empty. -/
  printOptionalAttrDictWithKeyword : DictionaryAttr → Array String → OpPrinter OpCode Unit
  /-- Print a region, optionally eliding the entry block's arguments. -/
  printRegion : Region → (printEntryBlockArgs : Bool) → OpPrinter OpCode Unit

/--
A custom (non-generic) printer for one operation. The dispatcher prints the
indentation, the `%x = ` prefix and the operation name; the registered printer
handles everything after the name, recursing only through `env`.

Runs in `OpPrinter` (so `indent` is in `State` and `IRContext` is in `Reader`);
the custom printer should use `OpPrinter.printString` etc. instead of raw
`IO.print`, and `env.printRegion` to recurse.
-/
abbrev CustomPrinter (OpCode : Type) [IsOpCode OpCode] :=
  PrintEnv OpCode → OperationPtr → OpPrinter OpCode Unit

end Printer

/-- Interface that stores each operation's custom printer. -/
class HasCustomPrinting (OpCode : Type) [IsOpCode OpCode] where
  /-- The custom printer for an operation of this type, if it has one. -/
  customPrinter? : OpCode → Option (Printer.CustomPrinter OpCode) := fun _ => none

end -- public section

end Veir
