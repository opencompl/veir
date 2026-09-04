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

/-- Context and recursive services for an `OpPrinter` action. -/
structure OpPrinterContext (OpCode : Type) [IsOpCode OpCode] where
  irContext : IRContext OpCode
  private printRegion : Region → Bool → StateT Nat IO Unit
deriving Inhabited

/-- Create a print context. -/
def OpPrinterContext.create (irContext : IRContext OpCode)
    (printRegion : Region → Bool → StateT Nat IO Unit) : OpPrinterContext OpCode :=
  { irContext, printRegion }

/--
Monadic printer. Threads the print context via `Reader` and the current
indentation level via `State`. Base monad is `IO` so that the printer can write
to the output stream. Recursive services are supplied by the main printer and
are not exposed directly to custom printer authors.
-/
abbrev OpPrinter (OpCode : Type) [IsOpCode OpCode] :=
  ReaderT (OpPrinterContext OpCode) (StateT Nat IO)

namespace OpPrinter

/-- Run an `OpPrinter` action. -/
def run {G : Type} [IsOpCode G]
    (context : OpPrinterContext G) (indent : Nat) (action : OpPrinter G α) : IO α :=
  StateT.run' (ReaderT.run action context) indent

/-- The `IRContext` for the current print. -/
def getContext : OpPrinter OpCode (IRContext OpCode) := do
  return (← read).irContext

/-- Current indentation level. -/
def getIndent : OpPrinter OpCode Nat :=
  get

/-- Print a raw string to the output stream. -/
def printString (s : String) : OpPrinter OpCode Unit := do
  (IO.print s : IO Unit)

/-- Print a newline. -/
def printNewline : OpPrinter OpCode Unit := do
  (IO.println "" : IO Unit)

/-- Print a symbol reference `@name`, escaping when it is not a bare identifier. -/
def printSymbolName (sym : ByteArray) : OpPrinter OpCode Unit := do
  let s := String.fromUTF8! sym
  let isAsciiAlpha (c : Char) : Bool :=
    ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
  let isBare : Bool :=
    !s.isEmpty &&
    (isAsciiAlpha s.front || s.front == '_') &&
    s.all (fun c => isAsciiAlpha c || ('0' ≤ c && c ≤ '9') || c == '_' || c == '.' || c == '$')
  if isBare then
    printString s!"@{s}"
  else
    printString s!"@\"{escapeStringLiteral sym}\""

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

/-- Print a type. -/
def printType (t : Attribute) : OpPrinter OpCode Unit :=
  printString s!"{t}"

/-- Print an attribute. -/
def printAttribute (a : Attribute) : OpPrinter OpCode Unit :=
  printString s!"{a}"

/-- Print an SSA value (`%x`, `%x#n`, or `%argN_M`). Uses the existing value name. -/
def printOperand (value : ValuePtr) : OpPrinter OpCode Unit := do
  let ctx ← getContext
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

/-- Print operation results `%x =` / `%x:n =`. -/
def printOpResults (op : OperationPtr) : OpPrinter OpCode Unit := do
  let ctx ← getContext
  if op.getNumResults! ctx != 0 then
    printString s!"%{op.id}"
    if op.getNumResults! ctx > 1 then
      printString s!":{op.getNumResults! ctx}"
    printString " = "

/-- Print operands `( %a, %b )`. -/
def printOpOperands (op : OperationPtr) : OpPrinter OpCode Unit := do
  let ctx ← getContext
  printString "("
  if op.getNumOperands! ctx != 0 then
    printOperand (op.getOperand! ctx 0)
    for index in List.range (op.getNumOperands! ctx - 1) do
      printString ", "
      printOperand (op.getOperand! ctx (index + 1))
  printString ")"

/-- Print successors ` [^bb0, ^bb1]`. -/
def printBlockOperands (op : OperationPtr) : OpPrinter OpCode Unit := do
  let ctx ← getContext
  if op.getNumSuccessors! ctx == 0 then return
  printString " ["
  printSuccessor (op.getSuccessor! ctx 0)
  for index in List.range (op.getNumSuccessors! ctx - 1) do
    printString ", "
    printSuccessor (op.getSuccessor! ctx (index + 1))
  printString "]"

/-- Print operation type ` : (i32) -> i32`. -/
def printOperationType (op : OperationPtr) : OpPrinter OpCode Unit := do
  let ctx ← getContext
  printString " : ("
  if op.getNumOperands! ctx != 0 then
    let firstOpType := (op.getOperand! ctx 0).getType! ctx
    printString s!"{firstOpType}"
    for index in List.range (op.getNumOperands! ctx - 1) do
      let opType := (op.getOperand! ctx (index + 1)).getType! ctx
      printString s!", {opType}"
  printString ") -> "
  if op.getNumResults! ctx == 0 then
    printString "()"
    return
  if op.getNumResults! ctx == 1 then
    let resType := ((op.getResult 0).get! ctx).type
    match resType.val with
    | .functionType _ => printString s!"({resType})"
    | _ => printString s!"{resType}"
    return
  printString "("
  let firstResType := ((op.getResult 0).get! ctx).type
  printString s!"{firstResType}"
  for index in List.range (op.getNumResults! ctx - 1) do
    let resType := ((op.getResult (index + 1)).get! ctx).type
    printString s!", {resType}"
  printString ")"

/-- Print an attribute dictionary ` { "k" = v }` if non-empty after eliding. -/
def printOptionalAttrDict (attrs : DictionaryAttr) (elided : Array String := #[]) : OpPrinter OpCode Unit := do
  let elidedBytes := elided.map (·.toUTF8)
  let filtered := attrs.entries.filter fun (k, _) => !elidedBytes.contains k
  if filtered.isEmpty then return
  printString " "
  printString s!"{{ attrs with entries := filtered }}"

/-- Print ` attributes { ... }` if non-empty after eliding, like MLIR's `printOptionalAttrDictWithKeyword`. -/
def printOptionalAttrDictWithKeyword (attrs : DictionaryAttr) (elided : Array String := #[]) : OpPrinter OpCode Unit := do
  let elidedBytes := elided.map (·.toUTF8)
  let filtered := attrs.entries.filter fun (k, _) => !elidedBytes.contains k
  if filtered.isEmpty then return
  printString " attributes "
  printString s!"{{ attrs with entries := filtered }}"

/-- Recursively print a region with the main printer's options and dispatch. -/
def printRegion (region : Region) (printEntryBlockArgs : Bool := false) : OpPrinter OpCode Unit := do
  let context ← read
  monadLift (context.printRegion region printEntryBlockArgs)

end OpPrinter

/--
A custom (non-generic) printer for one operation. The dispatcher prints the
indentation, the `%x = ` prefix and the operation name; the registered printer
handles everything after the name.

Runs in `OpPrinter`; custom printers use its operations for output, values,
attributes, and recursive regions.
-/
abbrev CustomPrinter (OpCode : Type) [IsOpCode OpCode] :=
  OperationPtr → OpPrinter OpCode Unit

end Printer

/-- Interface that stores each operation's custom printer.

The printer target may be a larger opcode aggregate containing this dialect. This
keeps dialect registration polymorphic, like context-sensitive `HasOpInfo`
helpers such as `Func.verifyLocalInvariants`.
-/
class HasCustomPrinting (Dialect : Type) [IsOpCode Dialect] where
  /-- The custom printer for an operation of this type, if it has one. -/
  customPrinter? :
    {GlobalOpCode : Type} →
    [IsOpCode GlobalOpCode] →
    [HasDialect GlobalOpCode Dialect] →
    Dialect → Option (Printer.CustomPrinter GlobalOpCode) :=
      fun {_} _ _ _ => none

end -- public section

end Veir
