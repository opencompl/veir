module

/-
# Custom printing for the `func` dialect

Hand-written custom printers for `func` operations whose syntax cannot be
expressed declaratively (mirroring MLIR's `hasCustomAssemblyFormat`), plus the
`HasCustomPrinting` instance registering them.
-/

public import Veir.Printer.CustomPrinting
public import Veir.Dialects.Func.OpInfo

namespace Veir

public section

variable {GlobalOpCode : Type} [IsOpCode GlobalOpCode] [HasDialect GlobalOpCode Func]

/-- Helper: print a symbol reference `@name` with minimal escaping. -/
def printSymbolName (sym : ByteArray) : Printer.OpPrinter GlobalOpCode Unit := do
  let s := String.fromUTF8! sym
  -- MLIR bare identifiers: `[a-zA-Z_][a-zA-Z0-9_$.]*` and not starting with digit.
  -- If s matches, print `@s`, else print `@"escaped"` .
  let isBare : Bool :=
    !s.isEmpty &&
    (s.front.isAlpha || s.front == '_') &&
    s.all (fun c => c.isAlphanum || c == '_' || c == '.' || c == '$')
  if isBare then
    Printer.OpPrinter.printString s!"@{s}"
  else
    let escaped := s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"
    Printer.OpPrinter.printString s!"@\"{escaped}\""

/--
Custom printer for `func.func`, mirroring MLIR's `hasCustomAssemblyFormat`.
The dispatcher prints the `func.func` op name; this printer handles everything
after it: ` @name(%args) -> results attributes { body }`.
-/
def Func.printFuncFunc : Printer.CustomPrinter GlobalOpCode := fun env op => do
  let ctx ← Printer.OpPrinter.getContext
  let props : FuncFuncProperties := op.getProperties! ctx Func.func
  let funcType : FunctionType := props.function_type
  -- ` @name` with optional visibility, like MLIR's `printFunctionOp` does
  -- `visibility` is stored in `extra` if present (e.g. `"private"`).
  let visibility? := props.extra.entries.find? fun (k, _) => k == "sym_visibility".toUTF8
  let extraWithoutVisibility := DictionaryAttr.fromArray (props.extra.entries.filter fun (k, _) => k != "sym_visibility".toUTF8)
  Printer.OpPrinter.printString " "
  if let some (_, .stringAttr vis) := visibility? then
    Printer.OpPrinter.printString s!"{String.fromUTF8! vis.value} "
  printSymbolName (GlobalOpCode := GlobalOpCode) props.sym_name.value
  Printer.OpPrinter.printString "("
  let region := (op.getRegion! ctx 0).get! ctx
  let isExternal := region.firstBlock.isNone
  -- Print argument list: for defined functions use entry block args (SSA names),
  -- for external use types only, like MLIR's `printFunctionSignature`.
  if !isExternal then
    let entryPtr := region.firstBlock.get!
    let nargs := entryPtr.getNumArguments! ctx
    for i in List.range nargs do
      if i != 0 then Printer.OpPrinter.printString ", "
      let argPtr := entryPtr.getArgument i
      let value : ValuePtr := ValuePtr.blockArgument argPtr
      env.printRegionArgument value
      Printer.OpPrinter.printString s!": {(argPtr.get! ctx).type}"
  else
    let inputs := funcType.inputs
    for i in List.range inputs.size do
      if i != 0 then Printer.OpPrinter.printString ", "
      Printer.OpPrinter.printString s!"{inputs[i]!}"
  Printer.OpPrinter.printString ")"
  -- Results
  let outs := funcType.outputs
  if outs.size == 1 then
    Printer.OpPrinter.printString s!" -> {outs[0]!}"
  else if outs.size > 1 then
    Printer.OpPrinter.printString " -> ("
    Printer.OpPrinter.printString s!"{outs[0]!}"
    for i in List.range (outs.size - 1) do
      Printer.OpPrinter.printString s!", {outs[i + 1]!}"
    Printer.OpPrinter.printString ")"
  -- Function attributes via `printOptionalAttrDictWithKeyword`, like MLIR's `printFunctionAttributes`.
  -- `extraWithoutVisibility` already excludes `visibility`, and `extra` excludes `sym_name`/`function_type`.
  env.printOptionalAttrDictWithKeyword extraWithoutVisibility #[]
  -- Body if not external, like MLIR's `if (!body.empty()) p.printRegion(body, false)`
  if !isExternal then
    Printer.OpPrinter.printString " "
    env.printRegion region false

/-- Dialect-local `HasCustomPrinting` instance for `Func`. -/
instance : HasCustomPrinting Func where
  customPrinter?
    | .func => some (Func.printFuncFunc (GlobalOpCode := Func))
    | _ => none

/-- Polymorphic helper for the global `HasCustomPrinting OpCode` instance. -/
def Func.customPrinter? : Func → Option (Printer.CustomPrinter GlobalOpCode)
  | .func => some (Func.printFuncFunc (GlobalOpCode := GlobalOpCode))
  | _ => none

end -- public section

end Veir
