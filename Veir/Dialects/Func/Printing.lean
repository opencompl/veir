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

open Printer.OpPrinter

public section

variable {GlobalOpCode : Type} [IsOpCode GlobalOpCode] [HasDialect GlobalOpCode Func]

/--
Custom printer for `func.func`, mirroring MLIR's `hasCustomAssemblyFormat`.
The dispatcher prints the `func.func` op name; this printer handles everything
after it: ` @name(%args) -> results attributes { body }`.
-/
def Func.printFuncFunc : Printer.CustomPrinter GlobalOpCode := fun op => do
  let ctx ← getContext
  let props : FuncFuncProperties := op.getProperties! ctx Func.func
  let funcType : FunctionType := props.function_type
  -- ` @name` with optional visibility, like MLIR's `printFunctionOp` does
  -- `visibility` is stored in `extra` if present (e.g. `"private"`).
  let visibility? := props.extra.entries.find? fun (k, _) => k == "sym_visibility".toUTF8
  let extraWithoutVisibility := DictionaryAttr.fromArray (props.extra.entries.filter fun (k, value) =>
    k != "sym_visibility".toUTF8 || match value with
      | .stringAttr _ => false
      | _ => true)
  printString " "
  if let some (_, .stringAttr vis) := visibility? then
    unless vis.value == "public".toUTF8 do
      printString s!"{String.fromUTF8! vis.value} "
  printSymbolName props.sym_name.value
  printString "("
  let region := (op.getRegion! ctx 0).get! ctx
  let isExternal := region.firstBlock.isNone
  -- Print argument list: for defined functions use entry block args (SSA names),
  -- for external use types only, like MLIR's `printFunctionSignature`.
  if !isExternal then
    let entryPtr := region.firstBlock.get!
    let nargs := entryPtr.getNumArguments! ctx
    for i in List.range nargs do
      if i != 0 then printString ", "
      let argPtr := entryPtr.getArgument i
      printRegionArgument argPtr
      printString s!": {(argPtr.get! ctx).type}"
    if funcType.isVarArg then
      if nargs > 0 then printString ", "
      printString "..."
  else
    let inputs := funcType.inputs
    for i in List.range inputs.size do
      if i != 0 then printString ", "
      printType inputs[i]!
    if funcType.isVarArg then
      if !inputs.isEmpty then printString ", "
      printString "..."
  printString ")"
  -- Results
  let outs := funcType.outputs
  if outs.size == 1 then
    match outs[0]! with
    | .functionType _ => printString s!" -> ({outs[0]!})"
    | _ => printString s!" -> {outs[0]!}"
  else if outs.size > 1 then
    printString " -> ("
    printString s!"{outs[0]!}"
    for i in List.range (outs.size - 1) do
      printString s!", {outs[i + 1]!}"
    printString ")"
  -- Function attributes via `printOptionalAttrDictWithKeyword`, like MLIR's `printFunctionAttributes`.
  -- `extraWithoutVisibility` already excludes `sym_visibility`, and `extra` excludes `sym_name`/`function_type`.
  printOptionalAttrDictWithKeyword extraWithoutVisibility
  -- Body if not external, like MLIR's `if (!body.empty()) p.printRegion(body, false)`
  if !isExternal then
    printString " "
    printRegion region

instance : HasCustomPrinting Func where
  customPrinter?
    | .func => some (Func.printFuncFunc (GlobalOpCode := Func))
    | _ => none

end

end Veir
