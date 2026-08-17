module

/-
# Custom printing for the `func` dialect

Hand-written custom printers for `func` operations whose syntax cannot be
expressed declaratively (mirroring MLIR's `hasCustomAssemblyFormat`), plus the
`HasCustomPrinting` instance registering them. Operations with a declarative
`assemblyFormat` (e.g. `func.return`, `func.call`) are registered here too,
in the `assemblyFormat` follow-up.
-/

public import Veir.Printer.Basic
public import Veir.Dialects.Func.OpInfo

namespace Veir

variable {GlobalOpCode : Type} [IsOpCode GlobalOpCode] [HasDialect GlobalOpCode Func] 

public section

/--
  Print a function body region, eliding the entry block's label and arguments
  (they appear in the function signature). Prints `{ ... }` with the entry
  block's operation list and any trailing blocks.
-/
def Func.printFuncBodyRegion
    (env : Printer.PrintEnv GlobalOpCode) (ctx : IRContext GlobalOpCode)
    (entryPtr : BlockPtr) (indent : Nat) : IO Unit := do
  IO.println "{"
  match (entryPtr.get! ctx).firstOp with
  | some firstOp => env.printOpList ctx firstOp (indent + 1)
  | none => pure ()
  match (entryPtr.get! ctx).next with
  | some nextBlock => env.printBlockList ctx nextBlock (indent + 1)
  | none => pure ()
  env.printIndent indent
  IO.print "}"

/--
  Custom (pretty) printer for `func.func`, mirroring MLIR's
  `hasCustomAssemblyFormat`. The dispatcher prints the `func.func` op name; this
  printer handles everything after it: ` @name(%args) -> results { body }`.
-/
def Func.printFuncFunc : Printer.CustomPrinter GlobalOpCode := fun env ctx op indent => do
  let props : FuncFuncProperties := op.getProperties! ctx Func.func
  let symName := String.fromUTF8! props.sym_name.value
  let funcType : FunctionType := props.function_type
  IO.print s!" @{symName}("
  match (op.getRegion! ctx 0).get! ctx |>.firstBlock with
  | some entryPtr =>
    let nargs := entryPtr.getNumArguments! ctx
    for i in 0...nargs do
      if i > 0 then IO.print ", "
      let arg := entryPtr.getArgument i
      IO.print s!"%arg{entryPtr.id}_{i}: {(arg.get! ctx).type}"
    IO.print ")"
    let outs := funcType.outputs
    if outs.size = 1 then
      IO.print s!" -> {outs[0]!}"
    else if outs.size > 1 then
      IO.print " -> ("
      IO.print s!"{outs[0]!}"
      for i in 1...outs.size do
        IO.print s!", {outs[i]!}"
      IO.print ")"
    let extraEntries := props.extra.entries
    if extraEntries.size > 0 then
      IO.print " attributes "
      IO.print (DictionaryAttr.fromArray extraEntries)
    IO.print " "
    Func.printFuncBodyRegion env ctx entryPtr indent
  | none =>
    IO.print ") {}"

/--
  The custom printer for a `func` operation, if it has one, in any global
  operation type that contains `func` operations.
-/
def Func.customPrinter? :
    Func → Option (Printer.CustomPrinter GlobalOpCode)
  | .func => some (Func.printFuncFunc (GlobalOpCode := GlobalOpCode))
  | _ => none

end -- public section

end Veir
