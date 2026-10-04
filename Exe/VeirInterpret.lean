import Veir.Parser.MlirParser
import Veir.Verifier
import Veir.Interpreter.Basic
import Veir.Input
import Veir.Panic

/-!
  # Veir Interpreter CLI Tool

  This file implements a simple command-line tool that reads an MLIR
  program from a file or from standard input, finds a zero-argument
  function-like operation named `main`, and then executes that function
  using the interpreter defined in `Veir.Interpreter`.
 -/

open Veir.Parser
open Veir.Input
open Veir

/-- Returns true if `op` is a viable zero-argument `@main` function. -/
private def isZeroArgMainFunc (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  match FunctionOp.cast? op ctx with
  | some funcOp =>
    String.fromUTF8! funcOp.getSymName.value == "main" && funcOp.getNumArguments == 0
  | none => false

/-- Scan the module's top-level ops for entry points. -/
partial def scanEntryPoints (ctx : IRContext OpCode) (op : Option OperationPtr)
    (entryPoints : List {op : OperationPtr // op.isFunctionLike ctx} := []) :
    IO (List {op : OperationPtr // op.isFunctionLike ctx}) := do
  match op with
  | none => return entryPoints
  | some op =>
    if hIsFunc : op.isFunctionLike ctx then
      let entryPoints := if isZeroArgMainFunc ctx op then ⟨op, hIsFunc⟩ :: entryPoints else entryPoints
      scanEntryPoints ctx (op.get! ctx).next entryPoints
    else
      match op.getOpType! ctx with
      | .llvm .module_flags | .llvm .mlir__global =>
        scanEntryPoints ctx (op.get! ctx).next entryPoints
      | _ =>
        IO.eprintln "Error: unsupported top-level operation; expected a function, llvm.mlir.global, or llvm.module_flags"
        IO.Process.exit 1

/-- Resolve the unique entry point of the module, if one exists. -/
def resolveEntryPoint (ctx : IRContext OpCode) (moduleOp : OperationPtr) :
    IO {op : OperationPtr // op.isFunctionLike ctx} := do
  let region := moduleOp.getRegion! ctx 0
  let entryPoints ←
    match (region.get! ctx).firstBlock with
    | none => pure []
    | some blockPtr => scanEntryPoints ctx (blockPtr.get! ctx).firstOp
  match entryPoints with
  | [] =>
    IO.eprintln "Error: No entry point: define a zero-argument function named 'main'"
    IO.Process.exit 1
  | [mainOp] => return mainOp
  | _ =>
    IO.eprintln "Error: Multiple entry points: define exactly one zero-argument function named 'main'"
    IO.Process.exit 1

/-- The value of an interpretation that must succeed before `main` can run. -/
private def expectOk (what : String) : Interp α → IO α
  | .ok a => pure a
  | .ub _ => do
    IO.println "Undefined behavior"
    IO.Process.exit 0
  | .fail _ => do
    IO.eprintln s!"error: failed to initialize {what}"
    IO.Process.exit 1

/--
  Give each global and function of the module an object, before any of them
  is initialized, so that an initializer can take the address of any symbol.
  A function gets an object of no bytes. Returns the globals still to be
  initialized, with their objects.
-/
partial def allocateGlobals (ctx : WfIRContext OpCode) (op : Option OperationPtr)
    (mem : MemoryState) (pending : Array (OperationPtr × Data.Pointer) := #[]) :
    IO (MemoryState × Array (OperationPtr × Data.Pointer)) := do
  let some op := op | return (mem, pending)
  let raw : IRContext OpCode := ctx
  let (mem, pending) ← match op.getOpType! raw with
    | .llvm .mlir__global => do
      let props : LLVMGlobalProperties := op.getProperties! raw (OpCode.llvm .mlir__global)
      let name := "@" ++ String.fromUTF8! props.sym_name.value
      let some size := DataLayout.riscv64.getTypeAllocSize props.global_type.val
        | IO.eprintln s!"error: cannot size global {name}"; IO.Process.exit 1
      let (mem, ptr) ← expectOk name (mem.alloc size.toUInt64)
      pure ({ mem with globals := mem.globals.insert name ptr.object }, pending.push (op, ptr))
    | _ =>
      match FunctionOp.cast? op raw with
      | some funcOp =>
        let name := "@" ++ String.fromUTF8! funcOp.getSymName.value
        let (mem, ptr) ← expectOk name (mem.alloc 0)
        pure ({ mem with globals := mem.globals.insert name ptr.object }, pending)
      | none => pure (mem, pending)
  allocateGlobals ctx (op.get! raw).next mem pending

/--
  Fill the object of a global with its `value`, or with what its initializer
  region returns. A global with neither stays poison.
-/
def initializeGlobal (ctx : WfIRContext OpCode) (op : OperationPtr) (ptr : Data.Pointer)
    (mem : MemoryState) : IO MemoryState := do
  let raw : IRContext OpCode := ctx
  let props : LLVMGlobalProperties := op.getProperties! raw (OpCode.llvm .mlir__global)
  let name := "@" ++ String.fromUTF8! props.sym_name.value
  match props.value with
  | some (.integerAttr a) =>
    let bw := a.type.bitwidth
    expectOk name (mem.llvmStore ptr (.int bw (.val (BitVec.ofInt bw a.value))))
  | some (.stringAttr str) => expectOk name (mem.store ptr str.value)
  | some _ => IO.eprintln s!"error: unsupported value of global {name}"; IO.Process.exit 1
  | none =>
    if hop : ¬op.InBounds ctx.raw then pure mem
    else if h : op.getNumRegions ctx.raw ≠ 1 then pure mem
    else
      let region := op.getRegion ctx.raw 0
      match (region.get ctx.raw).firstBlock with
      | none => pure mem
      | some _ => do
        let (state, results) ← expectOk name
          (interpretRegion region #[] (ctx := ctx) ⟨.empty ctx, mem⟩)
        let some value := results[0]? | pure state.memory
        expectOk name (state.memory.llvmStore ptr value)

/--
  Give each global and function of the module an object before `main` runs,
  in two passes: first every object, then every initial value.
-/
def materializeGlobals (ctx : WfIRContext OpCode) (op : Option OperationPtr)
    (mem : MemoryState) : IO MemoryState := do
  let (mem, pending) ← allocateGlobals ctx op mem
  pending.foldlM (fun mem (op, ptr) => initializeGlobal ctx op ptr mem) mem

set_option warn.sorry false in
def main (args : List String) : IO Unit := do
  enableExitOnPanic
  let filename ←
    match inputSourceOfArgs args with
    | .ok filename => pure filename
    | .error errMsg =>
      IO.eprintln errMsg
      IO.eprintln "Usage: veir-interpret [filename]"
      IO.eprintln "  Reads the program from standard input if no filename is given."
      IO.Process.exit 2
  match ← parseSourceFile filename (allowUnregisteredDialect := true) with
  | .ok (ctx, op, source) =>
    let rawCtx : IRContext OpCode := ctx
    let mainOp ← resolveEntryPoint rawCtx op
    let mainFunc := FunctionOp.cast mainOp.val rawCtx mainOp.property
    let firstOp := ((op.getRegion! rawCtx 0).get! rawCtx).firstBlock.bind
      fun b => (b.get! rawCtx).firstOp
    let mem ← materializeGlobals ctx firstOp MemoryState.empty
    let result := bind (interpretFunction (ctx := ctx) mainFunc #[] mem (by sorry))
                       (fun (_, r) => pure r)
    match result with
    | .ok results => IO.println s!"Program output: {results}"
    | .ub op? =>
      IO.println "Undefined behavior"
      if let some op := op? then
        IO.println (source.formatAt op "note" "triggered here")
    | .fail op? =>
      match op? with
      | some op => IO.eprintln (source.formatAt op "error" "failed to interpret operation")
      | none => IO.eprintln "error: failed to interpret module"
      IO.Process.exit 1
  | .error errMsg =>
    IO.eprintln errMsg
    IO.Process.exit 1
