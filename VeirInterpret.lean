import Veir.Parser.MlirParser
import Veir.Verifier
import Veir.Interpreter.Basic
import Veir.Input
import Veir.Panic

/-!
  # Veir Interpreter CLI Tool

  This file implements a simple command-line tool that reads an MLIR
  program from a file or from standard input, finds a zero-argument
  func.func or llvm.func named `main`, and then executes that function
  using the interpreter defined in `Veir.Interpreter`.
 -/

open Veir.Parser
open Veir.Input
open Veir

/-- Returns true if `op` is a viable zero-argument `@main` function. -/
private def isZeroArgMainFunc (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  match FunctionOpInterface.getSymName? op ctx with
  | some symName =>
      String.fromUTF8! symName.value == "main" &&
        (FunctionOpInterface.getNumArguments? op ctx == some 0)
  | none =>
      false

/-- Scan the module's top-level ops for entry points. -/
partial def scanEntryPoints (ctx : IRContext OpCode) (op : Option OperationPtr)
    (entryPoints : List OperationPtr := []) : IO (List OperationPtr) := do
  match op with
  | none => return entryPoints
  | some op =>
    if op.isFunctionLike ctx then
      let entryPoints := if isZeroArgMainFunc ctx op then op :: entryPoints else entryPoints
      scanEntryPoints ctx (op.get! ctx).next entryPoints
    else
      match op.getOpType! ctx with
      | .llvm .module_flags | .llvm .mlir__global =>
        scanEntryPoints ctx (op.get! ctx).next entryPoints
      | _ =>
        IO.eprintln "Error: unsupported top-level operation; expected a function, llvm.mlir.global, or llvm.module_flags"
        IO.Process.exit 1

/-- Resolve the unique entry point of the module, if one exists. -/
def resolveEntryPoint (ctx : IRContext OpCode) (moduleOp : OperationPtr) : IO OperationPtr := do
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

/--
  The initial bytes of a global of `size` bytes with the attribute `value`:
  integers little-endian, strings verbatim, anything else poison.
-/
private def globalInitBytes (value : Attribute) (size : Nat) : Array MemoryByte :=
  let bytes : Array MemoryByte := match value with
    | .integerAttr a => MemoryByte.ofByteArray (UInt64.ofBitVec (BitVec.ofInt 64 a.value)).toByteArrayLE
    | .stringAttr str => MemoryByte.ofByteArray str.value
    | _ => #[]
  (bytes ++ Array.replicate size MemoryByte.poison).extract 0 size

private def exitOnInterp (what : String) : Interp α → IO α
  | .ok a => pure a
  | .ub => do
    IO.println "Undefined behavior"
    IO.Process.exit 0
  | .fail => do
    IO.eprintln s!"Error while interpreting {what}"
    IO.Process.exit 1

set_option warn.sorry false in
/--
  Materialize the module's globals and functions as objects that live for
  the whole run, before `main` executes. A global with a `value` attribute
  starts with its bytes; one with an initializer region starts with the
  value that region returns; any other global starts as poison. Functions
  get empty objects so that their addresses are distinct.
-/
partial def materializeGlobals (ctx : WfIRContext OpCode) (op : Option OperationPtr)
    (mem : MemoryState) : IO MemoryState := do
  let some op := op | return mem
  let raw : IRContext OpCode := ctx
  let mem ← match op.getOpType! raw with
    | .llvm .mlir__global => do
      let props : LLVMGlobalProperties := op.getProperties! raw (OpCode.llvm .mlir__global)
      let name := "@" ++ String.fromUTF8! props.sym_name.value
      let some size := DataLayout.riscv64.getTypeAllocSize props.global_type.val
        | IO.eprintln s!"Error: cannot size global {name}"; IO.Process.exit 1
      let align := (props.alignment.map (·.value.toNat.toUInt64)).getD MemoryState.objectAlignment
      /- The object becomes constant only after its initializer is stored. -/
      let (mem, ptr) := mem.alloc size .global align
      let mem ← match props.value with
        | some value => exitOnInterp name (mem.storeBytes ptr (globalInitBytes value size))
        | none =>
          let region := op.getRegion! raw 0
          match (region.get! raw).firstBlock with
          | none => pure mem
          | some _ => do
            let (state, results) ← exitOnInterp name
              (interpretRegion region #[] (ctx := ctx) ⟨.empty ctx, mem⟩ (by sorry))
            let some value := results[0]? | pure state.memory
            exitOnInterp name (state.memory.llvmStore ptr value)
      let mem := match mem.getObject? ptr with
        | some obj => mem.setObject ptr { obj with isConst := props.constant }
        | none => mem
      pure { mem with globals := mem.globals.insert name ptr.object }
    | _ =>
      if op.isFunctionLike raw then
        match FunctionOpInterface.getSymName? op raw with
        | some sym =>
          let name := "@" ++ String.fromUTF8! sym.value
          let (mem, ptr) := mem.alloc 0 .global MemoryState.objectAlignment true
          pure { mem with globals := mem.globals.insert name ptr.object }
        | none => pure mem
      else pure mem
  materializeGlobals ctx (op.get! raw).next mem

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
  match ← parseOperation filename (allowUnregisteredDialect := true) with
  | .ok (ctx, op) =>
    match ctx.verify op with
    | .ok _ =>
      let rawCtx : IRContext OpCode := ctx
      let mainOp ← resolveEntryPoint rawCtx op
      let firstOp := ((op.getRegion! rawCtx 0).get! rawCtx).firstBlock.bind fun b => (b.get! rawCtx).firstOp
      let mem ← materializeGlobals ctx firstOp MemoryState.empty
      let result := bind (interpretFunction (ctx := ctx) mainOp #[] mem (by sorry))
                         (fun (_, r) => pure r)
      match result with
      | .ok results => IO.println s!"Program output: {results}"
      | .ub => IO.println "Undefined behavior"
      | .fail =>
        IO.eprintln "Error while interpreting module"
        IO.Process.exit 1
    | .error errMsg =>
      IO.eprintln s!"Error verifying input program: {errMsg}"
      IO.Process.exit 1
  | .error errMsg =>
    IO.eprintln s!"Error: {errMsg}"
    IO.Process.exit 1
