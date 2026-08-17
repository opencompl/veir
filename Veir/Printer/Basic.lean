module

/-
# Custom printing interface

Types for non-generic (custom, i.e. not the generic MLIR syntax) operation
printing, plus the `HasCustomPrinting` interface through which dialects expose
their operations' custom printers.

This module sits below the printer machinery (`Veir/Printer.lean`): it only
contains the types, so that dialect printing modules (e.g.
`Veir/Dialects/Func/Printing.lean`) can define custom printers without
depending on the printer itself, and so that the printer can depend on the
dialect modules without an import cycle.
-/

public import Veir.IR.OpCode
public import Veir.IR.Basic

namespace Veir

public section

namespace Printer

/--
Recursive printing capabilities available to a custom (non-generic) printer.

A custom printer is defined outside of the recursive printer family (e.g. in a
dialect's `Printing.lean`), so it cannot call `printRegion`/`printOpList`/...
directly; instead it receives an `env` record with those entry points, mirroring
MLIR's `Printer` methods.
-/
structure PrintEnv (OpCode : Type) [IsOpCode OpCode] where
  /-- Print an SSA value (`%x` / `%argN_M`). -/
  printValue     : IRContext OpCode → ValuePtr → IO Unit
  /-- Print an operation followed by its siblings. -/
  printOpList    : IRContext OpCode → OperationPtr → Nat → IO Unit
  /-- Print a block followed by its siblings. -/
  printBlockList : IRContext OpCode → BlockPtr → Nat → IO Unit
  /-- Print a region `{ ... }`. -/
  printRegion    : IRContext OpCode → Region → Nat → IO Unit
  /-- Print `indent` levels of indentation. -/
  printIndent    : Nat → IO Unit

/--
A custom (non-generic) printer for one operation. The dispatcher prints the
indentation, the `%x = ` prefix and the operation name; the registered printer
handles everything after the name, recursing only through `env`.
-/
abbrev CustomPrinter (OpCode : Type) [IsOpCode OpCode] :=
  PrintEnv OpCode → IRContext OpCode → OperationPtr → Nat → IO Unit

end Printer

/--
Interface that stores each operation's custom printer.
-/
class HasCustomPrinting (OpCode : Type) [IsOpCode OpCode] where
  /-- The custom printer for an operation of this operation type, if it has one. -/
  customPrinter? : OpCode → Option (Printer.CustomPrinter OpCode) := fun _ => none

end

end Veir
