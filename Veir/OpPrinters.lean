module

/-
# Global custom-printer registry

The `HasCustomPrinting` instance for the global `OpCode`, aggregating each
dialect's custom printers.

This module imports every dialect's printing module (e.g.
`Veir.Dialects.Func.Printing`), so that a new dialect's custom printers are
picked up by adding one import and one extra match arm in the instance. The
printer machinery (`Veir/Printer.lean`) then uses the `HasCustomPrinting` lookup
for custom syntax printing.
-/

public import Veir.GlobalOpInfo
public import Veir.Dialects.Func.Printing

namespace Veir

public section

instance : HasCustomPrinting OpCode where
  customPrinter? := fun
    | .func op => Func.customPrinter? op
    | _ => none

end -- public section

end Veir
