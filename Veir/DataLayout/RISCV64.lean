module

public import Veir.Interfaces.DataLayoutInterfaces

/-!
# RV64 Data Layout

The fixed data layout used by the RV64 backend.
-/

namespace Veir.DataLayout

/--
  The standard RV64 datalayout string, `e-m:e-p:64:64-i64:64-i128:128-n32:64-S128`,
  combined with LLVM's default integer entries: an unlisted width takes the next
  larger entry, so this table is `i1:8-i8:8-i16:16-i32:32-i64:64-i128:128`.

  The endianness, mangling, native-width and stack-alignment parts of the string
  are not modelled, since nothing queries them yet.
-/
public def riscv64Spec : DataLayoutSpec :=
  { integerAlignments := #[(1, 1), (8, 1), (16, 2), (32, 4), (64, 8), (128, 16)]
    pointerSize := 8
    pointerAlignment := 8 }

/-- The data layout of the RV64 target. -/
public def riscv64 : DataLayout := .ofSpec riscv64Spec

end Veir.DataLayout
