module

public import Veir.Dialects.Arith.FoldCorrectness
public import Veir.Dialects.LLVM.FoldCorrectness
public import Veir.Dialects.RISCV.FoldCorrectness

/-!
# Correctness of the dialect fold tables

Each dialect proves its own `tryFold` entries against `FoldTable.CorrectAt`.
Importing this module brings in every such proof.
-/
