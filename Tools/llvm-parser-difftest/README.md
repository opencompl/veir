# Differential testing: `mlir-translate` vs. the verified LLVM IR parser

| Mismatch | Examples | Fix belongs in | Why |
| --- | --- | --- | --- |
| Constant hoisting and sharing | 06, 08, 12, 23, 24 | (2) Comparison | Where mlir-translate puts constants is a detail of its C++ importer, not part of LLVM's meaning. Constants have no side effects, so one shared constant at the top means the same as one per use. The tile spec (constants immediately before their user) is a sound design choice and needn't copy LLVM's importer. A plain renaming check won't catch this, because the number of operations differs. The comparison has to treat programs as equal up to where constants are placed and shared, for example by first merging and hoisting constants on both sides, or by comparing after reverseModule. |
| Forward reference accepted | 21 | (1) Spec | The spec accepts input that LLVM rejects ("Instruction does not dominate a, the check is that each value is defined before it is used. It should go in ValidResolvedFunction or the resolver. Ignoring it in the comparison would hide a real soundness gap. |
| Unreachable second block rejected | 22 | (1) Spec | This is valid LLVM, and resolveFunction only handles single-block functionhe planned branch and phi support will close anyway. |

```sh
lake build Veir.Parser.LLVMLowering Veir.Input Veir.Printer
lake env lean --run Tools/llvm-parser-difftest/DiffTest.lean Tools/llvm-parser-difftest/examples Tools/llvm-parser-difftest/out
```
