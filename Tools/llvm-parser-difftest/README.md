# Differential testing: `mlir-translate` vs. the verified LLVM IR parser

Mismatch: Renaming (SSA and block numbers)
Examples: all 24
Fix belongs in: (2) Comparison
Why: The numbers are allocation IDs, and neither side has to match them. The RootedIso relation in LLVMLowering.lean already ignores them, so the comparison just needs a decidable version
of it.
────────────────────────────────────────
Mismatch: Constant hoisting and sharing
Examples: 06, 08, 12, 23, 24
Fix belongs in: (2) Comparison
Why: Where mlir-translate puts constants is a detail of its C++ importer, not part of LLVM's meaning. Constants have no side effects, so one shared constant at the top means the same as one
per use. Your tile spec (constants immediately before their user) is a sound design choice and needn't copy LLVM's importer. A plain renaming check won't catch this, because the number of
 operations differs. The comparison has to treat programs as equal up to where constants are placed and shared, for example by first merging and hoisting constants on both sides, or by
comparing after reverseModule.
────────────────────────────────────────
Mismatch: Default function attributes (calling convention, linkage, unnamed_addr, visibility)
Examples: none 
Fix belongs in: (1) Spec, done
Why: The lowering spec now requires every llvm.func to carry `defaultFuncExtra`, which holds exactly the values mlir-translate writes when the source names none of them.
────────────────────────────────────────
Mismatch: Module attributes (data-layout spec, module_asm, target_triple)
Examples: none
Fix belongs in: (1) Spec, done
Why: The lowering spec now requires the module to carry `defaultModuleAttrs`. When the grammar gains `target datalayout` and `target triple`, these attributes must come from the parsed lines instead, with today's values used only when the lines are absent.
────────────────────────────────────────
Mismatch: Forward reference accepted
Examples: 21
Fix belongs in: (1) Spec
Why: The spec accepts input that LLVM rejects ("Instruction does not dominate a, the check is that each value is defined before it is used. It should go in
ValidResolvedFunction or the resolver. Ignoring it in the comparison would hide a real soundness gap.
────────────────────────────────────────
Mismatch: Unreachable second block rejected
Examples: 22
Fix belongs in: (1) Spec
Why: This is valid LLVM, and resolveFunction only handles single-block functionhe planned branch and phi support will close anyway.

```sh
lake build Veir.Parser.LLVMLowering Veir.Input Veir.Printer
lake env lean --run Tools/llvm-parser-difftest/DiffTest.lean Tools/llvm-parser-difftest/examples Tools/llvm-parser-difftest/out
```

| Example | Outcome | Classification |
| --- | --- | --- |
| 01-ret-param | mismatch | renaming |
| 02-ret-const | mismatch | renaming |
| 03-single-xor | mismatch | renaming |
| 04-single-and | mismatch | renaming |
| 05-single-or | mismatch | renaming |
| 06-demorgan | mismatch | reordering: one shared `-1` per function at the top (21 vs. 25 ops) |
| 07-const-lhs | mismatch | renaming |
| 08-two-distinct-consts | mismatch | reordering: both constants hoisted to the block entry |
| 09-both-const | mismatch | renaming |
| 10-self-xor | mismatch | renaming |
| 11-i1 | mismatch | renaming |
| 12-odd-width | mismatch | reordering: constant hoisted above the `and` |
| 13-i128-large-const | mismatch | renaming |
| 14-i64-min | mismatch | renaming |
| 15-dead-code | mismatch | renaming |
| 16-chain | mismatch | renaming |
| 17-label-name | mismatch | renaming |
| 18-dotted-names | mismatch | renaming |
| 19-multi-func | mismatch | renaming |
| 20-comments | mismatch | renaming |
| 21-forward-ref | reference rejects | semantic mismatch: the new path accepts a use that its definition does not dominate |
| 22-unreachable-block | new path rejects | semantic mismatch: `resolveFunction` handles only single-block functions, although the input is valid LLVM |
| 23-repeated-const-many | mismatch | reordering: one shared `5` instead of four copies (12 vs. 15 ops) |
| 24-ret-const-after-insts | mismatch | reordering: the `ret` reuses the `and`'s constant (9 vs. 10 ops) |
| 25-i8-out-of-range | mismatch | renaming (both truncate `300` to `44 : i8`) |
| 26-unused-param | mismatch | renaming |
