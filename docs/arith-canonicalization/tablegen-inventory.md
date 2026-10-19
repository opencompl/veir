# TableGen canonicalization inventory

Pinned source: LLVM `32ec2901f308caee5c76dbdc8d21a12a08d5457a`. The inventory contains **67 concrete TableGen rewrite variants** registered by Arith operation canonicalization hooks: 51 direct `Pat`/`Pattern` definitions plus 16 concrete instantiations of the two parameterized select bases. It excludes helper constraints/native calls and the base classes themselves. See [machine-readable inventory](tablegen-inventory.json).

The `getCanonicalizationPatterns` hooks in `ArithOps.cpp` register these definitions with `patterns.add`/`patterns.insert`; `CmpIOp` uses `insert`, and `SelectOp` explicitly registers the 20 simple/select-minmax definitions. `TruncIOp` and `TruncFOp` register both TableGen definitions and C++ `NarrowExtremum` patterns; those C++ templates are outside this TableGen inventory. Other handwritten C++ canonicalization patterns are also outside this file.

## Pattern families

| Family | Count | Representative rewrites |
|---|---:|---|
| Integer arithmetic / extended integer ops | 18 | TD001–TD018 |
| Bitwise integer ops | 10 | TD019–TD022, TD049–TD054 |
| Integer comparisons | 2 | TD023–TD024 |
| Select and min/max | 20 | TD025–TD044 |
| Integer casts, bitcasts, and truncations | 7 | TD045–TD048, TD055–TD057 |
| Floating-point arithmetic and conversions | 10 | TD058–TD067 |

## Conditions and semantic cautions

- Constant-combining patterns evaluate fixed-width APInt attributes at the result type. Integer overflow flags are merged by bitwise intersection where explicitly stated; this is the exact source behavior, but reassociation can change which intermediate operation overflows and therefore where `nsw`/`nuw` poison occurs. Three source rewrites intentionally use default/no-overflow flags, and `AddIMulNegativeOne*` has a source TODO about overflow flags.
- Constant materialization guards cover dynamic shaped zeros (`SubISubILHSRHSLHS`) and scalar/splat constants (`-1`, `1`, shift amounts). TableGen zero materialization assumes scalar or static shape; poison values do not match ordinary integer constants unless they satisfy the specific matcher.
- Extended integer operation patterns that discard an overflow/borrow/high result require that result to have no uses. In that situation, replacing the dead result with `x` is explicitly allowed by the source comment.
- `nneg` is preserved or recomputed for extension-pushing patterns: XOR/OR require both extui operands nneg; AND requires either; comparisons drop nneg because only eq/ne are allowed.
- Float truncation cancellation requires absent rounding mode. `subf(-0,x)` also requires default rounding mode; the source marks custom-rounding safety as TODO for this and the paired-negation mul/div rewrites. The addf/negf rewrites propagate rounding mode and fast-math flags and are documented in source as bit-identical for any rounding mode.
- The peephole list here is TableGen-only. The operation hooks also include handwritten C++ patterns, and fold methods run separately under `--canonicalize`; they must be inventoried separately for a complete whole-pass catalogue.
