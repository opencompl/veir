| Mismatch | Examples | Fix belongs in | Why |
| --- | --- | --- | --- |
| Constant hoisting and sharing | 06, 08, 12, 23, 24, 28, 30, 31 | (2) Comparison | `mlir-translate` hoists or shares constants. VeIR materializes them at each use. The comparison should account for constant placement and sharing across blocks. |
| Non-dominating reference accepted | 21 | (1) Spec | `mlir-translate` rejects a use that the value's definition does not dominate. VeIR resolves the name and accepts the use. |
| Unreachable block preserved | 22 | (2) Comparison | VeIR lowers the unreachable block. `mlir-translate` drops it. The comparison should account for unreachable blocks. |
