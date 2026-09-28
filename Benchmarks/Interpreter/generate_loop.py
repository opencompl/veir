#!/usr/bin/env python3
"""Generate a small three-block LLVM loop with exactly N positive iterations."""
import argparse
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("output", type=Path)
parser.add_argument("--iterations", type=int, default=1000)
args = parser.parse_args()
if not 1 <= args.iterations < 2**32:
    parser.error("iterations must be between 1 and 2**32 - 1")
args.output.write_text(f'''// Three basic blocks, eight static operations, {args.iterations} loop iterations.
// Expected result: {args.iterations} : i32. Dynamic operations: {3 * args.iterations + 5}.
"builtin.module"() ({{
  "llvm.func"() <{{sym_name = "main", function_type = !llvm.func<i32 ()>}}> ({{
  ^entry:
    %zero = "llvm.mlir.constant"() <{{value = 0 : i32}}> : () -> i32
    %one = "llvm.mlir.constant"() <{{value = 1 : i32}}> : () -> i32
    %limit = "llvm.mlir.constant"() <{{value = {args.iterations} : i32}}> : () -> i32
    "llvm.br"(%zero) [^loop] : (i32) -> ()
  ^loop(%i : i32):
    %next = "llvm.add"(%i, %one) : (i32, i32) -> i32
    %again = "llvm.icmp"(%next, %limit) <{{predicate = 6 : i64}}> : (i32, i32) -> i1
    "llvm.cond_br"(%again, %next, %next) [^loop, ^exit] <{{operandSegmentSizes = array<i32: 1, 1, 1>}}> : (i1, i32, i32) -> ()
  ^exit(%result : i32):
    "llvm.return"(%result) : (i32) -> ()
  }}) : () -> ()
}}) : () -> ()
''')
