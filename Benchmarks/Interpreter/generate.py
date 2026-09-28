#!/usr/bin/env python3
"""Generate an MLIR addition chain sized by operations or exact file line count."""
import argparse
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("output", type=Path)
size = parser.add_mutually_exclusive_group()
size.add_argument("--operations", type=int, help="executed operations (default: 1000)")
size.add_argument("--lines", type=int, help="exact file line count, including six wrapper/comment lines")
parser.add_argument("--dialect", choices=("arith", "llvm"), default="llvm")
args = parser.parse_args()
if args.lines is not None:
    args.operations = args.lines - 6
elif args.operations is None:
    args.operations = 1000
if args.operations < 3:
    parser.error("at least three operations (nine file lines) are required")
constant, add = ("arith.constant", "arith.addi") if args.dialect == "arith" else ("llvm.mlir.constant", "llvm.add")
lines = [
    f"// {args.operations} executed operations: 2 constants, {args.operations - 3} additions, 1 return.",
    f"// Expected result: {args.operations - 3} : i32.",
    '"builtin.module"() ({',
    '  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({',
    f'    %v0 = "{constant}"() <{{value = 0 : i32}}> : () -> i32',
    f'    %one = "{constant}"() <{{value = 1 : i32}}> : () -> i32',
]
for i in range(1, args.operations - 2):
    lines.append(f'    %v{i} = "{add}"(%v{i - 1}, %one) : (i32, i32) -> i32')
lines += [f'    "func.return"(%v{args.operations - 3}) : (i32) -> ()', '  }) : () -> ()', '}) : () -> ()']
args.output.write_text("\n".join(lines) + "\n")
