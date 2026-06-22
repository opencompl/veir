#!/usr/bin/env python3
"""Generate a single random closed MLIR module for VeIR testing."""

# TODO:
# - support llvm.[load,store,alloca]

from __future__ import annotations

import argparse
import random
import secrets
import sys
from collections import defaultdict
from pathlib import Path


BINARY_OPS = ("llvm.add", "llvm.sub", "llvm.mul", "llvm.and", "llvm.or", "llvm.xor")
SHIFT_OPS = ("llvm.shl", "llvm.lshr", "llvm.ashr")
DIV_OPS = ("llvm.sdiv", "llvm.udiv", "llvm.srem", "llvm.urem")
ICMP_PREDS = tuple(range(10))

# Widths the RISC-V backend can compute on. i1 is permitted only as an icmp
# operand (so comparison results can feed into further comparisons); it is
# never produced or consumed by arithmetic/bitwise/shift/cast operations.
RISCV_WIDTHS = (8, 16, 32, 64)


def bitwidth(typ: str) -> int:
    return int(typ[1:])


def rand_int_type(rng: random.Random, riscv: bool = False) -> str:
    if riscv:
        return f"i{rng.choice(RISCV_WIDTHS)}"
    if rng.random() < 0.5:
        common = ("i1", "i8", "i16", "i32", "i64")
        return rng.choice(common)
    else:
        return f"i{rng.randint(1, 95)}"


def laplace_bias(rng: random.Random, scale: float, clip: int) -> int:
    mag = rng.expovariate(1.0 / scale)
    bias = mag if rng.random() < 0.5 else -mag
    return max(-clip, min(clip, round(bias)))


def rand_const_val(rng: random.Random, width: int) -> int:
    if rng.random() < 0.05:
        int_min = -(1 << (width - 1))
        int_max = (1 << (width - 1)) - 1
        base = rng.choice([int_min, int_max])
        val = (base + laplace_bias(rng, 2.43, 10))
        val &= (1 << width) - 1
        if val >= 1 << (width - 1):
            val -= 1 << width
        return val
    if width >= 9 and rng.random() < 0.75:
        mask = (1 << width) - 1
        val = 0
        for _ in range(rng.randint(0, 5)):
            val |= 1 << rng.randint(0, width - 1)
        val += laplace_bias(rng, 2.43, 10)
        if rng.random() < 0.5:
            val ^= mask
        val &= mask
        if val >= 1 << (width - 1):
            val -= 1 << width
        return val
    return rng.randint(-(2 ** (width - 1)), 2 ** (width - 1) - 1)


def format_block_arguments(arg_names: list[str], arg_types: list[str]) -> str:
    if not arg_names:
        return ""
    return ", ".join(f"{name} : {typ}" for name, typ in zip(arg_names, arg_types))


class Generator:
    def __init__(self, rng: random.Random, riscv: bool = False) -> None:
        self.rng = rng
        self.riscv = riscv
        self.counter = 0
        self.lines: list[str] = []
        self.imported: dict[str, list[str]] = defaultdict(list)
        self.imported_all: list[tuple[str, str]] = []
        self.local: dict[str, list[str]] = defaultdict(list)
        self.local_all: list[tuple[str, str]] = []

    def name(self, prefix: str) -> str:
        self.counter += 1
        return f"%{prefix}{self.counter}"

    def set_state(
        self,
        lines: list[str],
        imported: dict[str, list[str]],
        imported_all: list[tuple[str, str]],
        local_args: list[tuple[str, str]],
    ) -> None:
        self.lines = lines
        self.imported = imported
        self.imported_all = imported_all
        self.local = defaultdict(list)
        self.local_all = []
        for name, typ in local_args:
            self.local[typ].append(name)
            self.local_all.append((name, typ))

    def rand_type(self) -> str:
        return rand_int_type(self.rng, self.riscv)

    def rand_icmp_type(self) -> str:
        """Operand type for an icmp. In RISC-V mode, i1 is allowed here so that
        comparison results can be fed back into further comparisons."""
        if self.riscv:
            return f"i{self.rng.choice((1,) + RISCV_WIDTHS)}"
        return self.rand_type()

    def random_dominating_value(self, width: int) -> str:
        typ = f"i{width}"
        local = self.local.get(typ, [])
        imported = self.imported.get(typ, [])
        if local and imported:
            pool = local if self.rng.random() < 0.7 else imported
        else:
            pool = local or imported
        if not pool:
            return self.add_const(typ, rand_const_val(self.rng, width))
        return self.rng.choice(pool)

    def nsw_nuw_props(self) -> str:
        flags = self.rng.choice((0, 1, 2, 3))
        if flags == 0:
            return ""
        return f' <{{"overflowFlags" = {flags} : i32}}>'

    def binary_props(self, op: str) -> str:
        if op in ("llvm.add", "llvm.sub", "llvm.mul"):
            return self.nsw_nuw_props()
        if op == "llvm.or":
            return self.rng.choice(("", " <{disjoint}>"))
        return ""

    def shift_props(self, op: str) -> str:
        if op == "llvm.shl":
            return self.nsw_nuw_props()
        return self.rng.choice(("", " <{exact}>"))

    def shift_amount(self, width: int) -> str:
        """Generate a shift amount for a width-`width` shift.

        50%: constant in [0, width-1] (always inbounds).
        25%: dominating value masked with `(1 << floor_log2(width)) - 1` (always inbounds).
        25%: raw dominating value (may be out of bounds, producing poison).
        """
        typ = f"i{width}"
        r = self.rng.random()
        if r < 0.50:
            return self.add_const(typ, self.rng.randint(0, width - 1))
        if r < 0.75:
            var = self.random_dominating_value(width)
            mask = (1 << (width.bit_length() - 1)) - 1
            mask_const = self.add_const(typ, mask)
            return self.add_operation("llvm.and", [var, mask_const], [typ, typ], typ)
        return self.random_dominating_value(width)

    def div_props(self, op: str) -> str:
        if op in ("llvm.sdiv", "llvm.udiv"):
            return self.rng.choice(("", " <{exact}>"))
        return ""

    def divisor(self, width: int) -> str:
        """Generate a divisor for a width-`width` div/rem.

        50%: constant (occasionally zero -> UB).
        25%: dominating value OR'd with 1 (guaranteed non-zero, but still poison if input is).
        25%: raw dominating value (may be zero, producing UB).
        """
        typ = f"i{width}"
        r = self.rng.random()
        if r < 0.50:
            return self.add_const(typ, rand_const_val(self.rng, width))
        if r < 0.75:
            var = self.random_dominating_value(width)
            one = self.add_const(typ, 1)
            return self.add_operation("llvm.or", [var, one], [typ, typ], typ)
        return self.random_dominating_value(width)

    def add_const(self, typ: str, val: int) -> str:
        name = self.name("c")
        self.lines.append(f'  {name} = "llvm.mlir.constant"() <{{"value" = {val} : {typ}}}> : () -> {typ}')
        self.local[typ].append(name)
        self.local_all.append((name, typ))
        return name

    def add_operation(
        self,
        op: str,
        operands: list[str],
        operand_types: list[str],
        result_type: str,
        props: str = "",
        name_prefix: str = "v",
    ) -> str:
        name = self.name(name_prefix)
        operands_str = ", ".join(operands)
        operand_types_str = ", ".join(operand_types)
        self.lines.append(f'  {name} = "{op}"({operands_str}){props} : ({operand_types_str}) -> {result_type}')
        self.local[result_type].append(name)
        self.local_all.append((name, result_type))
        return name

    def seed_block(self) -> None:
        typ = self.rand_type()
        width = bitwidth(typ)
        self.add_const(typ, rand_const_val(self.rng, width))
        self.add_const(typ, rand_const_val(self.rng, width))
        if self.rng.random() < 0.5:
            extra_typ = self.rand_type()
            self.add_const(extra_typ, rand_const_val(self.rng, bitwidth(extra_typ)))

    def random_branch_condition(self) -> str:
        return self.random_dominating_value(1)

    def random_return_value(self) -> tuple[str, str]:
        pool = self.local_all + self.imported_all
        if self.riscv:
            # i1 values may only feed icmps, never casts or the xor combine, so
            # keep them out of the returned set entirely.
            pool = [(name, typ) for name, typ in pool if bitwidth(typ) in RISCV_WIDTHS]
        if not pool:
            typ = self.rand_type()
            return self.add_const(typ, rand_const_val(self.rng, bitwidth(typ))), typ
        n = min(self.rng.randint(1, 25), len(pool))
        chosen = self.rng.sample(pool, n)
        target_width = self.rng.choice([bitwidth(typ) for _, typ in chosen])
        target = f"i{target_width}"
        casted: list[str] = []
        for name, typ in chosen:
            w = bitwidth(typ)
            if w == target_width:
                casted.append(name)
            elif w < target_width:
                op = self.rng.choice(("llvm.zext", "llvm.sext"))
                casted.append(self.add_operation(op, [name], [typ], target))
            else:
                casted.append(self.add_operation("llvm.trunc", [name], [typ], target))
        result = casted[0]
        for other in casted[1:]:
            result = self.add_operation("llvm.xor", [result, other], [target, target], target)
        return result, target

    def add_block_body(self, count: int) -> None:
        exprs: list[tuple[str, str, str, str, str]] = []
        for _ in range(count):
            choice = self.rng.random()
            if choice < 0.35:
                typ = self.rand_type()
                same_type_exprs = [e for e in exprs if e[3] == typ]
                if same_type_exprs and self.rng.random() < 0.55:
                    op, lhs, rhs, typ, props = self.rng.choice(same_type_exprs)
                else:
                    op = self.rng.choice(BINARY_OPS)
                    width = bitwidth(typ)
                    lhs = self.random_dominating_value(width)
                    rhs = self.random_dominating_value(width)
                    props = self.binary_props(op)
                    exprs.append((op, lhs, rhs, typ, props))
                self.add_operation(op, [lhs, rhs], [typ, typ], typ, props)
            elif choice < 0.48:
                typ = self.rand_type()
                width = bitwidth(typ)
                lhs = self.random_dominating_value(width)
                rhs = self.shift_amount(width)
                op = self.rng.choice(SHIFT_OPS)
                props = self.shift_props(op)
                self.add_operation(op, [lhs, rhs], [typ, typ], typ, props)
            elif choice < 0.60:
                typ = self.rand_type()
                width = bitwidth(typ)
                lhs = self.random_dominating_value(width)
                rhs = self.divisor(width)
                op = self.rng.choice(DIV_OPS)
                props = self.div_props(op)
                self.add_operation(op, [lhs, rhs], [typ, typ], typ, props)
            elif choice < 0.72:
                src = self.rand_type()
                src_w = bitwidth(src)
                op = self.rng.choice(("llvm.sext", "llvm.zext"))
                if self.riscv:
                    wider = [w for w in RISCV_WIDTHS if w > src_w]
                    if not wider:
                        continue
                    dst = f"i{self.rng.choice(wider)}"
                else:
                    if src_w >= 95:
                        continue
                    dst = f"i{self.rng.randint(src_w + 1, 95)}"
                props = " <{nneg}>" if op == "llvm.zext" and self.rng.random() < 0.5 else ""
                operand = self.random_dominating_value(src_w)
                self.add_operation(op, [operand], [src], dst, props)
            elif choice < 0.82:
                src = self.rand_type()
                src_w = bitwidth(src)
                if self.riscv:
                    narrower = [w for w in RISCV_WIDTHS if w < src_w]
                    if not narrower:
                        continue
                    dst = f"i{self.rng.choice(narrower)}"
                else:
                    if src_w <= 1:
                        continue
                    dst = f"i{self.rng.randint(1, src_w - 1)}"
                props = self.nsw_nuw_props()
                operand = self.random_dominating_value(src_w)
                self.add_operation("llvm.trunc", [operand], [src], dst, props)
            elif choice < 0.90:
                typ = self.rand_icmp_type()
                width = bitwidth(typ)
                lhs = self.random_dominating_value(width)
                rhs = self.random_dominating_value(width)
                pred = self.rng.choice(ICMP_PREDS)
                props = f' <{{"predicate" = {pred} : i64}}>'
                self.add_operation("llvm.icmp", [lhs, rhs], [typ, typ], "i1", props)
            elif choice < 0.96:
                typ = self.rand_type()
                width = bitwidth(typ)
                cond = self.random_dominating_value(1)
                tval = self.random_dominating_value(width)
                fval = self.random_dominating_value(width)
                self.add_operation("llvm.select", [cond, tval, fval], ["i1", typ, typ], typ)
            else:
                typ = self.rand_type()
                self.add_const(typ, rand_const_val(self.rng, bitwidth(typ)))


def generate(path: Path, rng: random.Random, riscv: bool = False) -> None:
    """Write a random closed MLIR module to path."""
    gen = Generator(rng, riscv)
    lines: list[str] = []
    return_type: str | None = None
    num_blocks = rng.randint(1, 20)
    block_arg_types: list[list[str]] = [[]]
    block_arg_names: list[list[str]] = [[]]

    for block_id in range(1, num_blocks):
        arg_count = rng.randint(0, 5)
        arg_types = [rand_int_type(rng, riscv) for _ in range(arg_count)]
        arg_names = [f"%arg{block_id}_{arg_idx}" for arg_idx in range(arg_count)]
        block_arg_types.append(arg_types)
        block_arg_names.append(arg_names)

    preds: list[set[int]] = [set() for _ in range(num_blocks)]
    doms: list[set[int]] = [set() for _ in range(num_blocks)]
    snap_values: list[dict[str, list[str]]] = [defaultdict(list) for _ in range(num_blocks)]
    snap_all: list[list[tuple[str, str]]] = [[] for _ in range(num_blocks)]

    for block_id in range(num_blocks):
        if block_id == 0:
            doms[0] = {0}
        elif preds[block_id]:
            doms[block_id] = {block_id} | set.intersection(*(doms[p] for p in preds[block_id]))
        else:
            doms[block_id] = set(range(block_id + 1))

        imported: dict[str, list[str]] = defaultdict(list)
        imported_all: list[tuple[str, str]] = []
        for d in sorted(doms[block_id] - {block_id}):
            for typ, names in snap_values[d].items():
                imported[typ].extend(names)
            imported_all.extend(snap_all[d])

        local_args = list(zip(block_arg_names[block_id], block_arg_types[block_id]))
        header_args = format_block_arguments(block_arg_names[block_id], block_arg_types[block_id])
        lines.append(f"^bb{block_id}({header_args}):")
        gen.set_state(lines, imported, imported_all, local_args)
        gen.seed_block()
        gen.add_block_body(rng.randint(3, 18))

        snap_values[block_id] = {t: list(vs) for t, vs in gen.local.items()}
        snap_all[block_id] = list(gen.local_all)

        successors = [f"^bb{succ}" for succ in range(block_id + 1, num_blocks)]
        if not successors:
            returned, typ = gen.random_return_value()
            return_type = typ
            lines.append(f'  "llvm.return"({returned}) : ({typ}) -> ()')
            continue

        if rng.random() < 0.20:
            target = rng.choice(range(block_id + 1, num_blocks))
            target_types = block_arg_types[target]
            target_args = [gen.random_dominating_value(bitwidth(typ)) for typ in target_types]
            operands_str = ", ".join(target_args)
            operand_types_str = ", ".join(target_types)
            lines.append(
                f'  "llvm.br"({operands_str}) [^bb{target}] '
                f': ({operand_types_str}) -> ()'
            )
            preds[target].add(block_id)
            continue

        cond = gen.random_branch_condition()
        if len(successors) == 1:
            true_block = false_block = block_id + 1
        else:
            true_block, false_block = rng.sample(range(block_id + 1, num_blocks), 2)
        true_dest = f"^bb{true_block}"
        false_dest = f"^bb{false_block}"
        true_types = block_arg_types[true_block]
        false_types = block_arg_types[false_block]
        true_args = [gen.random_dominating_value(bitwidth(typ)) for typ in true_types]
        false_args = [gen.random_dominating_value(bitwidth(typ)) for typ in false_types]
        operands = [cond] + true_args + false_args
        operand_types = ["i1"] + true_types + false_types
        operands_str = ", ".join(operands)
        operand_types_str = ", ".join(operand_types)
        lines.append(
            f'  "llvm.cond_br"({operands_str}) [{true_dest}, {false_dest}] '
            f'<{{"operandSegmentSizes" = array<i32: 1, {len(true_args)}, {len(false_args)}>}}> '
            f': ({operand_types_str}) -> ()'
        )
        preds[true_block].add(block_id)
        preds[false_block].add(block_id)

    if return_type is None:
        raise AssertionError("generated CFG has no return block")

    module_lines = [
        '"builtin.module"() ({',
        f'  "llvm.func"() <{{sym_name = "main", function_type = !llvm.func<{return_type} ()>}}> ({{',
    ]
    module_lines.extend(f"    {line}" for line in lines)
    module_lines.append("  }) : () -> ()")
    module_lines.append("}) : () -> ()")
    path.write_text("\n".join(module_lines) + "\n")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="path for the generated MLIR file")
    parser.add_argument("--seed", type=int, default=None, help="random seed; defaults to fresh system entropy")
    parser.add_argument("--riscv", action="store_true",
                        help="restrict bitwidths to those the RISC-V backend supports (8, 16, 32, 64)")
    args = parser.parse_args(argv)
    seed = args.seed if args.seed is not None else secrets.randbits(64)
    generate(args.output, random.Random(seed), args.riscv)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
