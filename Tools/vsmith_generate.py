#!/usr/bin/env python3
"""Generate a single random closed MLIR module for VeIR testing."""

from __future__ import annotations

import argparse
import random
import secrets
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


BINARY_OPS = ("llvm.add", "llvm.sub", "llvm.mul", "llvm.and", "llvm.or", "llvm.xor")
SHIFT_OPS = ("llvm.shl", "llvm.lshr", "llvm.ashr")
DIV_OPS = ("llvm.sdiv", "llvm.udiv", "llvm.srem", "llvm.urem")
ICMP_PREDS = tuple(range(10))

# Integer intrinsics, grouped by arity. All operands and the result share one
# type. `ctlz`/`cttz` additionally carry an `is_zero_poison` flag, and `bswap`
# is only defined for the byte-swappable widths below.
INTRINSIC_BINARY = ("llvm.intr.smax", "llvm.intr.smin", "llvm.intr.umax", "llvm.intr.umin")
INTRINSIC_TERNARY = ("llvm.intr.fshl", "llvm.intr.fshr")
INTRINSIC_COUNT = ("llvm.intr.ctpop", "llvm.intr.bitreverse")
INTRINSIC_ZERO_POISON = ("llvm.intr.ctlz", "llvm.intr.cttz")
# Saturating arithmetic intrinsics: two operands sharing the result type, no
# attributes. The `*shl.sat` shift-amount operand may be out of range (>= the
# bit width), which yields poison, just like the ordinary shifts.
INTRINSIC_SAT_BINARY = (
    "llvm.intr.sadd.sat", "llvm.intr.uadd.sat",
    "llvm.intr.ssub.sat", "llvm.intr.usub.sat",
    "llvm.intr.sshl.sat", "llvm.intr.ushl.sat",
)
BSWAP_WIDTHS = (16, 32, 64)

# Widths the RISC-V backend can compute on. In RISC-V mode, i1 appears only as
# the result of an icmp, and that result may feed only a conditional branch or
# the condition of an llvm.select: icmps take i32 or i64 operands (never i1),
# and i1 values are never consumed by arithmetic/bitwise/shift/cast operations
# or further comparisons.
RISCV_WIDTHS = (32, 64)

# Memory: allocate aggregates and derive pointers through different type paths.
# Every pointer has an eight-byte access window, possibly overlapping another.
# Initialize and checksum these windows through independent byte GEPs, so a
# wrong aggregate offset cannot hide behind matching stores and loads. Sparse
# windows keep large allocations inexpensive. All accesses use alignment 1.
# Loads and stores use only the widths the interpreter can move to and from
# memory (and, in RISC-V mode, those the backend selects).
MEM_WIDTHS = (8, 16, 32, 64)
RISCV_MEM_WIDTHS = (32, 64)
MEM_MAX_BYTES = 8192
MEM_MAX_POINTERS = 12
MEM_ALIGN_PROPS = ' <{"alignment" = 1 : i64}>'


def align_to(size: int, alignment: int) -> int:
    return (size + alignment - 1) // alignment * alignment


@dataclass(frozen=True)
class MemoryType:
    """An LLVM type and its RV64 allocation stride, alignment and GEP paths.

    Only addresses use these types; memory transfers remain scalar integers.
    Vectors are leaves because indexing vector elements is not implemented.
    """

    text: str
    size: int
    alignment: int
    element: MemoryType | None = None
    count: int = 0
    fields: tuple[tuple[int, MemoryType], ...] = ()


def random_memory_type(rng: random.Random, depth: int = 3) -> MemoryType:
    kind = rng.random() if depth else 0.0
    if kind < 0.30:
        width = rng.choice((1, 8, 16, 24, 32, 40, 64, 128, 200))
        alignment = next(a for a in (1, 2, 4, 8, 16) if width <= a * 8 or a == 16)
        return MemoryType(f"i{width}", align_to((width + 7) // 8, alignment), alignment)
    if kind < 0.40:
        count, width = rng.choice(((17, 1), (5, 24), (3, 32), (2, 64)))
        size = (count * width + 7) // 8
        alignment = 1 << (size - 1).bit_length()
        return MemoryType(f"vector<{count}xi{width}>", alignment, alignment)
    if kind < 0.65:
        elem = random_memory_type(rng, depth - 1)
        count = rng.choice((0, 1, 2, 3, 5, 8, 17))
        return MemoryType(f"!llvm.array<{count} x {elem.text}>",
                          count * elem.size, elem.alignment, elem, count)
    packed = rng.choice((False, True))
    members = [random_memory_type(rng, depth - 1) for _ in range(rng.randint(0, 4))]
    fields = []
    offset, alignment = 0, 1
    for member in members:
        field_alignment = 1 if packed else member.alignment
        offset = align_to(offset, field_alignment)
        fields.append((offset, member))
        offset += member.size
        alignment = max(alignment, field_alignment)
    body = ", ".join(member.text for member in members)
    text = f"!llvm.struct<{'packed ' if packed else ''}({body})>"
    return MemoryType(text, align_to(offset, alignment), alignment, fields=tuple(fields))


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
        # Pointers into the entry block's alloca, as (name, byte offset). They
        # live outside the integer pools: they are never returned, cast, or
        # passed to blocks, only used as load/store addresses.
        self.mem_size = 0
        self.ptrs: list[tuple[str, int]] = []
        self.check_ptrs: list[str] = []
        self.index_slot = ""

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

    def random_dominating_value(self, width: int) -> str:
        typ = f"i{width}"
        local = self.local.get(typ, [])
        imported = self.imported.get(typ, [])
        if local and imported:
            pool = local if self.rng.random() < 0.7 else imported
        else:
            pool = local or imported
        if not pool:
            if width == 1:
                # Never inject a fresh i1 literal: i1 constants have no RISC-V
                # lowering. Every boolean must originate from a comparison.
                return self.make_bool()
            return self.add_const(typ, rand_const_val(self.rng, width))
        return self.rng.choice(pool)

    def make_bool(self) -> str:
        """Materialize an i1 value via an icmp rather than a fresh literal."""
        typ = self.rand_type()
        while bitwidth(typ) == 1:
            typ = self.rand_type()
        width = bitwidth(typ)
        lhs = self.random_dominating_value(width)
        rhs = self.random_dominating_value(width)
        pred = self.rng.choice(ICMP_PREDS)
        props = f' <{{"predicate" = {pred} : i64}}>'
        return self.add_operation("llvm.icmp", [lhs, rhs], [typ, typ], "i1", props)

    def nsw_nuw_props(self) -> str:
        flags = self.rng.choice((0, 1, 2, 3))
        if flags == 0:
            return ""
        return f' <{{"overflowFlags" = {flags} : i32}}>'

    def binary_props(self, op: str) -> str:
        if op in ("llvm.add", "llvm.sub", "llvm.mul"):
            return self.nsw_nuw_props()
        if op == "llvm.or":
            return self.rng.choice(("", " <{isDisjoint}>"))
        return ""

    def shift_props(self, op: str) -> str:
        if op == "llvm.shl":
            return self.nsw_nuw_props()
        return self.rng.choice(("", " <{isExact}>"))

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
            return self.rng.choice(("", " <{isExact}>"))
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

    def emit_intrinsic(self) -> None:
        """Emit a random integer intrinsic. All operands share the result type.

        `bswap` is restricted to widths it is defined on; in RISC-V mode every
        intrinsic uses i32 or i64 (the only widths `rand_type` yields there).

        Note: the saturating arithmetic intrinsics and `llvm.intr.abs` are only
        lowered at i64 in RISC-V mode (there is no i32 isel yet), so `--riscv`
        mode pins them to i64 rather than letting `rand_type` also pick i32.
        """
        if self.rng.random() < 0.30:
            if self.rng.random() < 0.85:
                op = self.rng.choice(INTRINSIC_SAT_BINARY)
                typ = "i64" if self.riscv else self.rand_type()
                width = bitwidth(typ)
                lhs = self.random_dominating_value(width)
                rhs = self.random_dominating_value(width)
                self.add_operation(op, [lhs, rhs], [typ, typ], typ)
            else:
                # `abs` carries an `is_int_min_poison` i1 flag deciding whether
                # abs(INT_MIN) is poison (true) or INT_MIN (false).
                typ = "i64" if self.riscv else self.rand_type()
                operand = self.random_dominating_value(bitwidth(typ))
                poison = "true" if self.rng.random() < 0.5 else "false"
                self.add_operation("llvm.intr.abs", [operand], [typ], typ,
                                   f" <{{is_int_min_poison = {poison}}}>")
            return
        r = self.rng.random()
        if r < 0.30:
            op = self.rng.choice(INTRINSIC_BINARY)
            typ = self.rand_type()
            width = bitwidth(typ)
            lhs = self.random_dominating_value(width)
            rhs = self.random_dominating_value(width)
            self.add_operation(op, [lhs, rhs], [typ, typ], typ)
        elif r < 0.55:
            op = self.rng.choice(INTRINSIC_TERNARY)
            typ = self.rand_type()
            width = bitwidth(typ)
            # General funnel shift: two independent data operands (when they
            # happen to be equal this degenerates to the rotate special case).
            hi = self.random_dominating_value(width)
            lo = self.random_dominating_value(width)
            amount = self.random_dominating_value(width)
            self.add_operation(op, [hi, lo, amount], [typ, typ, typ], typ)
        elif r < 0.78:
            op = self.rng.choice(INTRINSIC_ZERO_POISON)
            typ = self.rand_type()
            operand = self.random_dominating_value(bitwidth(typ))
            poison = "true" if self.rng.random() < 0.5 else "false"
            self.add_operation(op, [operand], [typ], typ, f" <{{is_zero_poison = {poison}}}>")
        elif r < 0.92:
            op = self.rng.choice(INTRINSIC_COUNT)
            typ = self.rand_type()
            operand = self.random_dominating_value(bitwidth(typ))
            self.add_operation(op, [operand], [typ], typ)
        else:
            typ = self.rand_type() if self.riscv else f"i{self.rng.choice(BSWAP_WIDTHS)}"
            operand = self.random_dominating_value(bitwidth(typ))
            self.add_operation("llvm.intr.bswap", [operand], [typ], typ)

    def emit_alloca(self) -> None:
        """Allocate up to 8 KiB and construct GEPs with known byte offsets."""
        while True:
            elem = random_memory_type(self.rng)
            if 0 < elem.size <= MEM_MAX_BYTES // 2:
                break
        target = self.rng.choice((64, 128, 256, 512, 2048, 4096, MEM_MAX_BYTES))
        count = max((8 + elem.size - 1) // elem.size,
                    self.rng.choice((1, 2, 3, max(1, target // elem.size))))
        count = min(count, MEM_MAX_BYTES // elem.size)
        self.mem_size = count * elem.size
        # The full RISC-V pipeline currently selects an i32 count before
        # alloca lowering can recover its constant value. Keep counts i64 there.
        size_type = "i64" if self.riscv else self.rng.choice(("i32", "i64"))
        size = self.add_const(size_type, count)
        base = self.name("mem")
        alignment = self.rng.choice(("", ", alignment = 1 : i64", ", alignment = 16 : i64"))
        self.lines.append(
            f'  {base} = "llvm.alloca"({size}) <{{elem_type = {elem.text}{alignment}}}> '
            f': ({size_type}) -> !llvm.ptr'
        )
        one = self.add_const("i64", 1)
        self.index_slot = self.name("index_slot")
        self.lines.append(
            f'  {self.index_slot} = "llvm.alloca"({one}) <{{elem_type = i64}}> : (i64) -> !llvm.ptr'
        )
        max_offset = self.mem_size - 8
        self.ptrs = [(base, 0)]
        for _ in range(self.rng.randint(6, MEM_MAX_POINTERS) - 1):
            if self.rng.random() < 0.65:
                # Walk the allocated type, keeping struct indices constant.
                # The first index steps over complete allocated objects.
                index = self.rng.randrange(count)
                if self.rng.random() < 0.25:
                    index = self.rng.choice((-1, count))
                indices = [(index, True)]
                offset = index * elem.size
                current = elem
                while self.rng.random() < 0.85:
                    if current.element is not None and current.count:
                        index = self.rng.randrange(current.count)
                        if self.rng.random() < 0.25:
                            index = self.rng.choice((-1, current.count))
                        indices.append((index, True))
                        offset += index * current.element.size
                        current = current.element
                    elif current.fields:
                        index = self.rng.randrange(len(current.fields))
                        field_offset, current = current.fields[index]
                        indices.append((index, False))
                        offset += field_offset
                    else:
                        break
                # Non-inbounds GEPs may step outside an array's nominal bounds.
                # Rebase so the final pointer has eight accessible bytes, even
                # for negative indices, empty members and fields near the end.
                adjustment = max(0, min(max_offset, offset)) - offset
                start = self.byte_gep(base, adjustment) if adjustment else base
                ptr = self.gep(start, elem.text, indices)
                offset += adjustment
            else:
                # Rebase an existing pointer, including backwards steps and
                # immediate-boundary offsets, without leaving the allocation.
                start, old_offset = self.rng.choice(self.ptrs)
                candidates = [0, max_offset, self.rng.randint(0, max_offset)]
                candidates += [old_offset + d for d in (-2049, -2048, -1, 1, 2047, 2048)]
                offset = self.rng.choice([o for o in candidates if 0 <= o <= max_offset])
                delta = offset - old_offset
                if delta == 0 and self.rng.random() < 0.5:
                    ptr = self.gep(start, elem.text, [])
                else:
                    ptr = self.gep(start, "i8", [(delta, True)])
            self.ptrs.append((ptr, offset))
        self.init_region(base)

    def gep(self, base: str, elem_type: str, indices: list[tuple[int, bool]]) -> str:
        """Emit a type path; the bool says whether an index may be dynamic.

        Use both signed and unsigned spellings of raw i32 indices. Dynamic
        operands include i32 and i64 constants and initialized volatile loads,
        which keep runtime index scaling alive through constant propagation.
        No inbounds/no-wrap promises are made for the rebased paths.
        """
        operands, types, raw = [base], ["!llvm.ptr"], []
        all_constant = self.rng.random() < 0.25
        for value, can_be_dynamic in indices:
            if can_be_dynamic and not all_constant and self.rng.random() < 0.75:
                typ = self.rng.choice(("i32", "i64"))
                idx = self.add_const(typ, value)
                if self.rng.random() < 0.5:
                    self.lines.append(
                        f'  "llvm.store"({idx}, {self.index_slot}){MEM_ALIGN_PROPS} '
                        f': ({typ}, !llvm.ptr) -> ()'
                    )
                    idx = self.add_operation("llvm.load", [self.index_slot], ["!llvm.ptr"], typ,
                                             ' <{alignment = 1 : i64, volatile_}>')
                operands.append(idx)
                types.append(typ)
                value = -2147483648
            if value < 0 and self.rng.random() < 0.5:
                value &= 0xffffffff
            raw.append(str(value))
        raw_attr = "array<i32" + (": " + ", ".join(raw) if raw else "") + ">"
        ptr = self.name("p")
        self.lines.append(
            f'  {ptr} = "llvm.getelementptr"({", ".join(operands)}) '
            f'<{{elem_type = {elem_type}, rawConstantIndices = {raw_attr}}}> '
            f': ({", ".join(types)}) -> !llvm.ptr'
        )
        return ptr

    def byte_gep(self, base: str, offset: int) -> str:
        """A simple, independent address for initialization and observation."""
        ptr = self.name("byte")
        self.lines.append(
            f'  {ptr} = "llvm.getelementptr"({base}) '
            f'<{{elem_type = i8, rawConstantIndices = array<i32: {offset}>}}> '
            f': (!llvm.ptr) -> !llvm.ptr'
        )
        return ptr

    def init_region(self, base: str) -> None:
        """Initialize all reachable windows, including overlapping accesses."""
        intervals: list[tuple[int, int]] = []
        for _, offset in sorted(self.ptrs, key=lambda p: p[1]):
            if intervals and offset <= intervals[-1][1]:
                lo, hi = intervals[-1]
                intervals[-1] = (lo, max(hi, offset + 8))
            else:
                intervals.append((offset, offset + 8))
        for lo, hi in intervals:
            offset = lo
            while offset < hi:
                # Each interval contains at least eight bytes. Overlap the
                # last store when necessary, keeping checksum loads at i64.
                offset = min(offset, hi - 8)
                val = self.add_const("i64", rand_const_val(self.rng, 64))
                ptr = self.byte_gep(base, offset)
                self.lines.append(f'  "llvm.store"({val}, {ptr}){MEM_ALIGN_PROPS} : (i64, !llvm.ptr) -> ()')
                self.check_ptrs.append(ptr)
                offset += 8

    def memory_checksum(self) -> str:
        """Observe every accessed byte and every generated GEP in an i64 hash.

        Multiplying between XORs makes order matter: duplicate addresses or
        equal values do not simply cancel. Use unflagged wrapping arithmetic.
        """
        result = self.add_const("i64", 0x123456789abcdef)
        factor = self.add_const("i64", 0x100000001b3)
        for ptr in self.check_ptrs + [ptr for ptr, _ in self.ptrs]:
            value = self.add_operation("llvm.load", [ptr], ["!llvm.ptr"], "i64", MEM_ALIGN_PROPS)
            result = self.add_operation("llvm.mul", [result, factor], ["i64", "i64"], "i64")
            result = self.add_operation("llvm.xor", [result, value], ["i64", "i64"], "i64")
        return result

    def mem_widths(self) -> tuple[int, ...]:
        return RISCV_MEM_WIDTHS if self.riscv else MEM_WIDTHS

    def mem_access(self) -> tuple[str, int]:
        """Pick an access within an initialized eight-byte window."""
        ptr, _ = self.rng.choice(self.ptrs)
        return ptr, self.rng.choice(self.mem_widths())

    def emit_store(self) -> None:
        ptr, width = self.mem_access()
        typ = f"i{width}"
        val = self.random_dominating_value(width)
        self.lines.append(f'  "llvm.store"({val}, {ptr}){MEM_ALIGN_PROPS} : ({typ}, !llvm.ptr) -> ()')

    def emit_load(self) -> None:
        ptr, width = self.mem_access()
        self.add_operation("llvm.load", [ptr], ["!llvm.ptr"], f"i{width}", MEM_ALIGN_PROPS)

    def emit_freeze(self) -> None:
        typ = self.rand_type()
        operand = self.random_dominating_value(bitwidth(typ))
        self.add_operation("llvm.freeze", [operand], [typ], typ)

    def add_block_body(self, count: int) -> None:
        exprs: list[tuple[str, str, str, str, str]] = []
        for _ in range(count):
            if self.ptrs and self.rng.random() < 0.20:
                if self.rng.random() < 0.5:
                    self.emit_store()
                else:
                    self.emit_load()
                continue
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
                props = " <{nonNeg}>" if op == "llvm.zext" and self.rng.random() < 0.5 else ""
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
                # icmp operands are ordinary integer values; in RISC-V mode that
                # means i32 or i64 (rand_type never yields i1 there), so an icmp
                # result is never fed back into another comparison.
                typ = self.rand_type()
                width = bitwidth(typ)
                lhs = self.random_dominating_value(width)
                rhs = self.random_dominating_value(width)
                pred = self.rng.choice(ICMP_PREDS)
                props = f' <{{"predicate" = {pred} : i64}}>'
                self.add_operation("llvm.icmp", [lhs, rhs], [typ, typ], "i1", props)
            elif choice < 0.92:
                typ = self.rand_type()
                width = bitwidth(typ)
                cond = self.random_dominating_value(1)
                tval = self.random_dominating_value(width)
                fval = self.random_dominating_value(width)
                self.add_operation("llvm.select", [cond, tval, fval], ["i1", typ, typ], typ)
            elif choice < 0.975:
                self.emit_intrinsic()
            # elif choice < 0.995:
            #     self.emit_freeze()
            else:
                typ = self.rand_type()
                self.add_const(typ, rand_const_val(self.rng, bitwidth(typ)))


def generate(path: Path, rng: random.Random, riscv: bool = False, memory_only: bool = False) -> None:
    """Write a random closed MLIR module to path."""
    gen = Generator(rng, riscv)
    lines: list[str] = []
    return_type: str | None = None
    # Keep a substantial fraction free of unrelated poison/UB so the memory
    # checksum remains informative, while retaining mixed arithmetic/CFG cases.
    memory_only = memory_only or rng.random() < 0.5
    num_blocks = 1 if memory_only else rng.randint(1, 20)
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
        if block_id == 0:
            gen.emit_alloca()
        if memory_only:
            for _ in range(rng.randint(6, 20)):
                if rng.random() < 0.5:
                    gen.emit_store()
                else:
                    gen.emit_load()
        else:
            gen.seed_block()
            gen.add_block_body(rng.randint(3, 18))

        snap_values[block_id] = {t: list(vs) for t, vs in gen.local.items()}
        snap_all[block_id] = list(gen.local_all)

        successors = [f"^bb{succ}" for succ in range(block_id + 1, num_blocks)]
        if not successors:
            arithmetic = None if memory_only else gen.random_return_value()
            returned = gen.memory_checksum()
            if arithmetic is not None:
                value, typ = arithmetic
                if bitwidth(typ) < 64:
                    value = gen.add_operation("llvm.zext", [value], [typ], "i64")
                elif bitwidth(typ) > 64:
                    value = gen.add_operation("llvm.trunc", [value], [typ], "i64")
                returned = gen.add_operation("llvm.xor", [returned, value], ["i64", "i64"], "i64")
            return_type = "i64"
            lines.append(f'  "llvm.return"({returned}) : (i64) -> ()')
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
                        help="restrict bitwidths to those the RISC-V backend supports (32, 64)")
    parser.add_argument("--memory-only", action="store_true",
                        help="generate only defined GEP/load/store programs returning a memory checksum")
    args = parser.parse_args(argv)
    seed = args.seed if args.seed is not None else secrets.randbits(64)
    generate(args.output, random.Random(seed), args.riscv, args.memory_only)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
