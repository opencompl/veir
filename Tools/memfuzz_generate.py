#!/usr/bin/env python3
"""Generate a random memory-exercising program in two forms at once.

The interpreter's memory model is tested by running the same program under
`veir-interpret` and under Alive2's `alive-exec`, so the two inputs must mean
the same thing.  Rather than translating one into the other, this generator
builds the program once and prints it twice: as VeIR's generic LLVM-dialect
MLIR and as LLVM IR.  A seed reproduces a program exactly.

The program is a single straight-line `@main` returning an `i64` folded from
loaded values, over objects from `alloca` and the C allocation functions.
Whether it triggers undefined behaviour is up to the draw: out-of-bounds
offsets, use after free, misaligned accesses and null dereferences all appear
with tunable probability, and the point of the harness is that both tools
agree on which of them do.
"""

from __future__ import annotations

import argparse
import random
import secrets
import sys
from dataclasses import dataclass, field
from pathlib import Path

INT_WIDTHS = (8, 16, 32, 64)
# The natural alignment of an integer of each width, which is both LLVM's ABI
# alignment and the alignment VeIR assumes when a load or store carries none.
NATURAL_ALIGN = {8: 1, 16: 2, 32: 4, 64: 8}
PTR_SIZE = 8
PTR_ALIGN = 8


@dataclass
class Obj:
    """An allocation the program made, and what the generator knows about it."""
    ptr: str
    size: int
    align: int
    kind: str          # "stack" | "heap"
    live: bool = True
    # Byte offsets known to hold a defined value, so that a load from them
    # yields a number rather than poison.  Tracked only for whole accesses
    # the generator itself made.
    written: set = field(default_factory=set)
    # Byte offsets holding part of a stored pointer, as offset -> (pointer
    # name, which of its eight bytes).  Reading these as an integer yields a
    # byte of an address, which VeIR and Alive2 lay out differently, so such a
    # value must never reach the result; reading all eight of one pointer in
    # order gives that pointer back, and anything else gives poison.
    frag: dict = field(default_factory=dict)
    # Byte offsets whose contents the generator stopped tracking.
    unknown: set = field(default_factory=set)


@dataclass
class Val:
    name: str
    width: int


@dataclass
class Ptr:
    """A pointer the program holds, and where the generator believes it points.

    `obj` is `None` when provenance was lost, which happens for a pointer read
    back out of memory; such a pointer is never chosen for an access the
    generator intends to be well defined.
    """
    name: str
    obj: "Obj | None"
    offset: int = 0


@dataclass
class Program:
    mlir: list[str] = field(default_factory=list)
    ll: list[str] = field(default_factory=list)
    decls: set[str] = field(default_factory=set)
    n: int = 0

    def fresh(self) -> str:
        self.n += 1
        return f"%v{self.n}"

    def emit(self, mlir: str, ll: str) -> None:
        self.mlir.append("      " + mlir)
        self.ll.append("  " + ll)


class Generator:
    def __init__(self, rng: random.Random, opts: argparse.Namespace) -> None:
        self.rng = rng
        self.o = opts
        self.p = Program()
        self.objs: list[Obj] = []
        self.ints: list[Val] = []
        self.ptrs: list[Ptr] = []

    # -- helpers ---------------------------------------------------------

    def const_int(self, width: int, value: int) -> str:
        name = self.p.fresh()
        mask = (1 << width) - 1
        value &= mask
        self.p.emit(
            f'{name} = "llvm.mlir.constant"() <{{value = {value} : i{width}}}> : () -> i{width}',
            f"{name} = add i{width} {value}, 0",
        )
        return name

    def maybe(self, prob: float) -> bool:
        return self.rng.random() < prob

    def live_objs(self) -> list[Obj]:
        return [o for o in self.objs if o.live]

    def defined_ptrs(self, need: int, align: int) -> list[Ptr]:
        """Pointers at which an aligned access of `need` bytes reads written bytes."""
        return [q for q in self.safe_ptrs(need, align)
                if q.obj is not None
                and all(q.offset + k in q.obj.written for k in range(need))
                and not any(q.offset + k in q.obj.frag or q.offset + k in q.obj.unknown
                            for k in range(need))]

    def find(self, ptr_name: str) -> Ptr | None:
        for q in self.ptrs:
            if q.name == ptr_name:
                return q
        return None

    def note_int_write(self, ptr_name: str, size: int) -> None:
        """Record a store of ordinary bytes, which clears any pointer there."""
        q = self.find(ptr_name)
        if q is None or q.obj is None:
            return
        for k in range(size):
            off = q.offset + k
            q.obj.written.add(off)
            q.obj.frag.pop(off, None)
            q.obj.unknown.discard(off)

    def note_ptr_write(self, ptr_name: str, stored: str) -> None:
        """Record a store of the pointer `stored`, as its eight bytes."""
        q = self.find(ptr_name)
        if q is None or q.obj is None:
            return
        for k in range(PTR_SIZE):
            off = q.offset + k
            q.obj.written.add(off)
            q.obj.frag[off] = (stored, k)
            q.obj.unknown.discard(off)

    def note_copy(self, dst_name: str, src_name: str, size: int) -> None:
        """Record a copy, which moves each byte's state to the destination."""
        d, sp = self.find(dst_name), self.find(src_name)
        if d is None or d.obj is None:
            return
        # Read the source state before touching the destination: the two can
        # be the same object, and for a copy onto itself the writes below
        # would otherwise destroy what is being read.
        state: list[tuple[tuple[str, int] | None, bool]] = []
        for k in range(size):
            if sp is None or sp.obj is None:
                state.append((None, False))
                continue
            src_off = sp.offset + k
            known = src_off in sp.obj.written and src_off not in sp.obj.unknown
            state.append((sp.obj.frag.get(src_off), known))
        for k in range(size):
            off = d.offset + k
            frag, known = state[k]
            d.obj.written.add(off)
            d.obj.unknown.discard(off)
            d.obj.frag.pop(off, None)
            if frag is not None:
                d.obj.frag[off] = frag
            elif not known:
                d.obj.unknown.add(off)

    def holds_pointer(self, ptr_name: str) -> bool:
        """Whether these eight bytes are one pointer's eight bytes, in order."""
        q = self.find(ptr_name)
        if q is None or q.obj is None:
            return False
        first = q.obj.frag.get(q.offset)
        if first is None or first[1] != 0:
            return False
        return all(q.obj.frag.get(q.offset + k) == (first[0], k) for k in range(PTR_SIZE))

    def reads_address(self, ptr_name: str, size: int) -> bool:
        """Whether an integer load here would read bytes of an address."""
        q = self.find(ptr_name)
        if q is None or q.obj is None:
            return True
        return any(q.offset + k in q.obj.frag or q.offset + k in q.obj.unknown
                   for k in range(size))

    def safe_ptrs(self, need: int, align: int) -> list[Ptr]:
        """Pointers at which an aligned access of `need` bytes stays in bounds."""
        return [q for q in self.ptrs
                if q.obj is not None and q.obj.live
                and q.offset >= 0 and q.offset + need <= q.obj.size
                and q.offset % align == 0 and q.obj.align % align == 0]

    def any_ptr(self) -> Ptr | None:
        return self.rng.choice(self.ptrs) if self.ptrs else None

    # -- allocation ------------------------------------------------------

    def gen_alloca(self) -> None:
        width = self.rng.choice(INT_WIDTHS)
        count = self.rng.randint(1, 4)
        elem = width // 8
        # Alignment is deliberately never below eight.  Alive2 reasons over
        # every layout a program could have, so an access that claims more
        # alignment than its object declares is undefined there, while VeIR
        # picks one concrete layout in which every object is 16-byte aligned
        # and the same access is fine.  That question is layout-dependent, so
        # the generator does not ask it: objects are aligned at least as
        # strictly as any access the generator makes, and misalignment is
        # reached through odd offsets instead, on which the two agree.
        align = self.rng.choice([8, 16])
        n = self.const_int(64, count)
        name = self.p.fresh()
        self.p.emit(
            f'{name} = "llvm.alloca"({n}) <{{alignment = {align} : i64, elem_type = i{width}}}> '
            f": (i64) -> !llvm.ptr",
            f"{name} = alloca i{width}, i64 {count}, align {align}",
        )
        obj = Obj(name, elem * count, align, "stack")
        self.objs.append(obj)
        self.ptrs.append(Ptr(name, obj, 0))

    def gen_malloc(self) -> None:
        fn = self.rng.choice(["malloc", "calloc"] if self.o.calloc else ["malloc"])
        size = self.rng.choice([1, 4, 8, 16, 32])
        name = self.p.fresh()
        if fn == "malloc":
            sz = self.const_int(64, size)
            self.p.decls.add("malloc")
            self.p.emit(
                f'{name} = "llvm.call"({sz}) <{{callee = @malloc, op_bundle_sizes = array<i32>, '
                f"operandSegmentSizes = array<i32: 1, 0>}}> : (i64) -> !llvm.ptr",
                f"{name} = call ptr @malloc(i64 {size})",
            )
            total = size
        else:
            count = self.rng.randint(1, 4)
            cnt = self.const_int(64, count)
            sz = self.const_int(64, size)
            self.p.decls.add("calloc")
            self.p.emit(
                f'{name} = "llvm.call"({cnt}, {sz}) <{{callee = @calloc, op_bundle_sizes = array<i32>, '
                f"operandSegmentSizes = array<i32: 2, 0>}}> : (i64, i64) -> !llvm.ptr",
                f"{name} = call ptr @calloc(i64 {count}, i64 {size})",
            )
            total = count * size
        # malloc may return null, which the model draws from its oracle; the
        # default oracle never fails, and alive-exec is told the same by the
        # harness only in that it never explores the failing branch here.
        obj = Obj(name, total, 16, "heap")
        if fn == "calloc":
            obj.written.update(range(total))
        self.objs.append(obj)
        self.ptrs.append(Ptr(name, obj, 0))

    def gen_free(self) -> None:
        heap = [o for o in self.live_objs() if o.kind == "heap"]
        if not heap:
            return
        obj = self.rng.choice(heap)
        self.p.decls.add("free")
        self.p.emit(
            f'"llvm.call"({obj.ptr}) <{{callee = @free, op_bundle_sizes = array<i32>, '
            f"operandSegmentSizes = array<i32: 1, 0>}}> : (!llvm.ptr) -> ()",
            f"call void @free(ptr {obj.ptr})",
        )
        obj.live = False

    # -- addressing ------------------------------------------------------

    def gen_gep(self) -> None:
        src = self.any_ptr()
        if src is None:
            return
        if src.obj is not None and not self.maybe(self.o.oob):
            # Stay inside the object, and land on a multiple of eight often
            # enough that a later aligned access has somewhere to go.
            target = self.rng.randrange(0, max(1, src.obj.size))
            if self.maybe(0.6):
                target -= target % 8
            offset = target - src.offset
        else:
            offset = self.rng.choice([-64, -8, -1, 1, 7, 8, 16, 64, 4096])
        idx = self.const_int(64, offset)
        name = self.p.fresh()
        self.p.emit(
            f'{name} = "llvm.getelementptr"({src.name}, {idx}) <{{elem_type = i8, '
            f'rawConstantIndices = array<i32: -2147483648>}}> : (!llvm.ptr, i64) -> !llvm.ptr',
            f"{name} = getelementptr i8, ptr {src.name}, i64 {offset}",
        )
        # The derived pointer keeps its base's provenance; its offset may well
        # be outside the object, which is the interesting case.
        self.ptrs.append(Ptr(name, src.obj, src.offset + offset))

    # -- accesses --------------------------------------------------------

    def null_ptr(self) -> str:
        name = self.p.fresh()
        self.p.emit(f'{name} = "llvm.mlir.zero"() : () -> !llvm.ptr',
                    f"{name} = getelementptr i8, ptr null, i64 0")
        return name

    def pick_read_target(self, need: int, align: int) -> str | None:
        """As `pick_target`, but preferring bytes that already hold a value."""
        if not self.maybe(self.o.ub) and not (self.o.null and self.maybe(self.o.null)):
            defined = self.defined_ptrs(need, align)
            if defined and self.maybe(self.o.defined):
                return self.rng.choice(defined).name
        return self.pick_target(need, align)

    def pick_target(self, need: int, align: int) -> str | None:
        """A pointer for an access of `need` bytes at alignment `align`.

        Most of the time this is a pointer the generator believes is in
        bounds, live and aligned, so the access is well defined.  With
        probability `--ub` it is any pointer at all, or null, so that the two
        tools have to agree on undefined behaviour as well.
        """
        if self.o.null and self.maybe(self.o.null):
            return self.null_ptr()
        if not self.maybe(self.o.ub):
            # No in-bounds pointer of this shape exists, so there is no way to
            # make this access well defined; skip it rather than reaching for
            # any pointer at all, which would smuggle in undefined behaviour
            # that `--ub 0` promised not to generate.
            safe = self.safe_ptrs(need, align)
            return self.rng.choice(safe).name if safe else None
        any_ptr = self.any_ptr()
        return any_ptr.name if any_ptr is not None else None

    def access_width(self, align_ok: bool) -> tuple[int, int]:
        width = self.rng.choice(INT_WIDTHS)
        align = 1 if not align_ok else NATURAL_ALIGN[width]
        return width, align

    def gen_store(self) -> None:
        if self.o.ptr_values and self.ptrs and self.maybe(0.2):
            ptr = self.pick_target(PTR_SIZE, PTR_ALIGN)
            if ptr is None:
                return
            src = self.rng.choice(self.ptrs).name
            self.p.emit(
                f'"llvm.store"({src}, {ptr}) <{{alignment = {PTR_ALIGN} : i64}}> '
                f": (!llvm.ptr, !llvm.ptr) -> ()",
                f"store ptr {src}, ptr {ptr}, align {PTR_ALIGN}",
            )
            self.note_ptr_write(ptr, src)
            return
        width, align = self.access_width(not self.maybe(self.o.misalign))
        ptr = self.pick_target(width // 8, align)
        if ptr is None:
            return
        val = self.const_int(width, self.rng.getrandbits(width))
        self.p.emit(
            f'"llvm.store"({val}, {ptr}) <{{alignment = {align} : i64}}> : (i{width}, !llvm.ptr) -> ()',
            f"store i{width} {val}, ptr {ptr}, align {align}",
        )
        self.note_int_write(ptr, width // 8)

    def gen_load(self) -> None:
        if self.o.ptr_values and self.maybe(0.2):
            ptr = self.pick_target(PTR_SIZE, PTR_ALIGN)
            if ptr is None:
                return
            name = self.p.fresh()
            self.p.emit(
                f'{name} = "llvm.load"({ptr}) <{{alignment = {PTR_ALIGN} : i64}}> '
                f": (!llvm.ptr) -> !llvm.ptr",
                f"{name} = load ptr, ptr {ptr}, align {PTR_ALIGN}",
            )
            # A pointer read out of bytes that a pointer was stored into is a
            # real pointer; read out of anything else it is poison. Both are
            # worth keeping, so that provenance through memory and the
            # handling of poison pointers are both exercised.
            if self.o.poison_pointers or self.holds_pointer(ptr):
                self.ptrs.append(Ptr(name, None, 0))
            return
        width, align = self.access_width(not self.maybe(self.o.misalign))
        ptr = self.pick_read_target(width // 8, align)
        if ptr is None:
            return
        name = self.p.fresh()
        self.p.emit(
            f'{name} = "llvm.load"({ptr}) <{{alignment = {align} : i64}}> : (!llvm.ptr) -> i{width}',
            f"{name} = load i{width}, ptr {ptr}, align {align}",
        )
        # The load still runs, so the two tools must still agree on whether it
        # is undefined; its value only joins the result when it cannot be a
        # byte of an address.
        if not self.reads_address(ptr, width // 8):
            self.ints.append(Val(name, width))

    # -- bulk and casts --------------------------------------------------

    def gen_mem_intrinsic(self) -> None:
        if not self.ptrs:
            return
        length = self.rng.choice([0, 1, 4, 8, 16])
        dst = self.pick_target(length, 1)
        if dst is None:
            return
        n = self.const_int(64, length)
        if self.o.memset and self.maybe(0.5):
            byte = self.const_int(8, self.rng.getrandbits(8))
            self.p.decls.add("memset")
            self.p.emit(
                f'"llvm.intr.memset"({dst}, {byte}, {n}) <{{isVolatile = false}}> '
                f": (!llvm.ptr, i8, i64) -> ()",
                f"call void @llvm.memset.p0.i64(ptr {dst}, i8 {byte}, i64 {length}, i1 false)",
            )
            self.note_int_write(dst, length)
        else:
            src = self.pick_target(length, 1)
            if src is None:
                return
            self.p.decls.add("memcpy")
            self.p.emit(
                f'"llvm.intr.memcpy"({dst}, {src}, {n}) <{{isVolatile = false}}> '
                f": (!llvm.ptr, !llvm.ptr, i64) -> ()",
                f"call void @llvm.memcpy.p0.p0.i64(ptr {dst}, ptr {src}, i64 {length}, i1 false)",
            )
            self.note_copy(dst, src, length)

    def gen_ptr_arith(self) -> None:
        """Use addresses only in ways whose result does not depend on them.

        VeIR lays objects out itself, so a raw address means something
        different than it does to Alive2.  The difference between two
        addresses in the same object, and a round trip through an integer,
        mean the same under both.
        """
        src = self.any_ptr()
        if src is None:
            return
        delta = self.rng.randrange(0, 8)
        idx = self.const_int(64, delta)
        off = self.p.fresh()
        self.p.emit(
            f'{off} = "llvm.getelementptr"({src.name}, {idx}) <{{elem_type = i8, '
            f'rawConstantIndices = array<i32: -2147483648>}}> : (!llvm.ptr, i64) -> !llvm.ptr',
            f"{off} = getelementptr i8, ptr {src.name}, i64 {delta}",
        )
        a, b = self.p.fresh(), self.p.fresh()
        self.p.emit(f'{a} = "llvm.ptrtoint"({src.name}) : (!llvm.ptr) -> i64',
                    f"{a} = ptrtoint ptr {src.name} to i64")
        self.p.emit(f'{b} = "llvm.ptrtoint"({off}) : (!llvm.ptr) -> i64',
                    f"{b} = ptrtoint ptr {off} to i64")
        d = self.p.fresh()
        self.p.emit(f'{d} = "llvm.sub"({b}, {a}) : (i64, i64) -> i64',
                    f"{d} = sub i64 {b}, {a}")
        self.ints.append(Val(d, 64))
        if self.maybe(0.4):
            rt = self.p.fresh()
            self.p.emit(f'{rt} = "llvm.inttoptr"({a}) : (i64) -> !llvm.ptr',
                        f"{rt} = inttoptr i64 {a} to ptr")
            if self.o.access_inttoptr:
                self.ptrs.append(Ptr(rt, src.obj, src.offset))

    # -- result ----------------------------------------------------------

    def fold_result(self) -> str:
        acc = self.const_int(64, 0)
        for val in self.ints[: self.o.fold]:
            ext = val.name
            if val.width != 64:
                ext = self.p.fresh()
                self.p.emit(
                    f'{ext} = "llvm.zext"({val.name}) : (i{val.width}) -> i64',
                    f"{ext} = zext i{val.width} {val.name} to i64",
                )
            nxt = self.p.fresh()
            self.p.emit(f'{nxt} = "llvm.add"({acc}, {ext}) : (i64, i64) -> i64',
                        f"{nxt} = add i64 {acc}, {ext}")
            acc = nxt
        return acc

    # -- driver ----------------------------------------------------------

    def run(self) -> tuple[str, str]:
        weights = [
            (self.gen_alloca, self.o.w_alloca),
            (self.gen_malloc, self.o.w_malloc),
            (self.gen_free, self.o.w_free),
            (self.gen_gep, self.o.w_gep),
            (self.gen_store, self.o.w_store),
            (self.gen_load, self.o.w_load),
            (self.gen_mem_intrinsic, self.o.w_mem),
            (self.gen_ptr_arith, self.o.w_ptr),
        ]
        ops = [w[0] for w in weights]
        probs = [w[1] for w in weights]
        # Start with at least one object so the early ops have something to aim at.
        self.gen_alloca()
        for _ in range(self.o.ops):
            self.rng.choices(ops, probs)[0]()
        result = self.fold_result()
        return self.render(result)

    def render(self, result: str) -> tuple[str, str]:
        decl_mlir, decl_ll = [], []
        sigs = {
            "malloc": ('!llvm.func<ptr (i64)>', "declare ptr @malloc(i64)"),
            "calloc": ('!llvm.func<ptr (i64, i64)>', "declare ptr @calloc(i64, i64)"),
            "free": ('!llvm.func<void (ptr)>', "declare void @free(ptr)"),
        }
        for name in sorted(self.p.decls):
            if name in sigs:
                ty, ll = sigs[name]
                decl_mlir.append(
                    f'  "llvm.func"() <{{function_type = {ty}, '
                    f'linkage = #llvm.linkage<external>, sym_name = "{name}"}}> ({{\n  }}) : () -> ()'
                )
                decl_ll.append(ll)
        if "memset" in self.p.decls:
            decl_ll.append("declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)")
        if "memcpy" in self.p.decls:
            decl_ll.append("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)")

        body_mlir = "\n".join(self.p.mlir)
        mlir = (
            '"builtin.module"() ({\n'
            + ("\n".join(decl_mlir) + "\n" if decl_mlir else "")
            + '  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "main"}> ({\n'
            "    ^bb0():\n"
            f"{body_mlir}\n"
            f'      "llvm.return"({result}) : (i64) -> ()\n'
            "  }) : () -> ()\n"
            "}) : () -> ()\n"
        )
        body_ll = "\n".join(self.p.ll)
        ll = (
            ("\n".join(decl_ll) + "\n\n" if decl_ll else "")
            + "define i64 @main() {\nentry:\n"
            + f"{body_ll}\n"
            + f"  ret i64 {result}\n}}\n"
        )
        return mlir, ll


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--mlir", type=Path, help="write the MLIR form here")
    ap.add_argument("--ll", type=Path, help="write the LLVM IR form here")
    ap.add_argument("--ops", type=int, default=12, help="number of random operations (default: 12)")
    ap.add_argument("--fold", type=int, default=4,
                    help="how many loaded values feed the result (default: 4)")
    ap.add_argument("--oob", type=float, default=0.0,
                    help="probability a getelementptr leaves its object")
    ap.add_argument("--ub", type=float, default=0.0,
                    help="probability an access ignores what is in bounds")
    ap.add_argument("--defined", type=float, default=0.8,
                    help="probability a load prefers bytes already written (default: 0.8)")
    ap.add_argument("--misalign", type=float, default=0.0,
                    help="probability an access claims alignment 1")
    ap.add_argument("--null", type=float, default=0.0,
                    help="probability an access goes through null")
    # alive-exec resolves calloc to a block but does not zero it, so a load
    # from fresh calloc memory is poison there and zero in VeIR.  That is a
    # gap in the reference, not in the model, so calloc is off by default.
    ap.add_argument("--calloc", dest="calloc", action="store_true",
                    help="also generate calloc, which alive-exec does not zero")
    ap.add_argument("--ptr-values", action="store_true",
                    help="also store and load pointers")
    # alive-exec computes the right bytes for memset but leaves them marked
    # poison, so a load after one disagrees on definedness while agreeing on
    # the value.  That is a gap in the reference, so memset is off by default.
    ap.add_argument("--memset", action="store_true",
                    help="also generate memset, whose bytes alive-exec leaves poison")
    # A pointer that has been through an integer has no provenance in Alive2,
    # which resolves it against any block the address could belong to, while
    # VeIR resolves it against the one object whose range contains it.  The
    # round trip is still generated; only accesses through its result are
    # held back, since the two models answer that differently by design.
    ap.add_argument("--access-inttoptr", action="store_true",
                    help="also access memory through inttoptr results")
    ap.add_argument("--no-poison-pointers", dest="poison_pointers", action="store_false",
                    help="do not use pointers loaded from uninitialised memory, which are poison")
    # The weights and the probabilities above start at what the interpreter
    # models today and are raised as it grows, so a run with the defaults is
    # always one the interpreter is expected to survive.
    for name, default in (("alloca", 2), ("malloc", 0), ("free", 0), ("gep", 3),
                          ("store", 4), ("load", 4), ("mem", 0), ("ptr", 0)):
        ap.add_argument(f"--w-{name}", type=int, default=default,
                        help=f"relative weight of {name} operations (default: {default})")
    return ap


def generate(rng: random.Random, opts: argparse.Namespace) -> tuple[str, str]:
    return Generator(rng, opts).run()


def main(argv: list[str]) -> int:
    opts = build_parser().parse_args(argv)
    seed = opts.seed if opts.seed is not None else secrets.randbits(64)
    mlir, ll = generate(random.Random(seed), opts)
    if opts.mlir:
        opts.mlir.write_text(mlir)
    if opts.ll:
        opts.ll.write_text(ll)
    if not opts.mlir and not opts.ll:
        sys.stdout.write(mlir)
        sys.stdout.write("\n; ---- LLVM IR ----\n")
        sys.stdout.write(ll)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
