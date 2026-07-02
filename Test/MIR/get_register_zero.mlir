// RUN: veir2mir %s | filecheck %s

// `rv64.get_register` referencing the hard-wired zero register `x0` (produced by
// the `li 0 -> x0` riscv-combine) lowers to a `COPY $x0` into a virtual register,
// rather than an unhandled op. The copy makes the value usable both as a direct
// operand and (elsewhere) as a PHI operand, and the register allocator coalesces
// it into a direct `zero` reference in the final assembly.

"builtin.module"() ({
  ^0():
    "llvm.func"() <{"function_type" = !llvm.func<i64 ()>, "sym_name" = "main"}> ({
      ^1():
        %v = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
        %z = "rv64.get_register"() : () -> !riscv.reg<x0>
        %c = "riscv.sltu"(%z, %v) : (!riscv.reg<x0>, !riscv.reg) -> !riscv.reg
        %r = "builtin.unrealized_conversion_cast"(%c) : (!riscv.reg) -> i64
        "llvm.return"(%r) : (i64) -> ()
    }) : () -> ()
}) : () -> ()

// The get_register becomes a COPY of the physical zero register...
// CHECK: [[Z:%v[0-9]+]]:gpr = COPY $x0
// ... and the consumer references that copy.
// CHECK: SLTU [[Z]], %{{.*}}
// CHECK-NOT: UNHANDLED
