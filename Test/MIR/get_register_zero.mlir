// RUN: veir2mir %s | filecheck %s

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
