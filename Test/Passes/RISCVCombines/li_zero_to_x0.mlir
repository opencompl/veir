// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// riscv-combine replaces the result of a `riscv.li 0` with a reference to the
// hard-wired zero register `x0` (`rv64.get_register`), dropping the
// materialization. This is valid because every consumer reads it as a source
// register, and `x0` reads as 0 in any source position -- including when it is
// forwarded as a generic `!riscv.reg` block argument.

"builtin.module"() ({
    "func.func"() <{function_type = (!riscv.reg) -> ()}> ({
    ^bb0(%x: !riscv.reg):
        %z = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
        %s = "riscv.slt"(%z, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "test.test"(%s) : (!riscv.reg) -> ()
        "riscv_cf.branch"(%z) [^bb1] : (!riscv.reg) -> ()
    ^bb1(%p: !riscv.reg):
        "func.return"() : () -> ()
    }) : () -> ()

    // A non-zero constant must be left untouched.
    "func.func"() <{function_type = (!riscv.reg) -> ()}> ({
    ^bb0(%x: !riscv.reg):
        %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
        %s = "riscv.slt"(%one, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "test.test"(%s) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

// The `li 0` is gone, replaced by a single x0 reference used everywhere.
// CHECK:      [[X0:%.*]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NOT:  "riscv.li"() <{"value" = 0
// CHECK:      "riscv.slt"([[X0]], %{{.*}}) : (!riscv.reg<x0>, !riscv.reg) -> !riscv.reg
// CHECK:      "riscv_cf.branch"([[X0]]) [^{{.*}}] : (!riscv.reg<x0>) -> ()

// The non-zero `li 1` survives unchanged.
// CHECK:      [[ONE:%.*]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
// CHECK:      "riscv.slt"([[ONE]], %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
