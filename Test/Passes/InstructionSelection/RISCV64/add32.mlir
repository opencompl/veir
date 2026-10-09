// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i32, i32) -> (), sym_name = "bar"}> ({
    ^bb(%a: i32, %b: i32):
        %add = "llvm.add"(%a, %b) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.addw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        "test.test"(%add) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
