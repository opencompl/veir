// RUN: veir-opt %s -p=riscv | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "foo"}> ({
    ^bb0(%a: i64, %b: i64):
        %srem = "llvm.srem"(%a, %b) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.rem"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64

        "test.test"(%srem) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    "func.func"()  <{function_type = (i32, i32) -> (), sym_name = "bar"}> ({
    ^bb0(%a: i32, %b: i32):
        %srem32 = "llvm.srem"(%a, %b) : (i32, i32) -> i32
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: [[B:%.*]] = "riscv.sextw"([[A]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: [[C:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.sextw"([[C]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.rem"([[B]], [[D]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        "test.test"(%srem32) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
