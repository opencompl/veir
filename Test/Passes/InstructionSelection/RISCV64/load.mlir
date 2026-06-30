// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr) -> ()}> ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.ld"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i64
        "func.return"() : () -> ()
    }) : () -> ()
    "func.func"()  <{function_type = (!llvm.ptr) -> ()}> ({
    ^bb0(%a: !llvm.ptr):
        %val32 = "llvm.load"(%a) : (!llvm.ptr) -> i32
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.lw"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i32
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
