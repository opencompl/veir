// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "foo"}> ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.ld"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i64
        "func.return"() : () -> ()
    }) : () -> ()

    // i32 load lowers to `riscv.lw`
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "bar"}> ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i32
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.lw"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i32
        "func.return"() : () -> ()
    }) : () -> ()

    // i8 load lowers to `riscv.lb`.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "baz"}> ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i8
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.lb"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i8
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
