// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "foo"}> ({
    ^bb0(%a: !llvm.ptr, %b : i64):
        "llvm.store"(%b, %a) : (i64, !llvm.ptr) -> ()
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: "riscv.sd"({{.*}}, {{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // i32 store lowers to `riscv.sw`.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "bar"}> ({
    ^bb0(%a: !llvm.ptr, %b : i32):
        "llvm.store"(%b, %a) : (i32, !llvm.ptr) -> ()
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: "riscv.sw"({{.*}}, {{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // i8 store lowers to `riscv.sb`.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "baz"}> ({
    ^bb0(%a: !llvm.ptr, %b : i8):
        "llvm.store"(%b, %a) : (i8, !llvm.ptr) -> ()
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (i8) -> !riscv.reg
        // CHECK-NEXT: "riscv.sb"({{.*}}, {{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
