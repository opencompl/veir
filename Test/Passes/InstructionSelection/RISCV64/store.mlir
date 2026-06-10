// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr) -> ()}> ({
    ^bb0(%a: !llvm.ptr, %b : i64):
        "llvm.store"(%b, %a) : (i64, !llvm.ptr) -> ()
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: "riscv.sd"({{.*}}, {{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    
}) : () -> ()
