// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.byte<64>, !llvm.byte<64>) -> ()}> ({
    ^bb0(%a: !llvm.byte<64>, %b: i64):
        %shl = "llvm.shl"(%a, %b) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<64>) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sll"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<64>
        %shl_nsw = "llvm.shl"(%a, %b) <{"overflowFlags" = 1 : i32}> : (!llvm.byte<64>, i64) -> !llvm.byte<64>
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<64>) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sll"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<64>
        %shl_nuw = "llvm.shl"(%a, %b) <{"overflowFlags" = 2 : i32}> : (!llvm.byte<64>, i64) -> !llvm.byte<64>
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<64>) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sll"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<64>
        %shl_nuw_nsw = "llvm.shl"(%a, %b) <{"overflowFlags" = 3 : i32}> : (!llvm.byte<64>, i64) -> !llvm.byte<64>
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<64>) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sll"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<64>
        "test.test"(%shl) : (!llvm.byte<64>) -> ()
        "test.test"(%shl_nsw) : (!llvm.byte<64>) -> ()
        "test.test"(%shl_nuw) : (!llvm.byte<64>) -> ()
        "test.test"(%shl_nuw_nsw) : (!llvm.byte<64>) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    "func.func"()  <{function_type = (!llvm.byte<32>, i32) -> ()}> ({
    ^bb(%a: !llvm.byte<32>, %b: i32):
        %shl = "llvm.shl"(%a, %b) : (!llvm.byte<32>, i32) -> !llvm.byte<32>
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<32>) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sllw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<32>
        "test.test"(%shl) : (!llvm.byte<32>) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
