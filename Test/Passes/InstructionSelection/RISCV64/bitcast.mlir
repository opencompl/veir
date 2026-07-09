// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, !llvm.byte<32>) -> ()}> ({
    ^bb0(%a : i64, %b : !llvm.byte<32>):
        %c = "llvm.bitcast"(%a) : (i64) -> !llvm.byte<64>
        // CHECK:           %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<64>
	%d = "llvm.bitcast"(%c) : (!llvm.byte<64>) -> !llvm.ptr
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<64>) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr
	%e = "llvm.bitcast"(%d) : (!llvm.ptr) -> !llvm.byte<64>
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<64>
	%f = "llvm.bitcast"(%b) : (!llvm.byte<32>) -> !llvm.byte<32>
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<32>) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<32>
	%g = "llvm.bitcast"(%f) : (!llvm.byte<32>) -> i32
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<32>) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32

        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

