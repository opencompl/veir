// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, !llvm.byte<32>, !llvm.ptr) -> (), sym_name = "foo"}> ({
    ^bb0(%a : i64, %b : !llvm.byte<32>, %p : !llvm.ptr):
        %c = "llvm.bitcast"(%a) : (i64) -> !llvm.byte<64>
        // CHECK:           %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<64>
	%e = "llvm.bitcast"(%p) : (!llvm.ptr) -> !llvm.ptr
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr
	%f = "llvm.bitcast"(%b) : (!llvm.byte<32>) -> !llvm.byte<32>
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<32>) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<32>
	%g = "llvm.bitcast"(%f) : (!llvm.byte<32>) -> i32
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<32>) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32

	"test.test"(%c) : (!llvm.byte<64>) -> ()
	"test.test"(%e) : (!llvm.ptr) -> ()
	"test.test"(%g) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

