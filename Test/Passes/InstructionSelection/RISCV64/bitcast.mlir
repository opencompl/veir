// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, !llvm.byte<32>) -> (), sym_name = "foo"}> ({
    ^bb0(%a : i64, %b : !llvm.byte<32>):
        %c = "llvm.bitcast"(%a) : (i64) -> !llvm.byte<64>
        // CHECK:           %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<64>
	// Going between an integer and a pointer is `llvm.inttoptr` and `llvm.ptrtoint`, which this
	// pass does not lower: a register holds an address, so a pointer that survives one would
	// come back having lost the object it points into.
	%c64 = "llvm.bitcast"(%c) : (!llvm.byte<64>) -> i64
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<64>) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
	%d = "llvm.inttoptr"(%c64) : (i64) -> !llvm.ptr
        // CHECK-NEXT:      %{{.*}} = "llvm.inttoptr"(%{{.*}}) : (i64) -> !llvm.ptr
	%e64 = "llvm.ptrtoint"(%d) : (!llvm.ptr) -> i64
        // CHECK-NEXT:      %{{.*}} = "llvm.ptrtoint"(%{{.*}}) : (!llvm.ptr) -> i64
	%e = "llvm.bitcast"(%e64) : (i64) -> !llvm.byte<64>
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<64>
	%f = "llvm.bitcast"(%b) : (!llvm.byte<32>) -> !llvm.byte<32>
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<32>) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.byte<32>
	%g = "llvm.bitcast"(%f) : (!llvm.byte<32>) -> i32
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<32>) -> !riscv.reg
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32

	"test.test"(%e) : (!llvm.byte<64>) -> ()
	"test.test"(%g) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

