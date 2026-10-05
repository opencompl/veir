// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i16, i32, !llvm.byte<32>) -> (), sym_name = "foo"}> ({
    ^bb0(%b : i16, %c: i32, %d: !llvm.byte<32>):
        %truncb = "llvm.trunc"(%b) : (i16) -> i8
        %truncc = "llvm.trunc"(%c) : (i32) -> i16
	%truncd = "llvm.trunc"(%d) : (!llvm.byte<32>) -> !llvm.byte<16>
        
        // CHECK:           func.func @foo([[B:.*]]: i16, [[C:.*]]: i32, [[D:.*]]: !llvm.byte<32>) {
        // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
        // CHECK-NEXT:      %[[I:.*]] = "builtin.unrealized_conversion_cast"(%[[H]]) : (!riscv.reg) -> i8
        // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:      %[[L:.*]] = "builtin.unrealized_conversion_cast"(%[[K]]) : (!riscv.reg) -> i16
        // CHECK-NEXT:      %[[N:.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!llvm.byte<32>) -> !riscv.reg
        // CHECK-NEXT:      %[[O:.*]] = "builtin.unrealized_conversion_cast"(%[[N]]) : (!riscv.reg) -> !llvm.byte<16>
        
        "test.test"(%truncb) : (i8) -> ()
        "test.test"(%truncc) : (i16) -> ()
	"test.test"(%truncd) : (!llvm.byte<16>) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // Every pair of widths up to 64 is lowered, including `i1` and non-power-of-two widths.
    "func.func"()  <{function_type = (i64, i52, i65) -> (), sym_name = "odd"}> ({
    ^bb0(%e : i64, %f: i52, %g: i65):
        %trunce = "llvm.trunc"(%e) : (i64) -> i1
        %truncf = "llvm.trunc"(%f) : (i52) -> i3
        %truncg = "llvm.trunc"(%g) : (i65) -> i1

        // CHECK:           func.func @odd([[E:.*]]: i64, [[F:.*]]: i52, [[G:.*]]: i65) {
        // CHECK-NEXT:      %[[P:.*]] = "builtin.unrealized_conversion_cast"([[E]]) : (i64) -> !riscv.reg
        // CHECK-NEXT:      %[[Q:.*]] = "builtin.unrealized_conversion_cast"(%[[P]]) : (!riscv.reg) -> i1
        // CHECK-NEXT:      %[[R:.*]] = "builtin.unrealized_conversion_cast"([[F]]) : (i52) -> !riscv.reg
        // CHECK-NEXT:      %[[S:.*]] = "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i3
        // An operand wider than a register is not lowered.
        // CHECK-NEXT:      %{{.*}} = "llvm.trunc"([[G]]) : (i65) -> i1

        "test.test"(%trunce) : (i1) -> ()
        "test.test"(%truncf) : (i3) -> ()
        "test.test"(%truncg) : (i1) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
