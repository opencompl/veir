// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// RUN: LLUBI
// RUN: ALIVE_EXEC

// The result width of `llvm.intr.scmp` is independent of its operand width.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i2, i2, i2, i8, i32, i8, i8, i2)}> ({
    %seven = "llvm.mlir.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %negseven = "llvm.mlir.constant"() <{ "value" = -7 : i8 }> : () -> i8
    %true = "llvm.mlir.constant"() <{ "value" = true }> : () -> i1
    %false = "llvm.mlir.constant"() <{ "value" = false }> : () -> i1
    %poison = "llvm.mlir.poison"() : () -> i8
    // -7 <s 7 -> -1
    %a = "llvm.intr.scmp"(%negseven, %seven) : (i8, i8) -> i2
    // 7 == 7 -> 0
    %b = "llvm.intr.scmp"(%seven, %seven) : (i8, i8) -> i2
    // 7 >s -7 -> 1
    %c = "llvm.intr.scmp"(%seven, %negseven) : (i8, i8) -> i2
    // a wider result: -1 is all ones
    %d = "llvm.intr.scmp"(%negseven, %seven) : (i8, i8) -> i8
    %e = "llvm.intr.scmp"(%seven, %negseven) : (i8, i8) -> i32
    // i1 operands: true is -1, so true <s false
    %f = "llvm.intr.scmp"(%true, %false) : (i1, i1) -> i8
    %g = "llvm.intr.scmp"(%false, %true) : (i1, i1) -> i8
    // poison in -> poison out
    %h = "llvm.intr.scmp"(%poison, %seven) : (i8, i8) -> i2
    "func.return"(%a, %b, %c, %d, %e, %f, %g, %h) : (i2, i2, i2, i8, i32, i8, i8, i2) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x3#2, 0x0#2, 0x1#2, 0xff#8, 0x00000001#32, 0xff#8, 0x01#8, poison]
