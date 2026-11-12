// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// RUN: LLUBI
// RUN: ALIVE_EXEC

// The result width of `llvm.intr.scmp` is independent of its operand width.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i2, i2, i2)}> ({
    %seven = "llvm.mlir.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %negseven = "llvm.mlir.constant"() <{ "value" = -7 : i8 }> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    // -7 <s 7 -> -1, all ones even in a wider result
    %a = "llvm.intr.scmp"(%negseven, %seven) : (i8, i8) -> i32
    // 7 == 7 -> 0
    %b = "llvm.intr.scmp"(%seven, %seven) : (i8, i8) -> i2
    // 7 >s -7 -> 1
    %c = "llvm.intr.scmp"(%seven, %negseven) : (i8, i8) -> i2
    // poison in -> poison out
    %d = "llvm.intr.scmp"(%poison, %seven) : (i8, i8) -> i2
    "func.return"(%a, %b, %c, %d) : (i32, i2, i2, i2) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffff#32, 0x0#2, 0x1#2, poison]
