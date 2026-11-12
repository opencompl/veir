// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=legalize-riscv64 | veir-interpret | filecheck %s

// The result width of `g_ucmp` is independent of its operand width.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i2, i2, i2)}> ({
    %seven = "llvm.mlir.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %negseven = "llvm.mlir.constant"() <{ "value" = -7 : i8 }> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    // 7 <u 249 -> -1 (where the signed comparison would give 1)
    %a = "gmir.g_ucmp"(%seven, %negseven) : (i8, i8) -> i32
    // 249 == 249 -> 0
    %b = "gmir.g_ucmp"(%negseven, %negseven) : (i8, i8) -> i2
    // 249 >u 7 -> 1
    %c = "gmir.g_ucmp"(%negseven, %seven) : (i8, i8) -> i2
    // poison in -> poison out
    %d = "gmir.g_ucmp"(%seven, %poison) : (i8, i8) -> i2
    "func.return"(%a, %b, %c, %d) : (i32, i2, i2, i2) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffff#32, 0x0#2, 0x1#2, poison]
