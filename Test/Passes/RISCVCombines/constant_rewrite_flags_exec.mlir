// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv-combine > %t
// RUN: veir-interpret %t | filecheck %s

// Block arguments keep the rewrites from being bypassed by constant folding.
// Each result is defined before rewriting: transferring overflow flags to the
// replacement operation must not turn it into poison.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i1, i1, i1, i8)}> ({
    %one8 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %min8 = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %one1 = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %zero1 = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    "cf.br"(%one8, %min8, %one1, %zero1) [^test] : (i8, i8, i1, i1) -> ()
  ^test(%x: i8, %min: i8, %a: i1, %b: i1):
    %unsigned = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i8
    %signed = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    // 1 * 255 does not overflow unsigned, but 0 - 1 does.
    %mulNuw = "llvm.mul"(%x, %unsigned) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %mulNsw = "llvm.mul"(%x, %signed) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %mulBoth = "llvm.mul"(%x, %signed) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8

    %true = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %inner = "llvm.sub"(%a, %b) : (i1, i1) -> i1
    // At i1, (1 - 0) - 1 is zero, but ~0 + 1 overflows both ways.
    %subNuw = "llvm.sub"(%inner, %true) <{overflowFlags = 2 : i32}> : (i1, i1) -> i1
    %subNsw = "llvm.sub"(%inner, %true) <{overflowFlags = 1 : i32}> : (i1, i1) -> i1
    %subBoth = "llvm.sub"(%inner, %true) <{overflowFlags = 3 : i32}> : (i1, i1) -> i1

    %one = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    // The inner subtraction may wrap: (-128 - 1) - 1 = 127 - 1 = 126.
    // Its replacement, -128 + ~1, overflows signed arithmetic.
    %wrapped = "llvm.sub"(%min, %x) : (i8, i8) -> i8
    %subWide = "llvm.sub"(%wrapped, %one) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%mulNuw, %mulNsw, %mulBoth, %subNuw, %subNsw, %subBoth, %subWide) : (i8, i8, i8, i1, i1, i1, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xff#8, 0xff#8, 0xff#8, 0x0#1, 0x0#1, 0x0#1, 0x7e#8]
