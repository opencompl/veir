// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=isel-riscv64 > %t
// RUN: veir-interpret %t | filecheck %s

// Decode at the attribute width before truncating to the result width.
// Integer attributes sign-extend, except that i1 attributes zero-extend.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i8, i1)}> ({
    %signed = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i64
    %boolean = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    %signed32 = "llvm.mlir.constant"() <{value = 4294967295 : i32}> : () -> i64
    %narrowed = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    %true = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    "func.return"(%signed, %boolean, %signed32, %narrowed, %true) : (i64, i64, i64, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffffff#64, 0x0000000000000001#64, 0xffffffffffffffff#64, 0x2c#8, 0x1#1]
