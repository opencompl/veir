// RUN: veir-interpret %s | filecheck %s --check-prefix=RESULT
// RUN: veir-opt %s --print-op-generic -p=riscv-combine > %t
// RUN: veir-interpret %t | filecheck %s --check-prefix=RESULT
// RUN: filecheck %s --check-prefix=FLAGS --input-file=%t

// 1 * 255 is defined unsigned, but 0 - 1 underflows. Multiplication by all-ones
// can become negation only if nuw is dropped. Signed negation preserves nsw.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    "cf.br"(%one) [^test] : (i8) -> ()
  ^test(%x: i8):
    %unsigned = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i8
    %signed = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %a = "llvm.mul"(%x, %unsigned) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %b = "llvm.mul"(%x, %signed) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %c = "llvm.mul"(%x, %signed) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %d = "llvm.mul"(%x, %signed) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%a, %b, %c, %d) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// RESULT: Program output: #[0xff#8, 0xff#8, 0xff#8, 0xff#8]
// FLAGS: "llvm.sub"({{.*}}) <{"overflowFlags" = 1 : i32}>
// FLAGS: "llvm.sub"({{.*}}) <{"overflowFlags" = 1 : i32}>
