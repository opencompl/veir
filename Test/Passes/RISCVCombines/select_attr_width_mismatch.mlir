// RUN: veir-opt %s -p=riscv-combine | filecheck %s
// RUN: %if mlir-min-22 %{ veir-opt %s -p=riscv-combine | mlir-opt --mlir-print-op-generic %}

// The select rewrites recognize `-1` (all ones) by comparing the matched
// constant's value.  `-1 : i1` in a wider result is the value 1, not all ones
// -- MLIR zero-extends a width-1 attribute -- so `select c, (-1 : i1), 0` is
// `zext c`, not `sext c`.  Reading the raw attribute instead of its value at the
// result type turns each of these into a miscompile.
//
// Reference lowering with upstream MLIR:
//
//   mlir-opt --convert-to-llvm --reconcile-unrealized-casts %s \
//     | mlir-translate --mlir-to-llvmir
//
//   define i32 @select_i1_neg1_zero(i1 %0) { ret select i1 %0, i32 1, i32 0 }
//   define i32 @select_zero_i1_neg1(i1 %0) { ret select i1 %0, i32 0, i32 1 }
//   define i32 @mul_i1_neg1(i32 %0)        { ret mul i32 %0, 1 }
//   define i32 @select_i8_neg1_zero(i1 %0) { ret select i1 %0, i32 -1, i32 0 }
//
// (bodies elided to one line each).

"builtin.module"() ({
  // select c, 1, 0  ->  zext c   (NOT sext c)
  "func.func"() <{sym_name = "select_i1_neg1_zero", function_type = (i1) -> i32}> ({
  ^bb0(%c: i1):
    %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i1 }> : () -> i32
    %z  = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %r  = "llvm.select"(%c, %m1, %z) : (i1, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // select c, 0, 1  ->  zext (not c)   (NOT sext (not c))
  "func.func"() <{sym_name = "select_zero_i1_neg1", function_type = (i1) -> i32}> ({
  ^bb0(%c: i1):
    %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i1 }> : () -> i32
    %z  = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %r  = "llvm.select"(%c, %z, %m1) : (i1, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // mul x, 1  ->  x   (NOT 0 - x)
  "func.func"() <{sym_name = "mul_i1_neg1", function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i1 }> : () -> i32
    %r  = "llvm.mul"(%x, %m1) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Same shape, but `-1 : i8` really is all ones at i32: sext still applies.
  "func.func"() <{sym_name = "select_i8_neg1_zero", function_type = (i1) -> i32}> ({
  ^bb0(%c: i1):
    %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i8 }> : () -> i32
    %z  = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %r  = "llvm.select"(%c, %m1, %z) : (i1, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "select_i1_neg1_zero"
// CHECK:         %[[Z:.*]] = "llvm.zext"(%{{.*}}) : (i1) -> i32
// CHECK-NEXT:    "func.return"(%[[Z]])

// CHECK-LABEL: "sym_name" = "select_zero_i1_neg1"
// CHECK:         "llvm.xor"
// CHECK:         %[[Z:.*]] = "llvm.zext"(%{{.*}}) : (i1) -> i32
// CHECK-NEXT:    "func.return"(%[[Z]])

// CHECK-LABEL: "sym_name" = "mul_i1_neg1"
// CHECK:         ^{{.*}}(%[[X:.*]] : i32):
// CHECK-NEXT:    "func.return"(%[[X]])

// CHECK-LABEL: "sym_name" = "select_i8_neg1_zero"
// CHECK:         %[[S:.*]] = "llvm.sext"(%{{.*}}) : (i1) -> i32
// CHECK-NEXT:    "func.return"(%[[S]])
