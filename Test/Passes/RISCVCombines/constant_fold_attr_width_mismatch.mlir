// RUN: veir-opt %s -p=riscv-combine | filecheck %s
// RUN: %if mlir-min-22 %{ veir-opt %s -p=riscv-combine | mlir-opt --mlir-print-op-generic %}
// Constants are decoded at their attribute widths and truncated to their result
// widths before folding. Computed constants must also fit their attribute types.

"builtin.module"() ({
  // `300 : i32` in an i8 result is the value 44, so smin(44, 50) = 44.
  "func.func"() <{function_type = () -> i8, sym_name = "smin_narrowed"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 50 : i8}> : () -> i8
    %r = "llvm.intr.smin"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // `200 : i8` in an i32 result is the value -56, so smax(-56, 0) = 0.
  "func.func"() <{function_type = () -> i32, sym_name = "smax_widened"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 200 : i8}> : () -> i32
    %c2 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %r = "llvm.intr.smax"(%c1, %c2) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Decode before adding: 44 + 50 = 94.
  "func.func"() <{function_type = () -> i8, sym_name = "add_narrowed"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 50 : i8}> : () -> i8
    %r = "llvm.add"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // Negating the minimum signed integer wraps back to itself at i8.
  "func.func"() <{function_type = (i8) -> i8, sym_name = "sub_to_add_min"}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %r = "llvm.sub"(%x, %c) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @smin_narrowed() -> i8 {
// CHECK:         "llvm.mlir.constant"() <{"value" = 44 : i8}> : () -> i8

// CHECK-LABEL: func.func @smax_widened() -> i32 {
// CHECK:         "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32

// CHECK-LABEL: func.func @add_narrowed() -> i8 {
// CHECK:         "llvm.mlir.constant"() <{"value" = 94 : i8}> : () -> i8

// CHECK-LABEL: func.func @sub_to_add_min(%{{.*}}: i8) -> i8 {
// CHECK:         "llvm.mlir.constant"() <{"value" = -128 : i8}> : () -> i8

// Reference lowering of the *input* with upstream MLIR, which is what the
// folded output above has to agree with:
//
//   mlir-opt --convert-to-llvm --reconcile-unrealized-casts \
//     Test/Passes/RISCVCombines/constant_fold_attr_width_mismatch.mlir \
//     | mlir-translate --mlir-to-llvmir \
//     | opt -O1 -S
//
//   define noundef i8 @smin_narrowed() local_unnamed_addr #0 {
//     ret i8 44
//   }
//   define noundef i32 @smax_widened() local_unnamed_addr #0 {
//     ret i32 0
//   }
//   define noundef i8 @add_narrowed() local_unnamed_addr #0 {
//     ret i8 94
//   }
//   define i8 @sub_to_add_min(i8 %0) local_unnamed_addr #0 {
//     %2 = xor i8 %0, -128
//     ret i8 %2
//   }
//
// Without -O1 the last function is `sub i8 %0, -128`.
// LLVM canonicalizes `x - (-128)` to `xor x, -128` for i8, which is the same
// value as `x + (-128)`: the constant the pass should materialize is
// `-128 : i8`, not the out-of-range `128 : i8`.
