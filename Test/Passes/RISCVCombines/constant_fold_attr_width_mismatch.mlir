// RUN: veir-opt %s -p=riscv-combine | filecheck %s
// RUN: %if mlir-min-22 %{ veir-opt %s -p=riscv-combine | mlir-opt --mlir-print-op-generic %}
// Expected to fail until `llvm.mlir.constant` handles the value attribute's
// integer width the way MLIR does; drop the XFAIL with the fix.
// XFAIL: *

// `matchConstantIntOp` (Veir/Passes/Matching/LLVM/Basic.lean) hands callers the
// raw `IntegerAttr.value`, and `constant_fold_binop_local`
// (Veir/Passes/RISCVCombines/Combine.lean) folds on those unbounded `Int`s.
// When the constant's attribute width differs from its result width, that value
// is not the operand's runtime value, and the folder disagrees with the
// interpreter.  Symmetrically, the folder writes results back with
// `IntegerAttr.mk result resultType` without reducing them to that type, so it
// can emit attributes MLIR rejects outright.
//
// The second RUN line asserts that mlir-opt accepts the pass output.

"builtin.module"() ({
  // `300 : i32` in an i8 result is the value 44, so smin(44, 50) = 44.
  // The folder reads `300` and picks 50.  Miscompile.
  "func.func"() <{function_type = () -> i8, sym_name = "smin_narrowed"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 50 : i8}> : () -> i8
    %r = "llvm.intr.smin"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // `200 : i8` in an i32 result is the value -56, so smax(-56, 0) = 0.
  // The folder reads `200` and picks 200.  Miscompile.
  "func.func"() <{function_type = () -> i32, sym_name = "smax_widened"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 200 : i8}> : () -> i32
    %c2 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %r = "llvm.intr.smax"(%c1, %c2) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // add is congruent mod 2^8, so the *value* survives: 44 + 50 = 94.  But the
  // folder materializes `350 : i8`, which mlir-opt rejects as out of range.
  "func.func"() <{function_type = () -> i8, sym_name = "add_narrowed"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 50 : i8}> : () -> i8
    %r = "llvm.add"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // sub_to_add negates the constant: -(-128) is 128, which is not an i8.  The
  // value is right modulo 2^8 but `128 : i8` is again rejected by mlir-opt.
  // Reachable without any width mismatch in the input.
  "func.func"() <{function_type = (i8) -> i8, sym_name = "sub_to_add_min"}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %r = "llvm.sub"(%x, %c) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "smin_narrowed"
// CHECK:         "llvm.mlir.constant"() <{"value" = 44 : i8}> : () -> i8

// CHECK-LABEL: "sym_name" = "smax_widened"
// CHECK:         "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32

// CHECK-LABEL: "sym_name" = "add_narrowed"
// CHECK:         "llvm.mlir.constant"() <{"value" = 94 : i8}> : () -> i8

// CHECK-LABEL: "sym_name" = "sub_to_add_min"
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
