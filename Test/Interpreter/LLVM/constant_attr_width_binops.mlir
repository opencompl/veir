// RUN: veir-interpret %s | filecheck %s
// Expected to fail until `llvm.mlir.constant` handles the value attribute's
// integer width the way MLIR does; drop the XFAIL with the fix.
// XFAIL: *

// The semantics that Test/Passes/RISCVCombines/constant_fold_attr_width_mismatch.mlir
// requires the constant folder to agree with.  Each result is the same
// computation that test folds at compile time:
//
//   smin(llvm.mlir.constant(300 : i32) : i8, 50 : i8)   ->  smin(44, 50)   = 44
//   smax(llvm.mlir.constant(200 : i8) : i32, 0 : i32)   ->  smax(-56, 0)   = 0
//   add (llvm.mlir.constant(300 : i32) : i8, 50 : i8)   ->  add(44, 50)    = 94
//   sub (%x, llvm.mlir.constant(-128 : i8) : i8) with %x = 0                = -128

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i32, i8, i8)}> ({
    %c300 = "llvm.mlir.constant"() <{ "value" = 300 : i32 }> : () -> i8
    %c50 = "llvm.mlir.constant"() <{ "value" = 50 : i8 }> : () -> i8
    %c200 = "llvm.mlir.constant"() <{ "value" = 200 : i8 }> : () -> i32
    %c0 = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %cmin = "llvm.mlir.constant"() <{ "value" = -128 : i8 }> : () -> i8
    %zero8 = "llvm.mlir.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %a = "llvm.intr.smin"(%c300, %c50) : (i8, i8) -> i8
    %b = "llvm.intr.smax"(%c200, %c0) : (i32, i32) -> i32
    %c = "llvm.add"(%c300, %c50) : (i8, i8) -> i8
    %d = "llvm.sub"(%zero8, %cmin) : (i8, i8) -> i8
    "func.return"(%a, %b, %c, %d) : (i8, i32, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x2c#8, 0x00000000#32, 0x5e#8, 0x80#8]

// Reference lowering with upstream MLIR:
//
//   mlir-opt --convert-to-llvm --reconcile-unrealized-casts \
//     Test/Interpreter/LLVM/constant_attr_width_binops.mlir \
//     | mlir-translate --mlir-to-llvmir
//
//   define { i8, i32, i8, i8 } @main() {
//     %1 = call i8 @llvm.smin.i8(i8 44, i8 50)
//     %2 = call i32 @llvm.smax.i32(i32 -56, i32 0)
//     %3 = insertvalue { i8, i32, i8, i8 } poison, i8 %1, 0
//     %4 = insertvalue { i8, i32, i8, i8 } %3, i32 %2, 1
//     %5 = insertvalue { i8, i32, i8, i8 } %4, i8 94, 2
//     %6 = insertvalue { i8, i32, i8, i8 } %5, i8 -128, 3
//     ret { i8, i32, i8, i8 } %6
//   }
//
// The intrinsic operands show the constants' real values: 44 (not 300) and
// -56 (not 200).  Piping that through `opt -O1 -S` folds them:
//
//   define { i8, i32, i8, i8 } @main() local_unnamed_addr #0 {
//     ret { i8, i32, i8, i8 } { i8 44, i32 0, i8 94, i8 -128 }
//   }
