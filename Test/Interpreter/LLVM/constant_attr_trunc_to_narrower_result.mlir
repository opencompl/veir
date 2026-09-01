// RUN: veir-interpret %s | filecheck %s

// The narrowing direction already matches MLIR: truncation to the result width
// is the same whether it happens before or after the value is reduced to the
// attribute's own width.  These cases pass today and exist to guard against a
// fix for the widening cases (see constant_attr_sext_to_wider_result.mlir)
// that over-corrects.
//
// Expected values below are what `mlir-translate --mlir-to-llvmir` produces:
//
//   llvm.mlir.constant(300 : i32) : i8          ->  i8 44
//   llvm.mlir.constant(-1 : i32) : i8           ->  i8 -1
//   llvm.mlir.constant(4294967295 : i32) : i8   ->  i8 -1
//   llvm.mlir.constant(200 : i8) : i4           ->  i4 -8
//   llvm.mlir.constant(300 : i32) : i32         ->  i32 300

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i4, i32)}> ({
    %a = "llvm.mlir.constant"() <{ "value" = 300 : i32 }> : () -> i8
    %b = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i8
    %c = "llvm.mlir.constant"() <{ "value" = 4294967295 : i32 }> : () -> i8
    %d = "llvm.mlir.constant"() <{ "value" = 200 : i8 }> : () -> i4
    // Same width: the attribute type and the result type agree.
    %e = "llvm.mlir.constant"() <{ "value" = 300 : i32 }> : () -> i32
    "func.return"(%a, %b, %c, %d, %e) : (i8, i8, i8, i4, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x2c#8, 0xff#8, 0xff#8, 0x8#4, 0x0000012c#32]

// Reference lowering with upstream MLIR:
//
//   mlir-opt --convert-to-llvm --reconcile-unrealized-casts \
//     Test/Interpreter/LLVM/constant_attr_trunc_to_narrower_result.mlir \
//     | mlir-translate --mlir-to-llvmir
//
//   define { i8, i8, i8, i4, i32 } @main() {
//     ret { i8, i8, i8, i4, i32 } { i8 44, i8 -1, i8 -1, i4 -8, i32 300 }
//   }
