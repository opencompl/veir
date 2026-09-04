// RUN: veir-interpret %s | filecheck %s

// `llvm.mlir.constant` permits the value attribute's integer type to differ
// from the result type. MLIR reads the literal as an APInt of the *attribute's*
// width and then sign-extends it to the result width (signless attributes);
// see the `IntegerAttr` case of `getLLVMConstant` in
// mlir/lib/Target/LLVMIR/ModuleTranslation.cpp.
//
// Veir instead reinterprets the literal's mathematical value at the result
// width (`LLVM.Int.constant bw intAttr.value`), which agrees with MLIR only
// when the literal already lies in the signed range of its own declared type.
//
// Expected values below are what `mlir-translate --mlir-to-llvmir` produces:
//
//   llvm.mlir.constant(200 : i8) : i32           ->  i32 -56
//   llvm.mlir.constant(3 : i2) : i32             ->  i32 -1
//   llvm.mlir.constant(255 : i8) : i64           ->  i64 -1
//   llvm.mlir.constant(4294967295 : i32) : i64   ->  i64 -1
//   llvm.mlir.constant(-3 : i8) : i32            ->  i32 -3     (agrees today)
//   llvm.mlir.constant(127 : i8) : i32           ->  i32 127    (agrees today)
//   llvm.mlir.constant(-128 : i8) : i32          ->  i32 -128   (agrees today)

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i64, i64, i32, i32, i32)}> ({
    // Out of the signed range of the attribute's own type: must sign-extend.
    %a = "llvm.mlir.constant"() <{ "value" = 200 : i8 }> : () -> i32
    %b = "llvm.mlir.constant"() <{ "value" = 3 : i2 }> : () -> i32
    %c = "llvm.mlir.constant"() <{ "value" = 255 : i8 }> : () -> i64
    %d = "llvm.mlir.constant"() <{ "value" = 4294967295 : i32 }> : () -> i64
    // Inside the signed range of the attribute's own type: already correct.
    %e = "llvm.mlir.constant"() <{ "value" = -3 : i8 }> : () -> i32
    %f = "llvm.mlir.constant"() <{ "value" = 127 : i8 }> : () -> i32
    %g = "llvm.mlir.constant"() <{ "value" = -128 : i8 }> : () -> i32
    "func.return"(%a, %b, %c, %d, %e, %f, %g) : (i32, i32, i64, i64, i32, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffc8#32, 0xffffffff#32, 0xffffffffffffffff#64, 0xffffffffffffffff#64, 0xfffffffd#32, 0x0000007f#32, 0xffffff80#32]

// Reference lowering with upstream MLIR:
//
//   mlir-opt --convert-to-llvm --reconcile-unrealized-casts \
//     Test/Interpreter/LLVM/constant_attr_sext_to_wider_result.mlir \
//     | mlir-translate --mlir-to-llvmir
//
//   define { i32, i32, i64, i64, i32, i32, i32 } @main() {
//     ret { i32, i32, i64, i64, i32, i32, i32 } { i32 -56, i32 -1, i64 -1, i64 -1, i32 -3, i32 127, i32 -128 }
//   }
//
// `--convert-to-llvm` packs the multiple results into a struct, so the fields
// are the seven constants in order.  The first four are the divergences.
