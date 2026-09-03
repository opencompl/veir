// RUN: veir-interpret %s | filecheck %s

// MLIR special-cases width-1 (and unsigned) integer attributes: they are
// *zero*-extended to the result width, not sign-extended.  See
// `getLLVMConstant` in mlir/lib/Target/LLVMIR/ModuleTranslation.cpp:
//
//   if (intTy && (intTy.isUnsigned() || intTy.getWidth() == 1))
//     value = intAttr.getValue().zextOrTrunc(...);
//   else
//     value = intAttr.getValue().sextOrTrunc(...);
//
// `-1 : i1` is a legal MLIR attribute (mlir-opt normalizes it to `true`), so
// this is reachable from valid input IR.  Veir has no unsigned integer types --
// the parser rejects `ui8` -- so width 1 is the only case that needs zext.
//
// Expected values below are what `mlir-translate --mlir-to-llvmir` produces:
//
//   llvm.mlir.constant(-1 : i1) : i32  ->  i32 1
//   llvm.mlir.constant(-1 : i1) : i8   ->  i8 1
//   llvm.mlir.constant(1 : i1) : i32   ->  i32 1     (agrees today)
//   llvm.mlir.constant(true) : i32     ->  i32 1     (agrees today)
//   llvm.mlir.constant(false) : i32    ->  i32 0     (agrees today)
//   llvm.mlir.constant(-1 : i1) : i1   ->  i1 true   (agrees today)

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i8, i32, i32, i32, i1)}> ({
    // Zero-extended, not sign-extended.
    %a = "llvm.mlir.constant"() <{ "value" = -1 : i1 }> : () -> i32
    %b = "llvm.mlir.constant"() <{ "value" = -1 : i1 }> : () -> i8
    // Already correct.
    %c = "llvm.mlir.constant"() <{ "value" = 1 : i1 }> : () -> i32
    %d = "llvm.mlir.constant"() <{ "value" = true }> : () -> i32
    %e = "llvm.mlir.constant"() <{ "value" = false }> : () -> i32
    %f = "llvm.mlir.constant"() <{ "value" = -1 : i1 }> : () -> i1
    "func.return"(%a, %b, %c, %d, %e, %f) : (i32, i8, i32, i32, i32, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32, 0x01#8, 0x00000001#32, 0x00000001#32, 0x00000000#32, 0x1#1]

// Reference lowering with upstream MLIR:
//
//   mlir-opt --convert-to-llvm --reconcile-unrealized-casts \
//     Test/Interpreter/LLVM/constant_attr_i1_zext_to_wider_result.mlir \
//     | mlir-translate --mlir-to-llvmir
//
//   define { i32, i8, i32, i32, i32, i1 } @main() {
//     ret { i32, i8, i32, i32, i32, i1 } { i32 1, i8 1, i32 1, i32 1, i32 0, i1 true }
//   }
//
// The first two fields are the divergences: `-1 : i1` widened to i32 and to i8
// is 1 both times.  Note that mlir-opt has already normalized every `-1 : i1`
// to `true` in the llvm dialect, before any lowering runs -- the zext-vs-sext
// choice in `getLLVMConstant` never sees a negative value here.
