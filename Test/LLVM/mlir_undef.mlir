// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `llvm.mlir.undef` produces a value of any LLVM type with no operands and no
// attributes, exactly as `llvm.mlir.poison` does. clang reaches for it when a
// global is only partly initialized, which is why every use of it in the
// sqlite3 corpus is a struct inside an `llvm.mlir.global` body.

"builtin.module"() ({
  // A partly initialized global: the aggregate starts undefined and is filled
  // in by `insertvalue` in the general case.
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = !llvm.struct<(i16, i8)>, linkage = #llvm.linkage<external>, sym_name = "partly"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<(i16, i8)>
    "llvm.return"(%u) : (!llvm.struct<(i16, i8)>) -> ()
  }) : () -> ()
  // The scalar and pointer forms, for contrast with the aggregate one.
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, linkage = #llvm.linkage<external>, sym_name = "scalar"}> ({
    %x = "llvm.mlir.undef"() : () -> i32
    %p = "llvm.mlir.undef"() : () -> !llvm.ptr
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.mlir.undef"() : () -> !llvm.struct<(i16, i8)>
// CHECK: "llvm.mlir.undef"() : () -> i32
// CHECK: "llvm.mlir.undef"() : () -> !llvm.ptr
