// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// A global whose name is not a bare identifier is spelled `@"..."` where it is
// referenced, but its `sym_name` carries the name without those quotes. The
// reference still has to resolve: clang names every string literal this way,
// so `@".str.1"` is the common case, not the exotic one.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, constant, global_type = !llvm.array<4 x i8>, linkage = #llvm.linkage<private>, sym_name = ".str.1", value = dense<[104, 105, 33, 0]> : tensor<4xi8>}> ({
  }) : () -> ()
  // A name carrying a byte MLIR will not print: clang's `\01` prefix, which
  // asks the backend not to mangle. `sym_name` holds it decoded, the reference
  // holds it escaped, and the two still have to meet.
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, linkage = #llvm.linkage<external>, sym_name = "\01_lstat"}> ({
    %z = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    "llvm.return"(%z) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<ptr ()>, linkage = #llvm.linkage<external>, sym_name = "greeting"}> ({
    %s = "llvm.mlir.addressof"() <{global_name = @".str.1"}> : () -> !llvm.ptr
    %f = "llvm.mlir.addressof"() <{global_name = @"\01_lstat"}> : () -> !llvm.ptr
    "llvm.return"(%s) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.mlir.addressof"() <{"global_name" = @".str.1"}> : () -> !llvm.ptr
// CHECK: "llvm.mlir.addressof"() <{"global_name" = @"\01_lstat"}> : () -> !llvm.ptr
