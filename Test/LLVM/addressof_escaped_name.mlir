// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// A symbol name holding a byte that has to be escaped. Both the name and the
// reference to it are reprinted from their bytes, so `\n` on input comes back
// as `\0A` -- the spelling `mlir-opt` writes, which is what lets this test
// compare the two.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "a\nb"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<ptr ()>, linkage = #llvm.linkage<external>, sym_name = "get"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @"a\nb"}> : () -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "sym_name" = "a\0Ab"
// CHECK: "llvm.mlir.addressof"() <{"global_name" = @"a\0Ab"}> : () -> !llvm.ptr
