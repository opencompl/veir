// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `llvm.mlir.addressof` names an `llvm.func` as readily as an
// `llvm.mlir.global`: taking the address of a function is how a function
// pointer, a callback argument or a vtable entry is spelled.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "callback"}> ({
  ^bb0(%x: i32):
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
  // A global holding the address of that function, and a function taking it.
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "handler"}> ({
    %f = "llvm.mlir.addressof"() <{global_name = @callback}> : () -> !llvm.ptr
    "llvm.return"(%f) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<ptr ()>, linkage = #llvm.linkage<external>, sym_name = "get_callback"}> ({
    %f = "llvm.mlir.addressof"() <{global_name = @callback}> : () -> !llvm.ptr
    "llvm.return"(%f) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.mlir.addressof"() <{"global_name" = @callback}> : () -> !llvm.ptr
// CHECK: "llvm.mlir.addressof"() <{"global_name" = @callback}> : () -> !llvm.ptr
