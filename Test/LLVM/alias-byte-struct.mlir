// RUN: VEIR_ROUNDTRIP
// RUN: %if mlir-min-23 %{ MLIR_ROUNDTRIP %}
//
// Checking a struct's fields must recognize LLVM byte types as compatible.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = !llvm.struct<(byte<8>)>, linkage = #llvm.linkage<external>, sym_name = "g"}> ({
  }) : () -> ()
  "llvm.mlir.alias"() <{alias_type = !llvm.struct<(byte<8>)>, linkage = #llvm.linkage<external>, sym_name = "a", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.mlir.alias"() <{"alias_type" = !llvm.struct<(!llvm.byte<8>)>
