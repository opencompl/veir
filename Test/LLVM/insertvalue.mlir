// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = !llvm.array<2 x ptr>, linkage = #llvm.linkage<external>, sym_name = "table"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.array<2 x ptr>
    %p = "llvm.mlir.zero"() : () -> !llvm.ptr
    %a = "llvm.insertvalue"(%u, %p) <{position = array<i64: 0>}> : (!llvm.array<2 x ptr>, !llvm.ptr) -> !llvm.array<2 x ptr>
    %b = "llvm.insertvalue"(%a, %p) <{position = array<i64: 1>}> : (!llvm.array<2 x ptr>, !llvm.ptr) -> !llvm.array<2 x ptr>
    "llvm.return"(%b) : (!llvm.array<2 x ptr>) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "nested"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<(i32, !llvm.struct<(i64, i8)>)>
    %v = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %r = "llvm.insertvalue"(%u, %v) <{position = array<i64: 1, 0>}> : (!llvm.struct<(i32, !llvm.struct<(i64, i8)>)>, i64) -> !llvm.struct<(i32, !llvm.struct<(i64, i8)>)>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.insertvalue"({{.*}}) <{"position" = array<i64: 0>}> : (!llvm.array<2 x !llvm.ptr>, !llvm.ptr) -> !llvm.array<2 x !llvm.ptr>
// CHECK: "llvm.insertvalue"({{.*}}) <{"position" = array<i64: 1>}> : (!llvm.array<2 x !llvm.ptr>, !llvm.ptr) -> !llvm.array<2 x !llvm.ptr>
// CHECK: "llvm.insertvalue"({{.*}}) <{"position" = array<i64: 1, 0>}>
