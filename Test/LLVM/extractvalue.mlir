// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<!llvm.ptr (!llvm.array<2 x ptr>)>, linkage = #llvm.linkage<external>, sym_name = "second"}> ({
  ^bb0(%t: !llvm.array<2 x ptr>):
    %a = "llvm.extractvalue"(%t) <{position = array<i64: 0>}> : (!llvm.array<2 x ptr>) -> !llvm.ptr
    %b = "llvm.extractvalue"(%t) <{position = array<i64: 1>}> : (!llvm.array<2 x ptr>) -> !llvm.ptr
    "llvm.return"(%b) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "nested"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<(i32, !llvm.struct<(i64, i8)>)>
    %r = "llvm.extractvalue"(%u) <{position = array<i64: 1, 0>}> : (!llvm.struct<(i32, !llvm.struct<(i64, i8)>)>) -> i64
    %w = "llvm.extractvalue"(%u) <{position = array<i64>}> : (!llvm.struct<(i32, !llvm.struct<(i64, i8)>)>) -> !llvm.struct<(i32, !llvm.struct<(i64, i8)>)>
    %s = "llvm.mlir.undef"() : () -> !llvm.array<2 x !llvm.struct<(i64, i8)>>
    %t = "llvm.extractvalue"(%s) <{position = array<i64: 1, 0>}> : (!llvm.array<2 x !llvm.struct<(i64, i8)>>) -> i64
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}> : (!llvm.array<2 x !llvm.ptr>) -> !llvm.ptr
// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1>}> : (!llvm.array<2 x !llvm.ptr>) -> !llvm.ptr
// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1, 0>}> : (!llvm.struct<(i32, {{(!llvm.)?}}struct<(i64, i8)>)>) -> i64
// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64>}> : (!llvm.struct<(i32, {{(!llvm.)?}}struct<(i64, i8)>)>) -> !llvm.struct<(i32, {{(!llvm.)?}}struct<(i64, i8)>)>
// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1, 0>}> : (!llvm.array<2 x {{(!llvm.)?}}struct<(i64, i8)>>) -> i64
