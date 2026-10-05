// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// An unresolved reference and its definition denote the same field type.
// Until references are resolved, skip equality checks that depend on them.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "recursive"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<"node", (ptr, struct<"node">)>
    %r = "llvm.extractvalue"(%u) <{position = array<i64: 1>}> : (!llvm.struct<"node", (ptr, struct<"node">)>) -> !llvm.struct<"node", (ptr, struct<"node">)>
    %s = "llvm.insertvalue"(%u, %r) <{position = array<i64: 1>}> : (!llvm.struct<"node", (ptr, struct<"node">)>, !llvm.struct<"node", (ptr, struct<"node">)>) -> !llvm.struct<"node", (ptr, struct<"node">)>
    // The unresolved reference can also occur inside the reached field type.
    %a = "llvm.mlir.undef"() : () -> !llvm.struct<"array_node", (array<1 x struct<"array_node">>)>
    %b = "llvm.extractvalue"(%a) <{position = array<i64: 0>}> : (!llvm.struct<"array_node", (array<1 x struct<"array_node">>)>) -> !llvm.array<1 x struct<"array_node", (array<1 x struct<"array_node">>)>>
    %c = "llvm.insertvalue"(%a, %b) <{position = array<i64: 0>}> : (!llvm.struct<"array_node", (array<1 x struct<"array_node">>)>, !llvm.array<1 x struct<"array_node", (array<1 x struct<"array_node">>)>>) -> !llvm.struct<"array_node", (array<1 x struct<"array_node">>)>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1>}>
// CHECK-NEXT: {{.*}}"llvm.insertvalue"({{.*}}) <{"position" = array<i64: 1>}>
// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}>
// CHECK-NEXT: {{.*}}"llvm.insertvalue"({{.*}}) <{"position" = array<i64: 0>}>
