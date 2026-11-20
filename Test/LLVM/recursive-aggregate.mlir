// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "recursive"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<"node", (ptr, struct<"node">)>
    %r = "llvm.extractvalue"(%u) <{position = array<i64: 1>}> : (!llvm.struct<"node", (ptr, struct<"node">)>) -> !llvm.struct<"node", (ptr, struct<"node">)>
    %s = "llvm.insertvalue"(%u, %r) <{position = array<i64: 1>}> : (!llvm.struct<"node", (ptr, struct<"node">)>, !llvm.struct<"node", (ptr, struct<"node">)>) -> !llvm.struct<"node", (ptr, struct<"node">)>
    // The unresolved reference can also occur inside the reached field type.
    %a = "llvm.mlir.undef"() : () -> !llvm.struct<"array_node", (array<1 x struct<"array_node">>)>
    %b = "llvm.extractvalue"(%a) <{position = array<i64: 0>}> : (!llvm.struct<"array_node", (array<1 x struct<"array_node">>)>) -> !llvm.array<1 x struct<"array_node", (array<1 x struct<"array_node">>)>>
    %c = "llvm.insertvalue"(%a, %b) <{position = array<i64: 0>}> : (!llvm.struct<"array_node", (array<1 x struct<"array_node">>)>, !llvm.array<1 x struct<"array_node", (array<1 x struct<"array_node">>)>>) -> !llvm.struct<"array_node", (array<1 x struct<"array_node">>)>
    // Known fields still match when their sibling is an unresolved reference.
    %d = "llvm.mlir.undef"() : () -> !llvm.struct<"wrapped_node", (struct<(i32, struct<"wrapped_node">)>)>
    %e = "llvm.extractvalue"(%d) <{position = array<i64: 0>}> : (!llvm.struct<"wrapped_node", (struct<(i32, struct<"wrapped_node">)>)>) -> !llvm.struct<(i32, struct<"wrapped_node", (struct<(i32, struct<"wrapped_node">)>)>)>
    %f = "llvm.insertvalue"(%d, %e) <{position = array<i64: 0>}> : (!llvm.struct<"wrapped_node", (struct<(i32, struct<"wrapped_node">)>)>, !llvm.struct<(i32, struct<"wrapped_node", (struct<(i32, struct<"wrapped_node">)>)>)>) -> !llvm.struct<"wrapped_node", (struct<(i32, struct<"wrapped_node">)>)>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1>}>
// CHECK-NEXT: {{.*}}"llvm.insertvalue"({{.*}}) <{"position" = array<i64: 1>}>
// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}>
// CHECK-NEXT: {{.*}}"llvm.insertvalue"({{.*}}) <{"position" = array<i64: 0>}>
// CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}>
// CHECK-NEXT: {{.*}}"llvm.insertvalue"({{.*}}) <{"position" = array<i64: 0>}>
