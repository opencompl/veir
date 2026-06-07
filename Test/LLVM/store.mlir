// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i64 (i64)>, linkage = #llvm.linkage<external>, sym_name = "store_load", visibility_ = 0 : i64}> ({
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 0 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%arg0, %1) <{access_groups = [], alias_scopes = [], alignment = 0 : i64, noalias_scopes = [], tbaa = []}> : (i64, !llvm.ptr) -> ()
    %2 = "llvm.load"(%1) <{access_groups = [], alias_scopes = [], alignment = 0 : i64, noalias_scopes = [], tbaa = []}> : (!llvm.ptr) -> i64
    "llvm.return"(%2) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, "function_type" = !llvm.func<i64 (i64)>, "linkage" = #llvm.linkage<external>, "sym_name" = "store_load", "visibility_" = 0 : i64}> ({
// CHECK-NEXT:       ^{{.*}}(%[[ARG:.*]] : i64):
// CHECK-NEXT:         %[[C1:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:         %[[PTR:.*]] = "llvm.alloca"(%[[C1]]) <{"alignment" = 0 : i64, "elem_type" = i64}> : (i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[ARG]], %[[PTR]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 0 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[LD:.*]] = "llvm.load"(%[[PTR]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 0 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:         "llvm.return"(%[[LD]]) : (i64) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
