// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<i32 (f64)>, linkage = #llvm.linkage<external>, sym_name = "f1", visibility_ = 0 : i64}> ({
  ^bb0(%arg0: f64):
    "llvm.unreachable"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<fastcc>, frame_pointer = #llvm.framePointerKind<none>, function_type = !llvm.func<void (i32)>, linkage = #llvm.linkage<internal>, sym_name = "f2", visibility_ = 0 : i64}> ({
  ^bb0(%arg0: i32):
    "llvm.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, "frame_pointer" = #llvm.framePointerKind<all>, "function_type" = !llvm.func<i32 (f64)>, "linkage" = #llvm.linkage<external>, "sym_name" = "f1", "visibility_" = 0 : i64}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : f64):
// CHECK-NEXT:         "llvm.unreachable"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "llvm.func"() <{"CConv" = #llvm.cconv<fastcc>, "frame_pointer" = #llvm.framePointerKind<none>, "function_type" = !llvm.func<void (i32)>, "linkage" = #llvm.linkage<internal>, "sym_name" = "f2", "visibility_" = 0 : i64}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT:         "llvm.unreachable"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
