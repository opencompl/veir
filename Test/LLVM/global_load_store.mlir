// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", unnamed_addr = 0 : i64, value = 41 : i32, visibility_ = 0 : i64}> ({
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i32 ()>, linkage = #llvm.linkage<external>, sym_name = "main", visibility_ = 0 : i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %global = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %old = "llvm.load"(%global) : (!llvm.ptr) -> i32
    %new = "llvm.add"(%old, %one) : (i32, i32) -> i32
    "llvm.store"(%new, %global) : (i32, !llvm.ptr) -> ()
    "llvm.return"(%new) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "llvm.mlir.global"()
// CHECK-SAME:   "global_type" = i32
// CHECK-SAME:   "sym_name" = "g"
// CHECK-SAME:   "value" = 41 : i32
// CHECK:      %[[GLOBAL:.*]] = "llvm.mlir.addressof"()
// CHECK-SAME:   "global_name" = @g
// CHECK:      %[[OLD:.*]] = "llvm.load"(%[[GLOBAL]]) {{.*}}: (!llvm.ptr) -> i32
// CHECK:      %[[NEW:.*]] = "llvm.add"(%[[OLD]], %{{.*}}) : (i32, i32) -> i32
// CHECK:      "llvm.store"(%[[NEW]], %[[GLOBAL]]) {{.*}}: (i32, !llvm.ptr) -> ()
// CHECK:      "llvm.return"(%[[NEW]]) : (i32) -> ()
