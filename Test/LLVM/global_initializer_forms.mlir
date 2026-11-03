// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// The three accepted ways to initialize an `llvm.mlir.global`: a `value`
// attribute, a body region ending in `llvm.return`, and neither (an external
// declaration, whose definition lives in another module). Only using a `value`
// and a body region together is rejected; see `global_value_and_region.mlir`.
// A `common` global is accepted as long as its initializer is zero.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "by_value", value = 41 : i32}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<internal>, sym_name = "by_region"}> ({
    %c = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "llvm.return"(%c) : (i32) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "declaration"}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<common>, sym_name = "common_zero", value = 0 : i32}> ({
  }) : () -> ()
}) : () -> ()

// CHECK:      "llvm.mlir.global"()
// CHECK-SAME:   "sym_name" = "by_value"
// CHECK-SAME:   "value" = 41 : i32
// CHECK:      "llvm.mlir.global"()
// CHECK-SAME:   "sym_name" = "by_region"
// CHECK:        %[[C:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK:        "llvm.return"(%[[C]]) : (i32) -> ()
// Attributes print in alphabetical order, so "value" would follow "sym_name":
// the CHECK-NOT has to come after it to actually cover that part of the line.
// CHECK:      "llvm.mlir.global"()
// CHECK-SAME:   "sym_name" = "declaration"
// CHECK-NOT:    "value"
// CHECK:      "llvm.mlir.global"()
// CHECK-SAME:   "linkage" = #llvm.linkage<common>
// CHECK-SAME:   "sym_name" = "common_zero"
// CHECK-SAME:   "value" = 0 : i32
