// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  // The index may have any integer width.
  "llvm.func"() <{function_type = !llvm.func<vector<4xi32> (vector<4xi32>, i32, i1, i8, i32, i64, i128)>, linkage = #llvm.linkage<external>, sym_name = "integer_indices"}> ({
  ^bb0(%v: vector<4xi32>, %x: i32, %i1: i1, %i8: i8, %i32: i32, %i64: i64, %i128: i128):
    %a = "llvm.insertelement"(%v, %x, %i1) : (vector<4xi32>, i32, i1) -> vector<4xi32>
    %b = "llvm.insertelement"(%a, %x, %i8) : (vector<4xi32>, i32, i8) -> vector<4xi32>
    %c = "llvm.insertelement"(%b, %x, %i32) : (vector<4xi32>, i32, i32) -> vector<4xi32>
    %d = "llvm.insertelement"(%c, %x, %i64) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %e = "llvm.insertelement"(%d, %x, %i128) : (vector<4xi32>, i32, i128) -> vector<4xi32>
    "llvm.return"(%e) : (vector<4xi32>) -> ()
  }) : () -> ()

  // Out-of-range indices produce poison, but are valid IR.
  "llvm.func"() <{function_type = !llvm.func<vector<4xi32> (vector<4xi32>, i32)>, linkage = #llvm.linkage<external>, sym_name = "out_of_range"}> ({
  ^bb0(%v: vector<4xi32>, %x: i32):
    %end = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %negative = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %a = "llvm.insertelement"(%v, %x, %end) : (vector<4xi32>, i32, i32) -> vector<4xi32>
    %b = "llvm.insertelement"(%a, %x, %negative) : (vector<4xi32>, i32, i32) -> vector<4xi32>
    "llvm.return"(%b) : (vector<4xi32>) -> ()
  }) : () -> ()

  "llvm.func"() <{function_type = !llvm.func<vector<1xi1> (i1, i64)>, linkage = #llvm.linkage<external>, sym_name = "single_lane"}> ({
  ^bb0(%x: i1, %i: i64):
    %v = "llvm.mlir.poison"() : () -> vector<1xi1>
    %r = "llvm.insertelement"(%v, %x, %i) : (vector<1xi1>, i1, i64) -> vector<1xi1>
    "llvm.return"(%r) : (vector<1xi1>) -> ()
  }) : () -> ()

  "llvm.func"() <{function_type = !llvm.func<vector<2x!llvm.ptr> (vector<2x!llvm.ptr>, !llvm.ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "pointers"}> ({
  ^bb0(%v: vector<2x!llvm.ptr>, %p: !llvm.ptr, %i: i64):
    %a = "llvm.insertelement"(%v, %p, %i) : (vector<2x!llvm.ptr>, !llvm.ptr, i64) -> vector<2x!llvm.ptr>
    "llvm.return"(%a) : (vector<2x!llvm.ptr>) -> ()
  }) : () -> ()

  "llvm.func"() <{function_type = !llvm.func<void (vector<2xbf16>, bf16, vector<4xf16>, f16, vector<2xf32>, f32, vector<2xf64>, f64, i32)>, linkage = #llvm.linkage<external>, sym_name = "floats"}> ({
  ^bb0(%a: vector<2xbf16>, %bf: bf16, %b: vector<4xf16>, %half: f16, %c: vector<2xf32>, %single: f32, %d: vector<2xf64>, %double: f64, %i: i32):
    %w = "llvm.insertelement"(%a, %bf, %i) : (vector<2xbf16>, bf16, i32) -> vector<2xbf16>
    %x = "llvm.insertelement"(%b, %half, %i) : (vector<4xf16>, f16, i32) -> vector<4xf16>
    %y = "llvm.insertelement"(%c, %single, %i) : (vector<2xf32>, f32, i32) -> vector<2xf32>
    %z = "llvm.insertelement"(%d, %double, %i) : (vector<2xf64>, f64, i32) -> vector<2xf64>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.insertelement"({{.*}}) : (vector<4xi32>, i32, i1) -> vector<4xi32>
// CHECK: "llvm.insertelement"({{.*}}) : (vector<4xi32>, i32, i8) -> vector<4xi32>
// CHECK: "llvm.insertelement"({{.*}}) : (vector<4xi32>, i32, i32) -> vector<4xi32>
// CHECK: "llvm.insertelement"({{.*}}) : (vector<4xi32>, i32, i64) -> vector<4xi32>
// CHECK: "llvm.insertelement"({{.*}}) : (vector<4xi32>, i32, i128) -> vector<4xi32>
// CHECK: "sym_name" = "out_of_range"
// CHECK: "llvm.insertelement"
// CHECK: "llvm.insertelement"
// CHECK: "llvm.insertelement"({{.*}}) : (vector<1xi1>, i1, i64) -> vector<1xi1>
// CHECK: "llvm.insertelement"({{.*}}) : (vector<2x!llvm.ptr>, !llvm.ptr, i64) -> vector<2x!llvm.ptr>
// CHECK: "llvm.insertelement"({{.*}}) : (vector<2xbf16>, bf16, i32) -> vector<2xbf16>
// CHECK: "llvm.insertelement"({{.*}}) : (vector<4xf16>, f16, i32) -> vector<4xf16>
// CHECK: "llvm.insertelement"({{.*}}) : (vector<2xf32>, f32, i32) -> vector<2xf32>
// CHECK: "llvm.insertelement"({{.*}}) : (vector<2xf64>, f64, i32) -> vector<2xf64>
