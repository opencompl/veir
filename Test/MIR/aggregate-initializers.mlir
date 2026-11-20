// RUN: veir-opt %s -p=riscv > %t
// RUN: veir2mir %t | filecheck %s

"builtin.module"() ({
  "llvm.mlir.global"() <{global_type = !llvm.struct<"Outer", (i64, !llvm.struct<packed (i16, !llvm.ptr)>, !llvm.array<2 x i32>)>, linkage = #llvm.linkage<external>, sym_name = "zero_struct", alignment = 8 : i64}> ({
    %zero = "llvm.mlir.zero"() : () -> !llvm.struct<"Outer", (i64, !llvm.struct<packed (i16, !llvm.ptr)>, !llvm.array<2 x i32>)>
    "llvm.return"(%zero) : (!llvm.struct<"Outer", (i64, !llvm.struct<packed (i16, !llvm.ptr)>, !llvm.array<2 x i32>)>) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<2 x !llvm.struct<(i8, i64)>>, linkage = #llvm.linkage<internal>, sym_name = "zero_array", alignment = 8 : i64}> ({
    %zero = "llvm.mlir.zero"() : () -> !llvm.array<2 x !llvm.struct<(i8, i64)>>
    "llvm.return"(%zero) : (!llvm.array<2 x !llvm.struct<(i8, i64)>>) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<3 x i16>, linkage = #llvm.linkage<external>, sym_name = "integers", alignment = 2 : i64, value = dense<[16863, -12805, 8118]> : tensor<3xi16>}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<2 x !llvm.array<2 x i32>>, linkage = #llvm.linkage<internal>, constant, sym_name = "matrix", value = dense<[[1, -2], [3, 4]]> : tensor<2x2xi32>}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<2 x i64>, linkage = #llvm.linkage<external>, sym_name = "wide", value = dense<[18446744073709551615, -9223372036854775808]> : tensor<2xi64>}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<3 x i16>, linkage = #llvm.linkage<external>, sym_name = "splat", value = dense<-7> : tensor<3xi16>}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<2 x !llvm.array<2 x i32>>, linkage = #llvm.linkage<external>, sym_name = "zeros", value = dense<0> : tensor<2x2xi32>}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<0 x i32>, linkage = #llvm.linkage<external>, sym_name = "empty", value = dense<> : tensor<0xi32>}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<2 x i1>, linkage = #llvm.linkage<external>, sym_name = "bits", value = dense<[true, false]> : tensor<2xi1>}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<3 x i16>, linkage = #llvm.linkage<external>, sym_name = "raw", value = dense<"0xFFFF00803412"> : tensor<3xi16>}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<2 x i16>, linkage = #llvm.linkage<external>, sym_name = "raw_splat", value = dense<"0x3412"> : tensor<2xi16>}> ({}) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i16 ()>, sym_name = "read_integer"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @integers}> : () -> !llvm.ptr
    %v = "llvm.load"(%p) : (!llvm.ptr) -> i16
    "llvm.return"(%v) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      @zero_struct = global { i64, <{ i16, ptr }>, [2 x i32] } zeroinitializer, align 8
// CHECK-NEXT: @zero_array = internal global [2 x { i8, i64 }] zeroinitializer, align 8
// CHECK-NEXT: @integers = global [3 x i16] [i16 16863, i16 -12805, i16 8118], align 2
// CHECK-NEXT: @matrix = internal constant [2 x [2 x i32]] [[2 x i32] [i32 1, i32 -2], [2 x i32] [i32 3, i32 4]]
// CHECK-NEXT: @wide = global [2 x i64] [i64 18446744073709551615, i64 -9223372036854775808]
// CHECK-NEXT: @splat = global [3 x i16] [i16 -7, i16 -7, i16 -7]
// CHECK-NEXT: @zeros = global [2 x [2 x i32]] zeroinitializer
// CHECK-NEXT: @empty = global [0 x i32] zeroinitializer
// CHECK-NEXT: @bits = global [2 x i1] [i1 1, i1 0]
// CHECK-NEXT: @raw = global [3 x i16] [i16 65535, i16 32768, i16 4660]
// CHECK-NEXT: @raw_splat = global [2 x i16] [i16 4660, i16 4660]
