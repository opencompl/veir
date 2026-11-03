// RUN: veir-opt %s -p=riscv > %t
// RUN: veir2mir %t | filecheck %s

// Identified structs can be printed inline in the stub IR: the name is not
// needed by machine operands, but nesting, arrays and packed layout must survive.
"builtin.module"() ({
  "llvm.mlir.global"() <{global_type = !llvm.struct<(i8, i32, !llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "literal", alignment = 8 : i64}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.struct<"Outer", (i64, !llvm.struct<"Inner", (i16, i16, i64)>)>, linkage = #llvm.linkage<external>, sym_name = "nested", alignment = 8 : i64}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.struct<"Packed", packed (i8, !llvm.array<2 x !llvm.struct<(i16, i32)>>)>, linkage = #llvm.linkage<external>, sym_name = "packed", alignment = 1 : i64}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<3 x !llvm.struct<packed (i8, i64)>>, linkage = #llvm.linkage<external>, sym_name = "array"}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.struct<()>, linkage = #llvm.linkage<external>, sym_name = "empty"}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.struct<"EmptyPacked", packed ()>, linkage = #llvm.linkage<external>, sym_name = "empty_packed"}> ({}) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "load_nested"}> ({
    %base = "llvm.mlir.addressof"() <{global_name = @nested}> : () -> !llvm.ptr
    %field = "llvm.getelementptr"(%base) <{elem_type = !llvm.struct<"Outer", (i64, !llvm.struct<"Inner", (i16, i16, i64)>)>, rawConstantIndices = array<i32: 0, 1, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %value = "llvm.load"(%field) : (!llvm.ptr) -> i64
    "llvm.return"(%value) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT:  UNHANDLED
// CHECK:      @literal = external global { i8, i32, ptr }, align 8
// CHECK-NEXT: @nested = external global { i64, { i16, i16, i64 } }, align 8
// CHECK-NEXT: @packed = external global <{ i8, [2 x { i16, i32 }] }>, align 1
// CHECK-NEXT: @array = external global [3 x <{ i8, i64 }>]
// CHECK-NEXT: @empty = external global {  }
// CHECK-NEXT: @empty_packed = external global <{  }>
// CHECK-NOT:  UNHANDLED
// CHECK-LABEL: name: load_nested
// CHECK-NOT:  UNHANDLED
// CHECK:      [[BASE:%v[0-9]+]]:gpr = PseudoLLA @nested
// CHECK-NEXT: {{%v[0-9]+}}:gpr = LD [[BASE]], 16
// CHECK-NOT:  UNHANDLED
