// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// Aliases precede the top-level operation, may build on earlier ones, and resolve
// wherever a type appears, including attribute element types. The printer expands them.
!int = i32
!ptr = !llvm.ptr
!fn = (!int, !ptr) -> !int
"builtin.module"() ({
  "func.func"() <{function_type = !fn, sym_name = "f"}> ({
  ^bb0(%a: !int, %p: !ptr):
    %c = "arith.constant"() <{value = 1 : !int}> : () -> !int
    %s = "arith.addi"(%a, %c) : (!int, !int) -> !int
    %g = "llvm.getelementptr"(%p, %a) <{elem_type = !int, rawConstantIndices = array<!int: -2147483648>}> : (!ptr, !int) -> !ptr
    "func.return"(%s) : (!int) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, !llvm.ptr) -> i32, "sym_name" = "f"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : i32, %{{.*}} : !llvm.ptr):
// CHECK-NEXT: %{{.*}} = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT: %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = i32, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
// CHECK-NEXT: "func.return"(%{{.*}}) : (i32) -> ()
