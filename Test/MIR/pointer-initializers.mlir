// RUN: veir-opt %s -p=riscv > %t
// RUN: filecheck %s --check-prefix=IR --input-file=%t
// RUN: veir2mir %t | filecheck %s

"builtin.module"() ({
  "llvm.mlir.global"() <{global_type = !llvm.struct<"Outer", (i64, !llvm.struct<(i16, i16, i64)>)>, linkage = #llvm.linkage<external>, sym_name = "object"}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.array<8 x i32>, linkage = #llvm.linkage<external>, sym_name = "array name"}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "field", alignment = 8 : i64}> ({
    %base = "llvm.mlir.addressof"() <{global_name = @object}> : () -> !llvm.ptr
    %field = "llvm.getelementptr"(%base) <{elem_type = !llvm.struct<"Outer", (i64, !llvm.struct<(i16, i16, i64)>)>, rawConstantIndices = array<i32: 0, 1, 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%field) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<internal>, constant, sym_name = "array_element"}> ({
    %base = "llvm.mlir.addressof"() <{global_name = @"array name"}> : () -> !llvm.ptr
    %two = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %element = "llvm.getelementptr"(%base, %two) <{elem_type = i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    "llvm.return"(%element) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "negative_offset"}> ({
    %base = "llvm.mlir.addressof"() <{global_name = @"array name"}> : () -> !llvm.ptr
    %one = "llvm.getelementptr"(%base) <{elem_type = i32, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %minus_two = "llvm.mlir.constant"() <{value = 4294967294 : i32}> : () -> i32
    %result = "llvm.getelementptr"(%one, %minus_two) <{elem_type = i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    "llvm.return"(%result) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "pointer_to_pointer"}> ({
    %base = "llvm.mlir.addressof"() <{global_name = @field}> : () -> !llvm.ptr
    "llvm.return"(%base) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "null_pointer"}> ({
    %zero = "llvm.mlir.zero"() : () -> !llvm.ptr
    "llvm.return"(%zero) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "function_pointer"}> ({
    %fn = "llvm.mlir.addressof"() <{global_name = @"external function"}> : () -> !llvm.ptr
    "llvm.return"(%fn) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "external function"}> ({}) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<!llvm.ptr ()>, sym_name = "get_field"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @field}> : () -> !llvm.ptr
    %v = "llvm.load"(%p) : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%v) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// The pipeline must preserve link-time expressions, while selecting function bodies.
// IR: "sym_name" = "field"
// IR-NEXT: ^{{.*}}():
// IR-NEXT: %{{.*}} = "llvm.mlir.addressof"
// IR-NEXT: %{{.*}} = "llvm.getelementptr"
// IR-NEXT: "llvm.return"
// IR: "sym_name" = "array_element"
// IR-NEXT: ^{{.*}}():
// IR: "llvm.mlir.constant"
// IR: "llvm.getelementptr"
// IR: "sym_name" = "get_field"
// IR: "riscv.la"
// IR: "riscv.ld"

// CHECK: @field = global ptr getelementptr (i8, ptr @object, i64 16), align 8
// CHECK-NEXT: @array_element = internal constant ptr getelementptr (i8, ptr @"array name", i64 8)
// CHECK-NEXT: @negative_offset = global ptr getelementptr (i8, ptr @"array name", i64 -4)
// CHECK-NEXT: @pointer_to_pointer = global ptr @field
// CHECK-NEXT: @null_pointer = global ptr null
// CHECK-NEXT: @function_pointer = global ptr @"external function"
// CHECK: declare void @"external function"()
