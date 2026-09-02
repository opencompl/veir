// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %len = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    "io.rand"(%buf, %len) : (!llvm.ptr, i64) -> ()
    "io.send"(%buf, %len) : (!llvm.ptr, i64) -> ()
    "io.recv"(%buf, %len) : (!llvm.ptr, i64) -> ()
    "io.send"(%buf, %len) : (!llvm.ptr, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %[[len:.*]] = "llvm.mlir.constant"() <{"value" = 32 : i64}> : () -> i64
// CHECK-NEXT:         %[[buf:.*]] = "llvm.alloca"(%[[len]]) <{"alignment" = 0 : i64, "elem_type" = i8}> : (i64) -> !llvm.ptr
// CHECK-NEXT:         "io.rand"(%[[buf]], %[[len]]) : (!llvm.ptr, i64) -> ()
// CHECK-NEXT:         "io.send"(%[[buf]], %[[len]]) : (!llvm.ptr, i64) -> ()
// CHECK-NEXT:         "io.recv"(%[[buf]], %[[len]]) : (!llvm.ptr, i64) -> ()
// CHECK-NEXT:         "io.send"(%[[buf]], %[[len]]) : (!llvm.ptr, i64) -> ()
// CHECK-NEXT:         "func.return"() : () -> ()
