// RUN: veir-opt %s -p=canonicalize | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "null_pointer", function_type = () -> !llvm.ptr}> ({
    // CHECK-LABEL: func.func @null_pointer
    // CHECK-NEXT: %[[NULL:.*]] = "llvm.mlir.zero"() : () -> !llvm.ptr
    // CHECK-NEXT: "func.return"(%[[NULL]]) : (!llvm.ptr) -> ()
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %ptr = "llvm.inttoptr"(%zero) : (i64) -> !llvm.ptr
    "func.return"(%ptr) : (!llvm.ptr) -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "poison_pointer", function_type = () -> !llvm.ptr}> ({
    // CHECK-LABEL: func.func @poison_pointer
    // CHECK-NEXT: %[[POISON:.*]] = "llvm.mlir.poison"() : () -> !llvm.ptr
    // CHECK-NEXT: "func.return"(%[[POISON]]) : (!llvm.ptr) -> ()
    %poison = "llvm.mlir.poison"() : () -> i64
    %ptr = "llvm.inttoptr"(%poison) : (i64) -> !llvm.ptr
    "func.return"(%ptr) : (!llvm.ptr) -> ()
  }) : () -> ()

  // Non-null concrete pointers still have no constant materialization.
  "func.func"() <{sym_name = "nonnull_pointer", function_type = () -> !llvm.ptr}> ({
    // CHECK-LABEL: func.func @nonnull_pointer
    // CHECK-NEXT: %[[ONE:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[PTR:.*]] = "llvm.inttoptr"(%[[ONE]]) : (i64) -> !llvm.ptr
    // CHECK-NEXT: "func.return"(%[[PTR]]) : (!llvm.ptr) -> ()
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %ptr = "llvm.inttoptr"(%one) : (i64) -> !llvm.ptr
    "func.return"(%ptr) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()
