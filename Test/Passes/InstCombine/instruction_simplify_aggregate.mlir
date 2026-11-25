// RUN: veir-opt %s --print-op-generic -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "reconstruct", function_type = (!llvm.struct<(i8, i32)>) -> !llvm.struct<(i8, i32)>}> ({
  ^bb0(%a: !llvm.struct<(i8, i32)>):
    %undef = "llvm.mlir.undef"() : () -> !llvm.struct<(i8, i32)>
    %x = "llvm.extractvalue"(%a) <{position = array<i64: 0>}> : (!llvm.struct<(i8, i32)>) -> i8
    %y = "llvm.extractvalue"(%a) <{position = array<i64: 1>}> : (!llvm.struct<(i8, i32)>) -> i32
    %first = "llvm.insertvalue"(%undef, %x) <{position = array<i64: 0>}> : (!llvm.struct<(i8, i32)>, i8) -> !llvm.struct<(i8, i32)>
    %both = "llvm.insertvalue"(%first, %y) <{position = array<i64: 1>}> : (!llvm.struct<(i8, i32)>, i32) -> !llvm.struct<(i8, i32)>
    "func.return"(%both) : (!llvm.struct<(i8, i32)>) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "reconstruct"
  // CHECK-NOT: "llvm.
  // CHECK: "func.return"(%arg{{[0-9]+}}_0)

  // Reconstructing only two fields of a three-field aggregate is not identity.
  "func.func"() <{sym_name = "partial_reconstruction", function_type = (!llvm.array<3 x i8>) -> !llvm.array<3 x i8>}> ({
  ^bb0(%a: !llvm.array<3 x i8>):
    %undef = "llvm.mlir.undef"() : () -> !llvm.array<3 x i8>
    %x = "llvm.extractvalue"(%a) <{position = array<i64: 0>}> : (!llvm.array<3 x i8>) -> i8
    %y = "llvm.extractvalue"(%a) <{position = array<i64: 1>}> : (!llvm.array<3 x i8>) -> i8
    %first = "llvm.insertvalue"(%undef, %x) <{position = array<i64: 0>}> : (!llvm.array<3 x i8>, i8) -> !llvm.array<3 x i8>
    %both = "llvm.insertvalue"(%first, %y) <{position = array<i64: 1>}> : (!llvm.array<3 x i8>, i8) -> !llvm.array<3 x i8>
    "func.return"(%both) : (!llvm.array<3 x i8>) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "partial_reconstruction"
  // CHECK: "llvm.insertvalue"
  // CHECK: "llvm.insertvalue"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "equal_path", function_type = (!llvm.struct<(i8, !llvm.array<2 x i32>)>, i32) -> i32}> ({
  ^bb0(%a: !llvm.struct<(i8, !llvm.array<2 x i32>)>, %x: i32):
    %b = "llvm.insertvalue"(%a, %x) <{position = array<i64: 1, 0>}> : (!llvm.struct<(i8, !llvm.array<2 x i32>)>, i32) -> !llvm.struct<(i8, !llvm.array<2 x i32>)>
    %r = "llvm.extractvalue"(%b) <{position = array<i64: 1, 0>}> : (!llvm.struct<(i8, !llvm.array<2 x i32>)>) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "equal_path"
  // CHECK-NOT: "llvm.
  // CHECK: "func.return"(%arg{{[0-9]+}}_1)

  "func.func"() <{sym_name = "extract_prefix", function_type = (!llvm.struct<(i8, !llvm.array<2 x i32>)>, i32) -> !llvm.array<2 x i32>}> ({
  ^bb0(%a: !llvm.struct<(i8, !llvm.array<2 x i32>)>, %x: i32):
    %b = "llvm.insertvalue"(%a, %x) <{position = array<i64: 1, 0>}> : (!llvm.struct<(i8, !llvm.array<2 x i32>)>, i32) -> !llvm.struct<(i8, !llvm.array<2 x i32>)>
    %r = "llvm.extractvalue"(%b) <{position = array<i64: 1>}> : (!llvm.struct<(i8, !llvm.array<2 x i32>)>) -> !llvm.array<2 x i32>
    "func.return"(%r) : (!llvm.array<2 x i32>) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "extract_prefix"
  // CHECK: %[[SUB:[0-9]+]] = "llvm.extractvalue"(%arg{{[0-9]+}}_0) <{"position" = array<i64: 1>}>
  // CHECK: "llvm.insertvalue"(%[[SUB]], %arg{{[0-9]+}}_1) <{"position" = array<i64: 0>}>
  // CHECK-NOT: "llvm.
  // CHECK: "func.return"

  "func.func"() <{sym_name = "insert_prefix", function_type = (!llvm.struct<(i8, !llvm.array<2 x i32>)>, !llvm.array<2 x i32>) -> i32}> ({
  ^bb0(%a: !llvm.struct<(i8, !llvm.array<2 x i32>)>, %x: !llvm.array<2 x i32>):
    %b = "llvm.insertvalue"(%a, %x) <{position = array<i64: 1>}> : (!llvm.struct<(i8, !llvm.array<2 x i32>)>, !llvm.array<2 x i32>) -> !llvm.struct<(i8, !llvm.array<2 x i32>)>
    %r = "llvm.extractvalue"(%b) <{position = array<i64: 1, 0>}> : (!llvm.struct<(i8, !llvm.array<2 x i32>)>) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "insert_prefix"
  // CHECK: "llvm.extractvalue"(%arg{{[0-9]+}}_1) <{"position" = array<i64: 0>}>
  // CHECK-NOT: "llvm.
  // CHECK: "func.return"

  // Sharing the first index does not make one path a prefix of the other.
  "func.func"() <{sym_name = "divergent_paths", function_type = (!llvm.struct<(i8, !llvm.array<2 x i32>)>, i32) -> i32}> ({
  ^bb0(%a: !llvm.struct<(i8, !llvm.array<2 x i32>)>, %x: i32):
    %b = "llvm.insertvalue"(%a, %x) <{position = array<i64: 1, 0>}> : (!llvm.struct<(i8, !llvm.array<2 x i32>)>, i32) -> !llvm.struct<(i8, !llvm.array<2 x i32>)>
    %r = "llvm.extractvalue"(%b) <{position = array<i64: 1, 1>}> : (!llvm.struct<(i8, !llvm.array<2 x i32>)>) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "divergent_paths"
  // CHECK: "llvm.extractvalue"(%arg{{[0-9]+}}_0) <{"position" = array<i64: 1, 1>}>
  // CHECK-NOT: "llvm.
  // CHECK: "func.return"
}) : () -> ()
