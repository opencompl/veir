// RUN: veir-opt %s -p=riscv-combine | filecheck %s
// RUN: %if mlir-min-22 %{ veir-opt %s -p=riscv-combine | mlir-opt --mlir-print-op-generic %}

"builtin.module"() ({
  // `300 : i32` in an i8 result is the value 44, so smin(44, 50) = 44:
  // folding the raw `300` would pick 50 instead.
  "func.func"() <{function_type = () -> i8, sym_name = "smin_narrowed"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 50 : i8}> : () -> i8
    %r = "llvm.intr.smin"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // `200 : i8` in an i32 result is the value -56, so smax(-56, 0) = 0:
  // folding the raw `200` would pick 200 instead.
  "func.func"() <{function_type = () -> i32, sym_name = "smax_widened"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 200 : i8}> : () -> i32
    %c2 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %r = "llvm.intr.smax"(%c1, %c2) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // add is congruent mod 2^8, so the *value* survives: 44 + 50 = 94.  The sum
  // is reduced before it is materialized; `350 : i8` would be out of range.
  "func.func"() <{function_type = () -> i8, sym_name = "add_narrowed"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 50 : i8}> : () -> i8
    %r = "llvm.add"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // sub_to_add negates the constant: -(-128) is 128, which is not an i8, so
  // the materialized literal must wrap back to -128.  Reachable without any
  // width mismatch in the input.
  "func.func"() <{function_type = (i8) -> i8, sym_name = "sub_to_add_min"}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %r = "llvm.sub"(%x, %c) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @smin_narrowed() -> i8 {
// CHECK:         "llvm.mlir.constant"() <{"value" = 44 : i8}> : () -> i8

// CHECK-LABEL: func.func @smax_widened() -> i32 {
// CHECK:         "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32

// CHECK-LABEL: func.func @add_narrowed() -> i8 {
// CHECK:         "llvm.mlir.constant"() <{"value" = 94 : i8}> : () -> i8

// CHECK-LABEL: func.func @sub_to_add_min(%{{.*}}: i8) -> i8 {
// CHECK:         "llvm.mlir.constant"() <{"value" = -128 : i8}> : () -> i8
