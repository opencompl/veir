// RUN: veir-opt %s -p=riscv-combine | filecheck %s
// RUN: %if mlir-min-22 %{ veir-opt %s -p=riscv-combine | mlir-opt --mlir-print-op-generic %}

// Constants built by the combines are normalized to their width, as the
// verifier requires.

"builtin.module"() ({
  // The sum is reduced before it is materialized: 127 + 1 wraps to -128;
  // `128 : i8` would not be normalized.
  "func.func"() <{function_type = () -> i8, sym_name = "add_wraps"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 127 : i8}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %r = "llvm.add"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // sub_to_add negates the constant: -(-128) is 128, which is not an i8, so
  // the materialized literal must wrap back to -128.
  "func.func"() <{function_type = (i8) -> i8, sym_name = "sub_to_add_min"}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %r = "llvm.sub"(%x, %c) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @add_wraps() -> i8 {
// CHECK:         "llvm.mlir.constant"() <{"value" = -128 : i8}> : () -> i8

// CHECK-LABEL: func.func @sub_to_add_min(%{{.*}}: i8) -> i8 {
// CHECK:         "llvm.mlir.constant"() <{"value" = -128 : i8}> : () -> i8
