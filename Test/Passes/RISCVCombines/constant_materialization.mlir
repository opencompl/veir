// RUN: veir-opt %s -p=riscv-combine | filecheck %s
// RUN: %if mlir-min-22 %{ veir-opt %s -p=riscv-combine | mlir-opt --mlir-print-op-generic %}

// Computed constants wrap to their result width and use signed literals that
// fit their attribute types. The pass output must also be accepted by MLIR.
"builtin.module"() ({
  // Addition is congruent modulo 2^8: 300 + 50 becomes 94 at i8.
  "func.func"() <{function_type = () -> i8, sym_name = "add_narrowed"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 50 : i8}> : () -> i8
    %r = "llvm.add"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // Negating the minimum signed integer wraps back to itself at i8.
  "func.func"() <{function_type = (i8) -> i8, sym_name = "sub_to_add_min"}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %r = "llvm.sub"(%x, %c) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // Overflow also occurs when the attribute and result widths match.
  "func.func"() <{function_type = () -> i8, sym_name = "add_overflow"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 100 : i8}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 101 : i8}> : () -> i8
    %r = "llvm.add"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // Negative results below the signed range wrap as well: -300 becomes -44.
  "func.func"() <{function_type = () -> i8, sym_name = "mul_underflow"}> ({
    %c1 = "llvm.mlir.constant"() <{value = -100 : i8}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %r = "llvm.mul"(%c1, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "add_narrowed"
// CHECK: %[[ADD:.*]] = "llvm.mlir.constant"() <{"value" = 94 : i8}> : () -> i8
// CHECK-NEXT: "func.return"(%[[ADD]]) : (i8) -> ()

// CHECK-LABEL: "sym_name" = "sub_to_add_min"
// CHECK: %[[MIN:.*]] = "llvm.mlir.constant"() <{"value" = -128 : i8}> : () -> i8
// CHECK-NEXT: %[[SUB:.*]] = "llvm.add"(%{{.*}}, %[[MIN]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[SUB]]) : (i8) -> ()

// CHECK-LABEL: "sym_name" = "add_overflow"
// CHECK: %[[OVERFLOW:.*]] = "llvm.mlir.constant"() <{"value" = -55 : i8}> : () -> i8
// CHECK-NEXT: "func.return"(%[[OVERFLOW]]) : (i8) -> ()

// CHECK-LABEL: "sym_name" = "mul_underflow"
// CHECK: %[[UNDERFLOW:.*]] = "llvm.mlir.constant"() <{"value" = -44 : i8}> : () -> i8
// CHECK-NEXT: "func.return"(%[[UNDERFLOW]]) : (i8) -> ()
