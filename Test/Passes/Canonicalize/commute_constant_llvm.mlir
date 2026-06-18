// RUN: veir-opt %s -p=canonicalize | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "main"}> ({
    ^bb0(%x : i32):
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c = "llvm.mlir.constant"() <{ "value" = 5 : i32 }> : () -> i32
      // CHECK-NEXT: %[[C:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32

      // Commutative op with the constant on the left: operands are swapped
      // so the constant is pushed to the right.
      %add = "llvm.add"(%c, %x) : (i32, i32) -> i32
      // CHECK-NEXT: %[[ADD:.*]] = "llvm.add"(%[[X]], %[[C]]) : (i32, i32) -> i32

      // Non-commutative op: operands are left untouched.
      %sub = "llvm.sub"(%c, %x) : (i32, i32) -> i32
      // CHECK-NEXT: "llvm.sub"(%[[C]], %[[X]]) : (i32, i32) -> i32

      // Already canonical (constant on the right): unchanged.
      %ok = "llvm.add"(%x, %c) : (i32, i32) -> i32
      // CHECK-NEXT: "llvm.add"(%[[X]], %[[C]]) : (i32, i32) -> i32

      "func.return"(%add) : (i32) -> ()
      // CHECK-NEXT: "func.return"(%[[ADD]]) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
