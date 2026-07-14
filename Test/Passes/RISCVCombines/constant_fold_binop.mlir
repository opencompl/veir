// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `binop(C1, C2)` with two constant operands folds to a single constant. Only
// opcodes well-defined over unbounded integers are folded here: add, sub, mul,
// smin, smax.

"builtin.module"() ({
  // add(5, 7) = 12
  "func.func"() <{function_type = () -> i32, sym_name = "foo"}> ({
  ^bb0():
    %a = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %r = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // sub(20, 8) = 12
  "func.func"() <{function_type = () -> i32, sym_name = "bar"}> ({
  ^bb0():
    %a = "llvm.mlir.constant"() <{value = 20 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %r = "llvm.sub"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // smin(4, 9) = 4
  "func.func"() <{function_type = () -> i32, sym_name = "baz"}> ({
  ^bb0():
    %a = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{value = 9 : i32}> : () -> i32
    %r = "llvm.intr.smin"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// add folds to 12.
// CHECK:      ^{{.*}}():
// CHECK:      %[[R:.*]] = "llvm.mlir.constant"() <{"value" = 12 : i32}> : () -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// sub folds to 12.
// CHECK:      ^{{.*}}():
// CHECK:      %[[R2:.*]] = "llvm.mlir.constant"() <{"value" = 12 : i32}> : () -> i32
// CHECK:      "func.return"(%[[R2]]) : (i32) -> ()

// smin folds to a constant (the smin op is gone).
// CHECK:      ^{{.*}}():
// CHECK-NOT:  "llvm.intr.smin"
// CHECK:      "func.return"(%{{.*}}) : (i32) -> ()
