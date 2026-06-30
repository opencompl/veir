// RUN: veir-interpret %s | filecheck %s

// Branching on a poison i1 is undefined behaviour.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %poison = "llvm.mlir.poison"() : () -> i1
      %tval   = "llvm.mlir.constant"() <{"value" = 42 : i32}> : () -> i32
      %fval   = "llvm.mlir.constant"() <{"value" = 99 : i32}> : () -> i32
      "llvm.cond_br"(%poison, %tval, %fval) [^t, ^f]
        <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    ^t(%x : i32):
      "llvm.return"(%x) : (i32) -> ()
    ^f(%y : i32):
      "llvm.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
