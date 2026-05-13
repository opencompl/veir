// RUN: veir-interpret %s | filecheck %s

// Branching on a poison i1 is undefined behaviour. The i1 poison is produced by
// `llvm.add nuw` on i1 (1 + 1 overflows unsigned).
"builtin.module"() ({
  ^entry():
    %one    = "llvm.mlir.constant"() <{"value" = 1 : i1}> : () -> i1
    %poison = "llvm.add"(%one, %one) <{nuw}> : (i1, i1) -> i1
    %tval   = "llvm.mlir.constant"() <{"value" = 42 : i32}> : () -> i32
    %fval   = "llvm.mlir.constant"() <{"value" = 99 : i32}> : () -> i32
    "llvm.cond_br"(%poison, %tval, %fval) [^t, ^f]
      <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^t(%x : i32):
    "llvm.return"(%x) : (i32) -> ()
  ^f(%y : i32):
    "llvm.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
