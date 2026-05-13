// RUN: veir-interpret %s | filecheck %s

// UB triggered by a poison cond_br in a non-entry block must propagate up
// through `interpretBlockCFG`'s recursive call rather than being lost or
// reported as a malformed-program error.
"builtin.module"() ({
  ^entry():
    "llvm.br"() [^poison_block] : () -> ()
  ^poison_block():
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
