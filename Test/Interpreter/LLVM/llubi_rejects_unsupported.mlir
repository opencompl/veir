// REQUIRES: llubi
// RUN: not %llubi-interpret %s 2>&1 | filecheck %s

// A negative test of the translator: an operation it cannot translate, here
// `llvm.readcyclecounter`, must fail the cross-check loudly instead of passing it
// silently. If the translator learns it, swap in another
// unsupported operation and update the message below.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %v = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %c = "llvm.readcyclecounter"() : () -> i64
    "llvm.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2llvm: error: unsupported LLVM operation: llvm.readcyclecounter
