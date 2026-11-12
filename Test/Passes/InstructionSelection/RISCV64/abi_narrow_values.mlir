// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s

// XFAIL: *
// Needs `widenBlockArguments`, commented out of the pass as unproven.

// A narrow call result is copied out of its register with a `g_trunc`. The legalizer folds it
// with the `g_anyext` of the block argument, so the returned value needs no `zext.b`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "source8", function_type = !llvm.func<i8 ()>}> ({
  }) : () -> ()

  "llvm.func"() <{sym_name = "select_call8", function_type = !llvm.func<i8 (i1, i8)>}> ({
  ^bb0(%c : i1, %x : i8):
    // CHECK-LABEL: "sym_name" = "select_call8"
    // CHECK:       "riscv_cf.bnez"
    // CHECK-NEXT:  ^{{.*}}(%[[R:.*]] : !riscv.reg):
    // CHECK-NEXT:    "riscv_cf.return"(%[[R]])
    %a = "llvm.call"() <{callee = @source8}> : () -> i8
    "llvm.cond_br"(%c, %a, %x) [^bb1, ^bb1] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i8, i8) -> ()
  ^bb1(%r : i8):
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
