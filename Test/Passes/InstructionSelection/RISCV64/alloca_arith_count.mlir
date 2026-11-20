// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// XFAIL: *
// The branch step of `llvm-to-gmir` rejects a module with an operation outside its refinement
// proof, and `arith` is not covered, so an `arith.constant` count is not lowered.

"builtin.module"() ({
  "func.func"() <{sym_name = "constant_like", function_type = () -> ()}> ({
    %two = "arith.constant"() <{value = 2 : i32}> : () -> i32
    %a = "llvm.alloca"(%two) <{elem_type = i64}> : (i32) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 16 : i64}>
    "test.test"(%a) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
