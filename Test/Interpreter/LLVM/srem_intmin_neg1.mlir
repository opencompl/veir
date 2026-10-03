// RUN: veir-interpret %s | filecheck %s

// LLUBI: returns 0 here, but LangRef makes srem overflow undefined behaviour
// so that srem can lower to an instruction that divides and takes the
// remainder at once; llubi checks the overflow for sdiv but not for srem.

// `srem intMin, -1` is immediate UB (signed overflow in the implicit division).
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %intmin = "llvm.mlir.constant"() <{ "value" = -2147483648 : i32 }> : () -> i32
    %negone = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
    %y = "llvm.srem"(%intmin, %negone) : (i32, i32) -> i32
    "llvm.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
