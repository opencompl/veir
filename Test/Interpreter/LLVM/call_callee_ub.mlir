// RUN: veir-interpret --ctree %s | filecheck %s
// RUN: LLUBI

// Undefined behavior in a callee is undefined behavior of the whole program, not just of the call.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<void ()>}> ({
    // Division by 0
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %x = "llvm.udiv"(%one, %zero) : (i32, i32) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    "llvm.call"() <{callee = @f}> : () -> ()
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.return"(%one) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
