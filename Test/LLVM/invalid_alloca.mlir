// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
        %0 = "llvm.constant"() <{"value" = 13 : i32}> : () -> i32
        %1 = "llvm.alloca"(%0) <{"alignment" = 4 : i32, "elem_type" = i32, inalloca}> : (i32) -> !llvm.ptr
        // CHECK: Expected alignment to be an i64 constant
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

