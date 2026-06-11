// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "main"}> ({
    ^bb0(%0 : i32):
        %1 = "llvm.alloca"(%0) <{"alignment" = 4 : i32, "elem_type" = i32, inalloca}> : (i32) -> !llvm.ptr
        // CHECK: 'llvm.alloca' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
