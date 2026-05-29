// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      // --- Identity and annihilation patterns ---
      %x = "test.test"() : () -> i32
      // CHECK: %[[X:.*]] = "test.test"() : () -> i32

      // and x & x => x
      %and_self = "llvm.and"(%x, %x) : (i32, i32) -> i32
      "test.test"(%and_self) : (i32) -> ()
      // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
