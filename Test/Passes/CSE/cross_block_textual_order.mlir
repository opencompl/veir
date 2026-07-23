// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

"builtin.module"() ({
  // ^def dominates ^use in the CFG, but ^use appears first in textual order.
  // Dominance-order traversal should still see ^def's add first and reuse it.
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32)>, sym_name = "textual_order"}> ({
  ^entry(%a : i32, %b : i32):
    "llvm.br"() [^def] : () -> ()
  ^use:
    %u = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%u) : (i32) -> ()
    "llvm.return"() : () -> ()
  ^def:
    %d = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%d) : (i32) -> ()
    "llvm.br"() [^use] : () -> ()
  }) : () -> ()

  // CHECK-LABEL: void (i32, i32)>
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    "test.test"(%[[D:.*]]) : (i32) -> ()
  // CHECK-NEXT:    "llvm.return"() : () -> ()
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    %[[D]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:    "test.test"(%[[D]]) : (i32) -> ()
}) : () -> ()
