// RUN: veir-opt %s -p=canonicalize | filecheck %s

"builtin.module"() ({

  // A block without predecessors is erased, and so is the block it branches to,
  // even though that block uses a value defined in the first one.
  // CHECK-LABEL: func.func @chain
  // CHECK-NEXT:    "func.return"() : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = () -> (), sym_name = "chain"}> ({
  ^entry():
    "func.return"() : () -> ()
  ^first():
    %x = "test.test"() : () -> i32
    "cf.br"() [^second] : () -> ()
  ^second():
    "test.test"(%x) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // Blocks of an unreachable cycle all have predecessors, but are erased.
  // CHECK-LABEL: func.func @cycle
  // CHECK-NEXT:    "func.return"() : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = () -> (), sym_name = "cycle"}> ({
  ^entry():
    "func.return"() : () -> ()
  ^a():
    "cf.br"() [^b] : () -> ()
  ^b():
    "cf.br"() [^a] : () -> ()
  }) : () -> ()

  // An unreachable block may branch to a reachable block and use a value of a
  // reachable block, including from a nested region. Only the unreachable block
  // goes away.
  // CHECK-LABEL: func.func @into_live
  // CHECK-NEXT:    "cf.br"(%[[A:.*]]) [^[[EXIT:.*]]] : (i32) -> ()
  // CHECK-NEXT:  ^[[EXIT]](%[[V:.*]] : i32):
  // CHECK-NEXT:    "test.test"(%[[V]]) : (i32) -> ()
  // CHECK-NEXT:    "func.return"() : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = (i32) -> (), sym_name = "into_live"}> ({
  ^entry(%a : i32):
    "cf.br"(%a) [^exit] : (i32) -> ()
  ^dead():
    "test.test"() ({
      "test.test"(%a) : (i32) -> ()
    }) : () -> ()
    "cf.br"(%a) [^exit] : (i32) -> ()
  ^exit(%v : i32):
    "test.test"(%v) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // Unreachable blocks in a region nested in a reachable block are erased.
  // Reachable blocks, including a loop, are kept.
  // CHECK-LABEL: func.func @nested
  // CHECK-NEXT:    "test.test"() ({
  // CHECK-NEXT:      ^{{.*}}():
  // CHECK-NEXT:        func.func @inner() {
  // CHECK-NEXT:        "func.return"() : () -> ()
  // CHECK-NEXT:      }
  // CHECK-NEXT:    }) : () -> ()
  // CHECK-NEXT:    "cf.br"() [^[[LOOP:.*]]] : () -> ()
  // CHECK-NEXT:  ^[[LOOP]]():
  // CHECK-NEXT:    "cf.br"() [^[[LOOP]]] : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = () -> (), sym_name = "nested"}> ({
  ^entry():
    "test.test"() ({
      "func.func"() <{function_type = () -> (), sym_name = "inner"}> ({
      ^innerEntry():
        "func.return"() : () -> ()
      ^innerDead():
        "func.return"() : () -> ()
      }) : () -> ()
    }) : () -> ()
    "cf.br"() [^loop] : () -> ()
  ^loop():
    "cf.br"() [^loop] : () -> ()
  }) : () -> ()

}) : () -> ()
