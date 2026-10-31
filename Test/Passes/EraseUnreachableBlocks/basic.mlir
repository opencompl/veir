// RUN: veir-opt %s -p=erase-unreachable-blocks | filecheck %s
// The output verifies, and the pass leaves it unchanged.
// RUN: veir-opt %s -p=erase-unreachable-blocks --print-op-generic | veir-opt -p=erase-unreachable-blocks | filecheck %s

"builtin.module"() ({

  // A single block without predecessors is erased.
  // CHECK-LABEL: func.func @no_predecessors
  // CHECK-NEXT:    "test.test"() : () -> ()
  // CHECK-NEXT:    "func.return"() : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = () -> (), sym_name = "no_predecessors"}> ({
  ^entry():
    "test.test"() : () -> ()
    "func.return"() : () -> ()
  ^dead():
    "test.test"() : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // An unreachable block may use the values of the unreachable block branching
  // to it. Both are erased.
  // CHECK-LABEL: func.func @chain
  // CHECK-NEXT:    "func.return"() : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = () -> (), sym_name = "chain"}> ({
  ^entry():
    "func.return"() : () -> ()
  ^first():
    %x = "arith.constant"() <{value = 1 : i32}> : () -> i32
    "cf.br"() [^second] : () -> ()
  ^second():
    "test.test"(%x) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // Every block of an unreachable cycle has a predecessor. The cycle is erased.
  // CHECK-LABEL: func.func @cycle
  // CHECK-NEXT:    "func.return"() : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = (i32) -> (), sym_name = "cycle"}> ({
  ^entry(%a : i32):
    "func.return"() : () -> ()
  ^loop(%b : i32):
    "cf.br"(%b) [^back] : (i32) -> ()
  ^back(%c : i32):
    "cf.br"(%c) [^loop] : (i32) -> ()
  }) : () -> ()

  // An unreachable block branching to a reachable block is erased, and the
  // reachable block loses a predecessor.
  // CHECK-LABEL: func.func @dead_to_live
  // CHECK-NEXT:    "cf.br"(%{{.*}}) [^[[exit:.*]]] : (i32) -> ()
  // CHECK-NEXT:  ^[[exit]](%[[v:.*]] : i32):
  // CHECK-NEXT:    "test.test"(%[[v]]) : (i32) -> ()
  // CHECK-NEXT:    "func.return"() : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = (i32) -> (), sym_name = "dead_to_live"}> ({
  ^entry(%a : i32):
    "cf.br"(%a) [^exit] : (i32) -> ()
  ^dead():
    %x = "arith.constant"() <{value = 7 : i32}> : () -> i32
    "cf.br"(%x) [^exit] : (i32) -> ()
  ^exit(%v : i32):
    "test.test"(%v) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // Operations nested in an unreachable block may use values of a reachable
  // block. Their uses are dropped with them, including those in multi-block
  // nested regions, which may contain branches of their own.
  // CHECK-LABEL: func.func @nested_use
  // CHECK-NEXT:    "test.test"(%{{.*}}) : (i32) -> ()
  // CHECK-NEXT:    "func.return"() : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = (i32) -> (), sym_name = "nested_use"}> ({
  ^entry(%a : i32):
    "test.test"(%a) : (i32) -> ()
    "func.return"() : () -> ()
  ^dead():
    "test.test"() ({
      "test.test"(%a) : (i32) -> ()
      "func.func"() <{function_type = () -> (), sym_name = "inner"}> ({
      ^inner():
        %y = "arith.constant"() <{value = 3 : i32}> : () -> i32
        "cf.br"() [^inner2] : () -> ()
      ^inner2():
        "test.test"(%y) : (i32) -> ()
        "func.return"() : () -> ()
      }) : () -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // Unreachable blocks in a region nested in a reachable block are erased too.
  // CHECK-LABEL: func.func @nested_region
  // CHECK-NEXT:    "test.test"() ({
  // CHECK-NEXT:      ^{{.*}}():
  // CHECK-NEXT:        func.func @inner_live() {
  // CHECK-NEXT:        "func.return"() : () -> ()
  // CHECK-NEXT:      }
  // CHECK-NEXT:    }) : () -> ()
  // CHECK-NEXT:    "func.return"() : () -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = () -> (), sym_name = "nested_region"}> ({
  ^entry():
    "test.test"() ({
      "func.func"() <{function_type = () -> (), sym_name = "inner_live"}> ({
      ^inner():
        "func.return"() : () -> ()
      ^innerDead():
        "func.return"() : () -> ()
      }) : () -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // Reachable blocks, including a loop, are kept.
  // CHECK-LABEL: func.func @all_reachable
  // CHECK-NEXT:    "cf.br"(%{{.*}}) [^[[loop:.*]]] : (i32) -> ()
  // CHECK-NEXT:  ^[[loop]](%{{.*}} : i32):
  // CHECK-NEXT:    "cf.br"(%{{.*}}) [^[[loop]]] : (i32) -> ()
  // CHECK-NEXT:  }
  "func.func"() <{function_type = (i32) -> (), sym_name = "all_reachable"}> ({
  ^entry(%a : i32):
    "cf.br"(%a) [^loop] : (i32) -> ()
  ^loop(%b : i32):
    "cf.br"(%b) [^loop] : (i32) -> ()
  }) : () -> ()

}) : () -> ()
