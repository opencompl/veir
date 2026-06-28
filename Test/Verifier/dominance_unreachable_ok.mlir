// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_AGREE

// Like LLVM/MLIR, the dominance check is skipped for unreachable blocks. ^dead
// has no predecessors (^entry returns), so its use of %v imposes no dominance
// requirement and the program verifies.

"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "main"}> ({
  ^entry():
    %v = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    "func.return"(%v) : (i32) -> ()
  ^dead():
    "func.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[V:.*]] = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT: "func.return"(%[[V]]) : (i32) -> ()
// CHECK:      "func.return"(%[[V]]) : (i32) -> ()
