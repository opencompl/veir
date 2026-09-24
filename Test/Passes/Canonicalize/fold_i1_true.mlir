// RUN: veir-opt %s -p=canonicalize | filecheck %s

// A fold that produces an all-ones `i1` materializes it as `true` (value 1),
// the only form the parser produces; the verifier rejects the value -1.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (i1, i1), sym_name = "f"}> ({
    %a = "arith.constant"() <{value = 5 : i32}> : () -> i32
    %t1 = "arith.cmpi"(%a, %a) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %b = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %t2 = "llvm.icmp"(%b, %b) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "func.return"(%t1, %t2) : (i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "arith.constant"() <{"value" = true}> : () -> i1
// CHECK: "llvm.mlir.constant"() <{"value" = true}> : () -> i1
