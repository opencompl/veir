// RUN: veir-opt %s -p=print-mod-arith-ranges | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, sym_name = "default_reduction"}> ({
  ^entry(%a : !mod_arith.int<12289 : i32>, %b : !mod_arith.int<12289 : i32>):
    // CHECK:      // dataflow.mod_arith.range block argument 0 = [0, 12288]
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 1 = [0, 12288]
    %c = "mod_arith.constant"() <{"value" = 46 : i32}> : () -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.constant result 0 = [46, 46]
    %small = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.constant result 0 = [3, 3]
    %add0 = "mod_arith.add"(%a, %c) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.add result 0 = [0, 12288]
    %add1 = "mod_arith.add"(%add0, %b) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.add result 0 = [0, 12288]
    %add2 = "mod_arith.add"(%add1, %a) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.add result 0 = [0, 12288]
    %out = "mod_arith.mul"(%add2, %small) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.mul result 0 = [0, 12288]
    "func.return"(%out) : (!mod_arith.int<12289 : i32>) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, sym_name = "no_reduction"}> ({
  ^entry(%a : !mod_arith.int<12289 : i32>, %b : !mod_arith.int<12289 : i32>):
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 0 = [0, 12288]
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 1 = [0, 12288]
    %c = "mod_arith.constant"() <{"value" = 46 : i32}> : () -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.constant result 0 = [46, 46]
    %small = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.constant result 0 = [3, 3]
    %add0 = "mod_arith.add"(%a, %c) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.add result 0 = [46, 12334]
    %add1 = "mod_arith.add"(%add0, %b) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.add result 0 = [46, 24622]
    %add2 = "mod_arith.add"(%add1, %a) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.add result 0 = [46, 36910]
    %out = "mod_arith.mul"(%add2, %small) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.mul result 0 = [138, 110730]
    "func.return"(%out) : (!mod_arith.int<12289 : i32>) -> ()
  }) : () -> ()

// Raw ModArith results are not bounded by their storage type.
  "func.func"() <{function_type = (!mod_arith.int<251 : i8>, !mod_arith.int<251 : i8>) -> (), sym_name = "unbounded_storage"}> ({
  ^entry(%a : !mod_arith.int<251 : i8>, %b : !mod_arith.int<251 : i8>):
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 0 = [0, 250]
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 1 = [0, 250]
    %sum = "mod_arith.add"(%a, %b) {"reduction" = "none"} : (!mod_arith.int<251 : i8>, !mod_arith.int<251 : i8>) -> !mod_arith.int<251 : i8>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.add result 0 = [0, 500]
    %product = "mod_arith.mul"(%a, %b) {"reduction" = "none"} : (!mod_arith.int<251 : i8>, !mod_arith.int<251 : i8>) -> !mod_arith.int<251 : i8>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.mul result 0 = [0, 62500]
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> (), sym_name = "subtraction"}> ({
  ^entry(%a : !mod_arith.int<17 : i32>, %b : !mod_arith.int<17 : i32>):
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 0 = [0, 16]
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 1 = [0, 16]
    %reduced = "mod_arith.sub"(%a, %b) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.sub result 0 = [0, 16]
    %raw = "mod_arith.sub"(%a, %b) {"reduction" = "none"} : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.sub result 0 = [1, 33]
    %unknown = "test.test"(%a) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range test.test result 0 = top
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1) -> (), sym_name = "cfg"}> ({
  ^entry(%cond : i1):
    %c2 = "mod_arith.constant"() <{"value" = 2 : i32}> : () -> !mod_arith.int<17 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.constant result 0 = [2, 2]
    %c7 = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<17 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.constant result 0 = [7, 7]
    "cf.cond_br"(%cond, %c2, %c7) [^left, ^right] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, !mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> ()
  ^left(%x : !mod_arith.int<17 : i32>):
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 0 = [2, 2]
    "cf.br"(%x) [^merge] : (!mod_arith.int<17 : i32>) -> ()
  ^right(%y : !mod_arith.int<17 : i32>):
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 0 = [7, 7]
    "cf.br"(%y) [^merge] : (!mod_arith.int<17 : i32>) -> ()
  ^merge(%phi : !mod_arith.int<17 : i32>):
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 0 = [2, 7]
    %c3 = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<17 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.constant result 0 = [3, 3]
    %out = "mod_arith.add"(%phi, %c3) {"reduction" = "none"} : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.add result 0 = [5, 10]
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = () -> (), sym_name = "backedge"}> ({
  ^entry:
    %c2 = "mod_arith.constant"() <{"value" = 2 : i32}> : () -> !mod_arith.int<17 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.constant result 0 = [2, 2]
    "cf.br"(%c2) [^loop] : (!mod_arith.int<17 : i32>) -> ()
  ^loop(%phi : !mod_arith.int<17 : i32>):
    // CHECK-NEXT: // dataflow.mod_arith.range block argument 0 = [2, 7]
    %c7 = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<17 : i32>
    // CHECK-NEXT: // dataflow.mod_arith.range mod_arith.constant result 0 = [7, 7]
    "cf.br"(%c7) [^loop] : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()
