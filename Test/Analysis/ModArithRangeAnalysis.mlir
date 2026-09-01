// RUN: split-file %s %t
// RUN: veir-opt %t/default.mlir -p=print-mod-arith-ranges | filecheck %s --check-prefix=DEFAULT
// RUN: veir-opt %t/no-reduction.mlir -p=print-mod-arith-ranges | filecheck %s --check-prefix=NONE
// RUN: veir-opt %t/storage-overflow.mlir -p=print-mod-arith-ranges | filecheck %s --check-prefix=STORAGE
// RUN: veir-opt %t/subtraction.mlir -p=print-mod-arith-ranges | filecheck %s --check-prefix=SUB
// RUN: veir-opt %t/cfg.mlir -p=print-mod-arith-ranges | filecheck %s --check-prefix=CFG
// RUN: veir-opt %t/backedge.mlir -p=print-mod-arith-ranges | filecheck %s --check-prefix=BACKEDGE
// RUN: veir-opt %t/widening.mlir -p=print-mod-arith-ranges | filecheck %s --check-prefix=WIDEN

//--- default.mlir

// DEFAULT:      // mod_arith.range block argument 0 = [0, 12288]
// DEFAULT-NEXT: // mod_arith.range block argument 1 = [0, 12288]
// DEFAULT-NEXT: // mod_arith.range mod_arith.constant result 0 = [46, 46]
// DEFAULT-NEXT: // mod_arith.range mod_arith.constant result 0 = [3, 3]
// DEFAULT-NEXT: // mod_arith.range mod_arith.add result 0 = [0, 12288]
// DEFAULT-NEXT: // mod_arith.range mod_arith.add result 0 = [0, 12288]
// DEFAULT-NEXT: // mod_arith.range mod_arith.add result 0 = [0, 12288]
// DEFAULT-NEXT: // mod_arith.range mod_arith.mul result 0 = [0, 12288]

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, sym_name = "default_reduction"}> ({
  ^entry(%a : !mod_arith.int<12289 : i32>, %b : !mod_arith.int<12289 : i32>):
    %c = "mod_arith.constant"() <{"value" = 46 : i32}> : () -> !mod_arith.int<12289 : i32>
    %small = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<12289 : i32>
    %add0 = "mod_arith.add"(%a, %c) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add1 = "mod_arith.add"(%add0, %b) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add2 = "mod_arith.add"(%add1, %a) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %out = "mod_arith.mul"(%add2, %small) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    "func.return"(%out) : (!mod_arith.int<12289 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

//--- no-reduction.mlir

// NONE:      // mod_arith.range block argument 0 = [0, 12288]
// NONE-NEXT: // mod_arith.range block argument 1 = [0, 12288]
// NONE-NEXT: // mod_arith.range mod_arith.constant result 0 = [46, 46]
// NONE-NEXT: // mod_arith.range mod_arith.constant result 0 = [3, 3]
// NONE-NEXT: // mod_arith.range mod_arith.add result 0 = [46, 12334]
// NONE-NEXT: // mod_arith.range mod_arith.add result 0 = [46, 24622]
// NONE-NEXT: // mod_arith.range mod_arith.add result 0 = [46, 36910]
// NONE-NEXT: // mod_arith.range mod_arith.mul result 0 = [138, 110730]

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, sym_name = "no_reduction"}> ({
  ^entry(%a : !mod_arith.int<12289 : i32>, %b : !mod_arith.int<12289 : i32>):
    %c = "mod_arith.constant"() <{"value" = 46 : i32}> : () -> !mod_arith.int<12289 : i32>
    %small = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<12289 : i32>
    %add0 = "mod_arith.add"(%a, %c) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add1 = "mod_arith.add"(%add0, %b) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add2 = "mod_arith.add"(%add1, %a) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %out = "mod_arith.mul"(%add2, %small) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    "func.return"(%out) : (!mod_arith.int<12289 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

//--- storage-overflow.mlir

// Raw ModArith operations still produce values of their unsigned storage type.
// When a mathematical interval can overflow i8, use the full i8 range.
// STORAGE:      // mod_arith.range block argument 0 = [0, 250]
// STORAGE-NEXT: // mod_arith.range block argument 1 = [0, 250]
// STORAGE-NEXT: // mod_arith.range mod_arith.add result 0 = [0, 255]
// STORAGE-NEXT: // mod_arith.range mod_arith.mul result 0 = [0, 255]

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<251 : i8>, !mod_arith.int<251 : i8>) -> (), sym_name = "storage_overflow"}> ({
  ^entry(%a : !mod_arith.int<251 : i8>, %b : !mod_arith.int<251 : i8>):
    %sum = "mod_arith.add"(%a, %b) {"reduction" = "none"} : (!mod_arith.int<251 : i8>, !mod_arith.int<251 : i8>) -> !mod_arith.int<251 : i8>
    %product = "mod_arith.mul"(%a, %b) {"reduction" = "none"} : (!mod_arith.int<251 : i8>, !mod_arith.int<251 : i8>) -> !mod_arith.int<251 : i8>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

//--- subtraction.mlir

// SUB:      // mod_arith.range block argument 0 = [0, 16]
// SUB-NEXT: // mod_arith.range block argument 1 = [0, 16]
// SUB-NEXT: // mod_arith.range mod_arith.sub result 0 = [0, 16]
// SUB-NEXT: // mod_arith.range mod_arith.sub result 0 = [1, 33]
// SUB-NEXT: // mod_arith.range test.test result 0 = [0, 4294967295]

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> (), sym_name = "subtraction"}> ({
  ^entry(%a : !mod_arith.int<17 : i32>, %b : !mod_arith.int<17 : i32>):
    %reduced = "mod_arith.sub"(%a, %b) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %raw = "mod_arith.sub"(%a, %b) {"reduction" = "none"} : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %unknown = "test.test"(%a) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

//--- cfg.mlir

// CFG:      // mod_arith.range mod_arith.constant result 0 = [2, 2]
// CFG-NEXT: // mod_arith.range mod_arith.constant result 0 = [7, 7]
// CFG-NEXT: // mod_arith.range block argument 0 = [2, 2]
// CFG-NEXT: // mod_arith.range block argument 0 = [7, 7]
// CFG-NEXT: // mod_arith.range block argument 0 = [2, 7]
// CFG-NEXT: // mod_arith.range mod_arith.constant result 0 = [3, 3]
// CFG-NEXT: // mod_arith.range mod_arith.add result 0 = [5, 10]

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "cfg"}> ({
  ^entry(%cond : i1):
    %c2 = "mod_arith.constant"() <{"value" = 2 : i32}> : () -> !mod_arith.int<17 : i32>
    %c7 = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<17 : i32>
    "cf.cond_br"(%cond, %c2, %c7) [^left, ^right] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, !mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> ()
  ^left(%x : !mod_arith.int<17 : i32>):
    "cf.br"(%x) [^merge] : (!mod_arith.int<17 : i32>) -> ()
  ^right(%y : !mod_arith.int<17 : i32>):
    "cf.br"(%y) [^merge] : (!mod_arith.int<17 : i32>) -> ()
  ^merge(%phi : !mod_arith.int<17 : i32>):
    %c3 = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<17 : i32>
    %out = "mod_arith.add"(%phi, %c3) {"reduction" = "none"} : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

//--- backedge.mlir

// BACKEDGE:      // mod_arith.range mod_arith.constant result 0 = [2, 2]
// BACKEDGE-NEXT: // mod_arith.range block argument 0 = [2, 7]
// BACKEDGE-NEXT: // mod_arith.range mod_arith.constant result 0 = [7, 7]

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "backedge"}> ({
  ^entry:
    %c2 = "mod_arith.constant"() <{"value" = 2 : i32}> : () -> !mod_arith.int<17 : i32>
    "cf.br"(%c2) [^loop] : (!mod_arith.int<17 : i32>) -> ()
  ^loop(%phi : !mod_arith.int<17 : i32>):
    %c7 = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<17 : i32>
    "cf.br"(%c7) [^loop] : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

//--- widening.mlir

// A raw loop-carried increment creates the infinite ascending chain
// [0, 0] -> [0, 1] -> [0, 2] -> ... without widening.
// WIDEN:      // mod_arith.range mod_arith.constant result 0 = [0, 0]
// WIDEN-NEXT: // mod_arith.range mod_arith.constant result 0 = [1, 1]
// WIDEN-NEXT: // mod_arith.range block argument 0 = [0, 4294967295]
// WIDEN-NEXT: // mod_arith.range mod_arith.add result 0 = [0, 4294967295]

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "widening"}> ({
  ^entry:
    %c0 = "mod_arith.constant"() <{"value" = 0 : i32}> : () -> !mod_arith.int<17 : i32>
    %c1 = "mod_arith.constant"() <{"value" = 1 : i32}> : () -> !mod_arith.int<17 : i32>
    "cf.br"(%c0) [^loop] : (!mod_arith.int<17 : i32>) -> ()
  ^loop(%phi : !mod_arith.int<17 : i32>):
    %next = "mod_arith.add"(%phi, %c1) {"reduction" = "none"}
      : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    "cf.br"(%next) [^loop] : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()
