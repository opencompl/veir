// RUN: veir-opt %s | filecheck %s

// --mlir-print-op-generic --mlir-print-local-scope version of HEIR's tests/Dialect/ModArith/IR/syntax.mlir
// See https://github.com/google/heir/blob/main/tests/Dialect/ModArith/IR/syntax.mlir
// but with the tensor and dense constants versions of the mod_arith.constant operations removed
// TODO: re-introduce tensor and dense constants versions once VEIR supports them
"builtin.module"() ({
// CHECK: "builtin.module"
  "func.func"() <{function_type = () -> (), sym_name = "test_arith_syntax"}> ({
    %6 = "arith.constant"() <{value = 1 : i10}> : () -> i10
    %7 = "arith.constant"() <{value = 4 : i10}> : () -> i10
    %8 = "arith.constant"() <{value = 5 : i10}> : () -> i10
    %9 = "arith.constant"() <{value = 6 : i10}> : () -> i10
    %10 = "arith.constant"() <{value = 17 : i10}> : () -> i10
    %15 = "mod_arith.constant"() <{value = 12 : i8}> : () -> !mod_arith.int<17 : i10>
    %16 = "mod_arith.constant"() <{value = 0 : i4}> : () -> !mod_arith.int<17 : i10>
    %17 = "mod_arith.constant"() <{value = -1 : i4}> : () -> !mod_arith.int<17 : i10>   
    %21 = "mod_arith.encapsulate"(%7) : (i10) -> !mod_arith.int<17 : i10>
    %22 = "mod_arith.encapsulate"(%8) : (i10) -> !mod_arith.int<17 : i10>
    %23 = "mod_arith.encapsulate"(%9) : (i10) -> !mod_arith.int<17 : i10>
    %27 = "mod_arith.reduce"(%21) : (!mod_arith.int<17 : i10>) -> !mod_arith.int<17 : i10>
    %28 = "mod_arith.reduce"(%22) : (!mod_arith.int<17 : i10>) -> !mod_arith.int<17 : i10>
    %29 = "mod_arith.reduce"(%23) : (!mod_arith.int<17 : i10>) -> !mod_arith.int<17 : i10>
    %33 = "mod_arith.extract"(%27) : (!mod_arith.int<17 : i10>) -> i10
    %35 = "mod_arith.add"(%28, %29) : (!mod_arith.int<17 : i10>, !mod_arith.int<17 : i10>) -> !mod_arith.int<17 : i10>
    %37 = "mod_arith.sub"(%28, %29) : (!mod_arith.int<17 : i10>, !mod_arith.int<17 : i10>) -> !mod_arith.int<17 : i10>
    %39 = "mod_arith.mul"(%28, %29) : (!mod_arith.int<17 : i10>, !mod_arith.int<17 : i10>) -> !mod_arith.int<17 : i10>
    %41 = "mod_arith.mac"(%28, %29, %27) : (!mod_arith.int<17 : i10>, !mod_arith.int<17 : i10>, !mod_arith.int<17 : i10>) -> !mod_arith.int<17 : i10>
    %43 = "mod_arith.barrett_reduce"(%6) <{modulus = 17 : i64}> : (i10) -> i10
    %45 = "mod_arith.subifge"(%6, %10) : (i10, i10) -> i10
    %47 = "mod_arith.mod_switch"(%23) : (!mod_arith.int<17 : i10>) -> !mod_arith.int<7 : i4>
    %48 = "mod_arith.mod_switch"(%23) : (!mod_arith.int<17 : i10>) -> !mod_arith.int<31 : i10>
    %49 = "mod_arith.mod_switch"(%23) : (!mod_arith.int<17 : i10>) -> !mod_arith.int<18446744069414584321 : i65>
    "func.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{function_type = (!rns.rns<!mod_arith.int<17 : i10>, !mod_arith.int<257 : i10>, !mod_arith.int<509 : i10>>, !rns.rns<!mod_arith.int<17 : i10>, !mod_arith.int<257 : i10>, !mod_arith.int<509 : i10>>) -> (), sym_name = "test_rns_syntax"}> ({
  ^bb0(%arg2: !rns.rns<!mod_arith.int<17 : i10>, !mod_arith.int<257 : i10>, !mod_arith.int<509 : i10>>, %arg3: !rns.rns<!mod_arith.int<17 : i10>, !mod_arith.int<257 : i10>, !mod_arith.int<509 : i10>>):
    %3 = "mod_arith.add"(%arg2, %arg3) : (!rns.rns<!mod_arith.int<17 : i10>, !mod_arith.int<257 : i10>, !mod_arith.int<509 : i10>>, !rns.rns<!mod_arith.int<17 : i10>, !mod_arith.int<257 : i10>, !mod_arith.int<509 : i10>>) -> !rns.rns<!mod_arith.int<17 : i10>, !mod_arith.int<257 : i10>, !mod_arith.int<509 : i10>>
    %4 = "mod_arith.mod_switch"(%3) : (!rns.rns<!mod_arith.int<17 : i10>, !mod_arith.int<257 : i10>, !mod_arith.int<509 : i10>>) -> !mod_arith.int<2223821 : i32>
    %5 = "mod_arith.mod_switch"(%4) : (!mod_arith.int<2223821 : i32>) -> !rns.rns<!mod_arith.int<17 : i10>, !mod_arith.int<257 : i10>, !mod_arith.int<509 : i10>>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
