// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv-combine > %t
// RUN: veir-interpret %t | filecheck %s

// Boolean selects need no extension. Exercise both condition values, both
// arm orders, and both spellings of true, using block arguments to keep the
// constant-condition rewrite from bypassing the select-to-extension rules.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i1, i1, i1, i1, i1, i1, i1, i1)}> ({
    %true = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %false = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    "cf.br"(%true, %false) [^test] : (i1, i1) -> ()
  ^test(%t: i1, %f: i1):
    %one = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %minusOne = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %zero = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    %a = "llvm.select"(%t, %one, %zero) : (i1, i1, i1) -> i1
    %b = "llvm.select"(%f, %one, %zero) : (i1, i1, i1) -> i1
    %c = "llvm.select"(%t, %zero, %one) : (i1, i1, i1) -> i1
    %d = "llvm.select"(%f, %zero, %one) : (i1, i1, i1) -> i1
    %e = "llvm.select"(%t, %minusOne, %zero) : (i1, i1, i1) -> i1
    %fval = "llvm.select"(%f, %minusOne, %zero) : (i1, i1, i1) -> i1
    %g = "llvm.select"(%t, %zero, %minusOne) : (i1, i1, i1) -> i1
    %h = "llvm.select"(%f, %zero, %minusOne) : (i1, i1, i1) -> i1
    "func.return"(%a, %b, %c, %d, %e, %fval, %g, %h) : (i1, i1, i1, i1, i1, i1, i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1#1, 0x0#1, 0x0#1, 0x1#1, 0x1#1, 0x0#1, 0x0#1, 0x1#1]
