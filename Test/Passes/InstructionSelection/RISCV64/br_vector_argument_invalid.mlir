// RUN: not veir-opt %s -p=isel-br-riscv64 2>&1 | filecheck %s

// A vector does not fit a register.
// CHECK: isel-br-riscv64: a branch operand does not fit a register
"builtin.module"() ({
    "func.func"()  <{"function_type" = (vector<2xi32>) -> (vector<2xi32>), "sym_name" = "a"}> ({
    ^bb0(%a: vector<2xi32>):
        "llvm.br"(%a) [^bb1] : (vector<2xi32>) -> ()

    ^bb1(%b: vector<2xi32>):
        "func.return"(%b) : (vector<2xi32>) -> ()
    }) : () -> ()
}) : () -> ()
