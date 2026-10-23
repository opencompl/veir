// RUN: not veir-opt %s -p=isel-br-riscv64 2>&1 | filecheck %s

// A float has no meaning in an integer register.
// CHECK: isel-br-riscv64: a branch operand does not fit a register
"builtin.module"() ({
    "func.func"()  <{"function_type" = (f64) -> (f64), "sym_name" = "a"}> ({
    ^bb0(%a: f64):
        "llvm.br"(%a) [^bb1] : (f64) -> ()

    ^bb1(%b: f64):
        "func.return"(%b) : (f64) -> ()
    }) : () -> ()
}) : () -> ()
