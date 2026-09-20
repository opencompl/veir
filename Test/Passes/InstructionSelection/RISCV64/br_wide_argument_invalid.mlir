// RUN: not veir-opt %s -p=isel-br-riscv64 2>&1 | filecheck %s

// A 128-bit value does not survive the round trip through a 64-bit register.
// CHECK: isel-br-riscv64: a branch operand does not fit a register
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i128) -> (i128), "sym_name" = "a"}> ({
    ^bb0(%a: i128):
        "llvm.br"(%a) [^bb1] : (i128) -> ()

    ^bb1(%b: i128):
        "func.return"(%b) : (i128) -> ()
    }) : () -> ()
}) : () -> ()
