// RUN: not veir-opt %s -p=isel-br-riscv64 2>&1 | filecheck %s

// A 65-bit condition does not fit a 64-bit register, so the branch is not
// lowered: `bnez` would test only its low 64 bits.
// CHECK: isel-br-riscv64: a branch operand does not fit a register
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i65, i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%c: i65, %a: i64):
        "gmir.g_brcond"(%c, %a) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i65, i64) -> ()

    ^bb1(%b: i64):
        "func.return"(%b) : (i64) -> ()

    ^bb2:
        "func.return"(%a) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
