// RUN: not veir-opt %s -p=isel-br-riscv64 2>&1 | filecheck %s

// A 65-bit value cannot be passed through a 64-bit register, on either
// successor of a conditional branch.
// CHECK: isel-br-riscv64: a branch operand does not fit a register
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i1, i64, i65) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%c: i1, %a: i64, %w: i65):
        "llvm.cond_br"(%c, %a, %w) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i65) -> ()

    ^bb1(%b: i64):
        "func.return"(%b) : (i64) -> ()

    ^bb2(%d: i65):
        "func.return"(%a) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
