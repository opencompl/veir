// RUN: not veir-opt %s -p=llvm-to-gmir,isel-br-riscv64 2>&1 | filecheck %s

// `llvm.switch` is not supported.
// CHECK: isel-br-riscv64: cannot lower a branch other than g_br or g_brcond
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i32) -> (i32), "sym_name" = "a"}> ({
    ^bb0(%v: i32):
        "llvm.switch"(%v, %v, %v) [^dflt, ^c0]
          <{"case_operand_segments" = array<i32: 1>, "case_values" = dense<[13]> : vector<1xi32>,
            "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i32, i32, i32) -> ()

    ^dflt(%x: i32):
        "func.return"(%x) : (i32) -> ()

    ^c0(%y: i32):
        "func.return"(%y) : (i32) -> ()
    }) : () -> ()
}) : () -> ()
