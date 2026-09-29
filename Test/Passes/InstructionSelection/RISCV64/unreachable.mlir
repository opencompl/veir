// RUN: veir-opt %s -p=isel-br-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() <{"function_type" = (i64, i1) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%a: i64, %b: i1):
        "llvm.cond_br"(%b, %a) [^bb1, ^bb2] <{"operandSegmentSizes" = array<i32: 1, 1, 0>}> : (i1, i64) -> ()

    ^bb1(%c: i64):
        "func.return"(%c) : (i64) -> ()

    ^bb2:
        "llvm.unreachable"() : () -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      func.func @a({{.*}}) -> i64 {
// CHECK:          "riscv_cf.bnez"
// CHECK:        ^{{[0-9]+}}():
// CHECK-NEXT:     "riscv_cf.unreachable"() : () -> ()
// CHECK-NEXT: }
// CHECK-NOT:  llvm.unreachable
