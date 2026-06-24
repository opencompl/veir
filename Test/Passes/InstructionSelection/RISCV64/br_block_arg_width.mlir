// RUN: veir-opt %s -p=isel-br-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() <{"function_type" = (i32, i64) -> (i32), "sym_name" = "block_arg"}> ({
    ^bb0(%a: i32, %n: i64):
        "llvm.br"(%a) [^bb1] : (i32) -> ()

    ^bb1(%b: i32):
        %c = "llvm.add"(%b, %b) : (i32, i32) -> i32
        "func.return"(%c) : (i32) -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i64) -> i32, "sym_name" = "block_arg"}> ({
// CHECK-NEXT:   ^{{[0-9]+}}([[A:%[a-z0-9_]+]] : i32, %{{[a-z0-9_]+}} : i64):
// CHECK-NEXT:     [[RA:%[a-z0-9]+]] = "builtin.unrealized_conversion_cast"([[A]]) : (i32) -> !riscv.reg
// CHECK-NEXT:     "riscv_cf.branch"([[RA]]) [^[[BB1:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:   ^[[BB1]]([[B:%[a-z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:     [[RB:%[a-z0-9]+]] = "builtin.unrealized_conversion_cast"([[B]]) : (!riscv.reg) -> i32
// CHECK-NEXT:     [[ADD:%[a-z0-9]+]] = "llvm.add"([[RB]], [[RB]]) : (i32, i32) -> i32
// CHECK-NEXT:     "func.return"([[ADD]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
