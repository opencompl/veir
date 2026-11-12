// RUN: veir-opt %s -p=isel-br-riscv64 | filecheck %s

// The arguments of an entry block are the parameters of its function, so the
// pass leaves them alone and converts only the block that is branched to.

// CHECK:      func.func @f([[X:%[a-z0-9_]+]]: i32, [[Y:%[a-z0-9_]+]]: i64) -> i64 {
// CHECK-NEXT:   [[RX:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[X]]) : (i32) -> !riscv.reg
// CHECK-NEXT:   [[RY:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[Y]]) : (i64) -> !riscv.reg
// CHECK-NEXT:   "riscv_cf.branch"([[RX]], [[RY]]) [^[[BB1:[0-9]+]]] : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:   ^[[BB1]](%{{[a-z0-9_]+}} : !riscv.reg, %{{[a-z0-9_]+}} : !riscv.reg):
"builtin.module"() ({
    "func.func"() <{"function_type" = (i32, i64) -> (i64), "sym_name" = "f"}> ({
    ^bb0(%x: i32, %y: i64):
        "gmir.g_br"(%x, %y) [^bb1] : (i32, i64) -> ()

    ^bb1(%a: i32, %b: i64):
        "func.return"(%b) : (i64) -> ()
    }) : () -> ()

    "func.func"() <{"function_type" = () -> (i64), "sym_name" = "g"}> ({
    ^bb0():
        %c0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
        %c1 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
        %r = "func.call"(%c0, %c1) <{callee = @f}> : (i32, i64) -> i64
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      func.func @g() -> i64 {
// CHECK:        "func.call"(%{{[a-z0-9_]+}}, %{{[a-z0-9_]+}}) <{"callee" = @f}> : (i32, i64) -> i64
