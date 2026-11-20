// RUN: veir-opt %s -p=llvm-to-gmir,isel-br-riscv64 --print-op-generic | filecheck %s

// The casts back to the argument types stand in the order of the arguments.

// CHECK:      ^[[BB1:.*]](%[[A0:.*]] : !riscv.reg, %[[A1:.*]] : !riscv.reg, %[[A2:.*]] : !riscv.reg):
// CHECK-NEXT:   "builtin.unrealized_conversion_cast"(%[[A0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:   "builtin.unrealized_conversion_cast"(%[[A1]]) : (!riscv.reg) -> i64
// CHECK-NEXT:   "builtin.unrealized_conversion_cast"(%[[A2]]) : (!riscv.reg) -> !llvm.ptr
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i32, i64, !llvm.ptr) -> (i64), "sym_name" = "f"}> ({
    ^bb0(%x: i32, %y: i64, %z: !llvm.ptr):
        "llvm.br"(%x, %y, %z) [^bb1] : (i32, i64, !llvm.ptr) -> ()

    ^bb1(%a: i32, %b: i64, %c: !llvm.ptr):
        "func.return"(%b) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
