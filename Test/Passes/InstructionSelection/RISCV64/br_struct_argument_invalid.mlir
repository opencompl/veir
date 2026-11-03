// RUN: not veir-opt %s -p=llvm-to-gmir,isel-br-riscv64 2>&1 | filecheck %s

// A struct does not fit a register.
// CHECK: isel-br-riscv64: a branch operand does not fit a register
"builtin.module"() ({
    "func.func"()  <{"function_type" = (!llvm.struct<(i32, i32)>) -> (!llvm.struct<(i32, i32)>), "sym_name" = "a"}> ({
    ^bb0(%a: !llvm.struct<(i32, i32)>):
        "llvm.br"(%a) [^bb1] : (!llvm.struct<(i32, i32)>) -> ()

    ^bb1(%b: !llvm.struct<(i32, i32)>):
        "func.return"(%b) : (!llvm.struct<(i32, i32)>) -> ()
    }) : () -> ()
}) : () -> ()
