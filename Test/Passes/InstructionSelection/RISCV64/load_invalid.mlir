// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "foo"}> ({
    ^bb0(%a: !llvm.ptr):
        // i20 is not a whole number of bytes, so this load stays un-lowered.
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i20
        // CHECK: {{.*}} = "llvm.load"({{.*}}) <{"alignment" = 0 : i64}> : (!llvm.ptr) -> i20
        "test.test"(%val) : (i20) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
