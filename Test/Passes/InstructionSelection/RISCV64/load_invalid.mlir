// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "foo"}> ({
    ^bb0(%a: !llvm.ptr):
        // i24 loads are not supported (only i64/i32/i16/i8), so this stays un-lowered.
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i24
        // CHECK: {{.*}} = "llvm.load"({{.*}}) <{"alignment" = 0 : i64}> : (!llvm.ptr) -> i24
        "test.test"(%val) : (i24) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
