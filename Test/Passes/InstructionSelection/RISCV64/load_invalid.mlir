// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "foo"}> ({
    ^bb0(%a: !llvm.ptr):
        // i16 loads are not supported (only i64/i32/i8), so this stays un-lowered.
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i16
        // CHECK: {{.*}} = "llvm.load"({{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 0 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i16
        "test.test"(%val) : (i16) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
