// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "foo"}> ({
    ^bb0(%a: !llvm.ptr):
        // Non-native widths remain un-lowered.
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i24
        // CHECK: {{.*}} = "llvm.load"({{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 0 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i24
        "test.test"(%val) : (i24) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
