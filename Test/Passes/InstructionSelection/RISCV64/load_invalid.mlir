// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr) -> ()}> ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i16
        // CHECK: {{.*}} = "llvm.load"({{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 0 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i16
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
