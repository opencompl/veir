// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i64
        
        "func.return"() : () -> ()
    }) : () -> ()
    
}) : () -> ()
