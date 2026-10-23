// RUN: veir-opt %s -p=isel-br-riscv64{strict=false} --print-op-generic | filecheck %s

// With `strict=false`, a branch that is left alone keeps all of its targets, even
// one that a lowered branch also reaches: the `llvm.cond_br` cannot be lowered
// because of `^bb2`, so `^bb1` keeps its type, and so does the `llvm.br` to it.

// CHECK:      "llvm.cond_br"(%{{.*}}, %{{.*}}, %{{.*}}) [^[[BB1:.*]], ^[[BB2:.*]]]
// CHECK-NEXT: ^[[BB1]](%{{.*}} : i32):
// CHECK-NEXT:   "func.return"
// CHECK-NEXT: ^[[BB2]](%{{.*}} : i128):
// CHECK-NEXT:   "llvm.br"(%{{.*}}) [^[[BB1]]] : (i32) -> ()
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i1, i32, i128) -> (i32), "sym_name" = "f"}> ({
    ^bb0(%c: i1, %a: i32, %w: i128):
        "llvm.cond_br"(%c, %a, %w) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i128) -> ()
    ^bb1(%p: i32):
        "func.return"(%p) : (i32) -> ()
    ^bb2(%q: i128):
        "llvm.br"(%a) [^bb1] : (i32) -> ()
    }) : () -> ()
}) : () -> ()
