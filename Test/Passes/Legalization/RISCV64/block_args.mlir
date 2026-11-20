// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

// `i64` and pointer block arguments are legal, and narrower integers are widened to `i64`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "br", function_type = !llvm.func<void (i8, i32, i64, !llvm.ptr)>}> ({
  ^bb0(%x : i8, %y : i32, %z : i64, %p : !llvm.ptr):
    // CHECK-LABEL: "sym_name" = "br"
    // CHECK:      ^{{.*}}(%[[X:.*]] : i8, %[[Y:.*]] : i32, %[[Z:.*]] : i64, %[[P:.*]] : !llvm.ptr):
    // CHECK-NEXT:   %[[EX:.*]] = "gmir.g_anyext"(%[[X]]) : (i8) -> i64
    // CHECK-NEXT:   %[[EY:.*]] = "gmir.g_anyext"(%[[Y]]) : (i32) -> i64
    // CHECK-NEXT:   "gmir.g_br"(%[[EX]], %[[EY]], %[[Z]], %[[P]]) [^[[BB:.*]]] : (i64, i64, i64, !llvm.ptr) -> ()
    "gmir.g_br"(%x, %y, %z, %p) [^bb1] : (i8, i32, i64, !llvm.ptr) -> ()
  ^bb1(%a : i8, %b : i32, %c : i64, %d : !llvm.ptr):
    // CHECK-NEXT: ^[[BB]](%[[A:.*]] : i64, %[[B:.*]] : i64, %[[C:.*]] : i64, %[[D:.*]] : !llvm.ptr):
    // CHECK-NEXT:   %[[TA:.*]] = "gmir.g_trunc"(%[[A]]) : (i64) -> i8
    // CHECK-NEXT:   %[[TB:.*]] = "gmir.g_trunc"(%[[B]]) : (i64) -> i32
    // CHECK-NEXT:   "test.test"(%[[TA]], %[[TB]], %[[C]], %[[D]])
    "test.test"(%a, %b, %c, %d) : (i8, i32, i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()

  // Each successor of a `g_brcond` gets the operands of its own segment widened.
  "llvm.func"() <{sym_name = "brcond", function_type = !llvm.func<void (i64, i8, i32)>}> ({
  ^bb0(%c : i64, %x : i8, %y : i32):
    // CHECK-LABEL: "sym_name" = "brcond"
    // CHECK:      %[[EX:.*]] = "gmir.g_anyext"(%{{.*}}) : (i8) -> i64
    // CHECK-NEXT: %[[EY:.*]] = "gmir.g_anyext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_brcond"(%{{.*}}, %[[EX]], %[[EY]]) [^[[BB1:.*]], ^[[BB2:.*]]]
    "gmir.g_brcond"(%c, %x, %y) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i64, i8, i32) -> ()
  ^bb1(%a : i8):
    // CHECK-NEXT: ^[[BB1]](%[[A:.*]] : i64):
    // CHECK-NEXT:   %{{.*}} = "gmir.g_trunc"(%[[A]]) : (i64) -> i8
    "test.test"(%a) : (i8) -> ()
    "llvm.return"() : () -> ()
  ^bb2(%b : i32):
    // CHECK:      ^[[BB2]](%[[B:.*]] : i64):
    // CHECK-NEXT:   %{{.*}} = "gmir.g_trunc"(%[[B]]) : (i64) -> i32
    "test.test"(%b) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()

  // A loop whose block holds only its branch passes the widened argument back to itself, without an
  // extension.
  "llvm.func"() <{sym_name = "self_loop", function_type = !llvm.func<void (i64, i8)>}> ({
  ^bb0(%c : i64, %x : i8):
    "gmir.g_br"(%x) [^bb1] : (i8) -> ()
  ^bb1(%a : i8):
    // CHECK-LABEL: "sym_name" = "self_loop"
    // CHECK:      ^[[BB:.*]](%[[A:.*]] : i64):
    // CHECK-NEXT:   "gmir.g_brcond"(%{{.*}}, %[[A]]) [^[[BB]], ^{{.*}}]
    "gmir.g_brcond"(%c, %a) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i64, i8) -> ()
  ^bb2:
    "llvm.return"() : () -> ()
  }) : () -> ()

  // Any branch that implements `BranchOpInterface` passes a widened value.
  "llvm.func"() <{sym_name = "llvm_br", function_type = !llvm.func<void (i8)>}> ({
  ^bb0(%x : i8):
    // CHECK-LABEL: "sym_name" = "llvm_br"
    // CHECK:      %[[EX:.*]] = "gmir.g_anyext"(%{{.*}}) : (i8) -> i64
    // CHECK-NEXT: "llvm.br"(%[[EX]]) [^[[BB:.*]]] : (i64) -> ()
    "llvm.br"(%x) [^bb1] : (i8) -> ()
  ^bb1(%a : i8):
    // CHECK-NEXT: ^[[BB]](%[[A:.*]] : i64):
    // CHECK-NEXT:   %{{.*}} = "gmir.g_trunc"(%[[A]]) : (i64) -> i8
    "test.test"(%a) : (i8) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
