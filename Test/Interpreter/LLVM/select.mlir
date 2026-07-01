// RUN: veir-interpret %s | filecheck %s

// `llvm.select` semantics: poison on the *non-selected* arm is ignored;
// poison on the selected arm, or on the condition, propagates.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i32, i32, i32, i32)}> ({
    %t = "llvm.mlir.constant"() <{ "value" = 1 : i1 }> : () -> i1
    %f = "llvm.mlir.constant"() <{ "value" = 0 : i1 }> : () -> i1
    %a = "llvm.mlir.constant"() <{ "value" = 3 : i32 }> : () -> i32
    %b = "llvm.mlir.constant"() <{ "value" = 5 : i32 }> : () -> i32

    %p32 = "llvm.mlir.poison"() : () -> i32
    %p1  = "llvm.mlir.poison"() : () -> i1

    // Concrete condition, concrete arms.
    %r1 = "llvm.select"(%t, %a, %b) : (i1, i32, i32) -> i32
    %r2 = "llvm.select"(%f, %a, %b) : (i1, i32, i32) -> i32

    // Poison on the unselected arm is blocked.
    %r3 = "llvm.select"(%t, %a, %p32) : (i1, i32, i32) -> i32
    %r4 = "llvm.select"(%f, %p32, %b) : (i1, i32, i32) -> i32

    // Poison on the selected arm propagates.
    %r5 = "llvm.select"(%t, %p32, %b) : (i1, i32, i32) -> i32
    %r6 = "llvm.select"(%f, %a, %p32) : (i1, i32, i32) -> i32

    // Poison condition produces poison.
    %r7 = "llvm.select"(%p1, %a, %b) : (i1, i32, i32) -> i32

    "func.return"(%r1, %r2, %r3, %r4, %r5, %r6, %r7)
      : (i32, i32, i32, i32, i32, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32, 0x00000005#32, 0x00000003#32, 0x00000005#32, poison, poison, poison]
