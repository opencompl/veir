// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
^bb0():
    // --- Identity and annihilation patterns ---
    %x = "test.test"() : () -> i32
    // CHECK: %[[X:.*]] = "test.test"() : () -> i32

    // or x | x => x
    %or_self = "llvm.or"(%x, %x) : (i32, i32) -> i32
    "test.test"(%or_self) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

}) : () -> ()
