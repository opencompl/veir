// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
^bb0():
    // --- Identity and annihilation patterns ---
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %x = "test.test"() : () -> i32
    // CHECK:      %{{.*}} = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %[[X:.*]] = "test.test"() : () -> i32

   // and x & 0 => 0
    %and_zero = "llvm.and"(%x, %zero) : (i32, i32) -> i32
    "test.test"(%and_zero) : (i32) -> ()
    // CHECK-NEXT: %[[AND_ZERO:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: "test.test"(%[[AND_ZERO]]) : (i32) -> ()

}) : () -> ()
