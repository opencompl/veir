// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
^bb0():
    // --- Identity and annihilation patterns ---
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %x = "test.test"() : () -> i32
    // CHECK:      %{{.*}} = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %[[X:.*]] = "test.test"() : () -> i32

    // sub x - 0 => x
    %sub_zero = "llvm.sub"(%x, %zero) : (i32, i32) -> i32
    "test.test"(%sub_zero) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

}) : () -> ()
