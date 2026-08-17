// RUN: veir-opt %s -p=cse | filecheck %s

// These operations were not part of CSE's former opcode whitelist. They are
// now admitted by their effect metadata and use the generic ordered-operand
// key.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32)>, sym_name = "foo"}> ({
  ^bb0(%arg0 : i32):
    %bitcast0 = "llvm.bitcast"(%arg0) : (i32) -> !llvm.byte<32>
    %bitcast1 = "llvm.bitcast"(%arg0) : (i32) -> !llvm.byte<32>
    %cast0 = "builtin.unrealized_conversion_cast"(%arg0) : (i32) -> i64
    %cast1 = "builtin.unrealized_conversion_cast"(%arg0) : (i32) -> i64
    "test.test"(%bitcast0, %bitcast1, %cast0, %cast1) :
      (!llvm.byte<32>, !llvm.byte<32>, i64, i64) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32):
    // CHECK-NEXT: %[[BITCAST:.*]] = "llvm.bitcast"(%{{.*}}) : (i32) -> !llvm.byte<32>
    // CHECK-NEXT: %[[CAST:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: "test.test"(%[[BITCAST]], %[[BITCAST]], %[[CAST]], %[[CAST]]) : (!llvm.byte<32>, !llvm.byte<32>, i64, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
