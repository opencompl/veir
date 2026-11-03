// RUN: VEIR_ROUNDTRIP
// RUN: %if mlir-min-23 %{ MLIR_ROUNDTRIP %}

"builtin.module"() ({
  "func.func"() <{function_type = (vector<4x!llvm.byte<8>>, !llvm.byte<8>, i32) -> vector<4x!llvm.byte<8>>, sym_name = "bytes"}> ({
  ^bb0(%v: vector<4x!llvm.byte<8>>, %x: !llvm.byte<8>, %i: i32):
    %r = "llvm.insertelement"(%v, %x, %i) : (vector<4x!llvm.byte<8>>, !llvm.byte<8>, i32) -> vector<4x!llvm.byte<8>>
    "func.return"(%r) : (vector<4x!llvm.byte<8>>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.insertelement"({{.*}}) : (vector<4x!llvm.byte<8>>, !llvm.byte<8>, i32) -> vector<4x!llvm.byte<8>>
