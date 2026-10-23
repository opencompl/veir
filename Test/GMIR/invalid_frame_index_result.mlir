// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %result = "gmir.g_frame_index"() <{size = 8 : i64, alignment = 8 : i64}> : () -> i64
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_frame_index: Expected result to have !llvm.ptr type
