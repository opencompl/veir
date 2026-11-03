// RUN: VEIR_ROUNDTRIP

// ClangIR types and typed constants parse and print in their ClangIR spelling. The ops are
// still generic here; the cir dialect's own ops arrive in a later change.
"builtin.module"() ({
  "func.func"() <{function_type = (!cir.int<s, 32>, !cir.bool) -> !cir.int<u, 8>, sym_name = "types"}> ({
  ^bb0(%a : !cir.int<s, 32>, %b : !cir.bool):
    %0 = "test.test"(%a, %b) {fn = !cir.func<(!cir.int<s, 32>) -> !cir.int<s, 32>>, void_fn = !cir.func<()>} : (!cir.int<s, 32>, !cir.bool) -> !cir.int<u, 8>
    "test.test"() {i = #cir.int<-7> : !cir.int<s, 64>, b = #cir.bool<true> : !cir.bool} : () -> ()
    "func.return"(%0) : (!cir.int<u, 8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (!cir.int<s, 32>, !cir.bool) -> !cir.int<u, 8>, "sym_name" = "types"}> ({
// CHECK-NEXT:   ^{{.*}}([[A:%.*]] : !cir.int<s, 32>, [[B:%.*]] : !cir.bool):
// CHECK-NEXT:     [[R:%.*]] = "test.test"([[A]], [[B]]) {"fn" = !cir.func<(!cir.int<s, 32>) -> !cir.int<s, 32>>, "void_fn" = !cir.func<()>} : (!cir.int<s, 32>, !cir.bool) -> !cir.int<u, 8>
// CHECK-NEXT:     "test.test"() {"b" = #cir.bool<true> : !cir.bool, "i" = #cir.int<-7> : !cir.int<s, 64>} : () -> ()
// CHECK-NEXT:     "func.return"([[R]]) : (!cir.int<u, 8>) -> ()
