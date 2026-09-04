// RUN: VEIR_UNREGISTERED_ROUNDTRIP

// ClangIR pieces VeIR does not model. A registered `cir` operation in an unmodelled
// variant (a pointer or float constant, a pointer comparison, a float select) is accepted
// and printed back verbatim; an unknown operation falls back to `builtin.unregistered`.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.ptr<!cir.int<s, 32>>) -> !cir.bool>, sym_name = "unmodelled"}> ({
  ^bb0(%p : !cir.ptr<!cir.int<s, 32>>):
    %null = "cir.const"() <{value = #cir.ptr<null> : !cir.ptr<!cir.int<s, 32>>}> : () -> !cir.ptr<!cir.int<s, 32>>
    %f = "cir.const"() <{value = #cir.fp<1.500000e+00> : !cir.double}> : () -> !cir.double
    %eq = "cir.cmp"(%p, %null) <{kind = 4 : i32}> : (!cir.ptr<!cir.int<s, 32>>, !cir.ptr<!cir.int<s, 32>>) -> !cir.bool
    %sel = "cir.select"(%eq, %f, %f) : (!cir.bool, !cir.double, !cir.double) -> !cir.double
    %g = "cir.get_global"() <{name = @counter}> : () -> !cir.ptr<!cir.int<s, 32>>
    "cir.return"(%eq) : (!cir.bool) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "cir.func"() <{"function_type" = !cir.func<(!cir.ptr<!cir.int<s, 32>>) -> !cir.bool>, "sym_name" = "unmodelled"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !cir.ptr<!cir.int<s, 32>>):
// CHECK-NEXT: %{{.*}} = "cir.const"() <{"value" = #cir.ptr<null> : !cir.ptr<!cir.int<s, 32>>}> : () -> !cir.ptr<!cir.int<s, 32>>
// CHECK-NEXT: %{{.*}} = "cir.const"() <{"value" = #cir.fp<1.500000e+00> : !cir.double}> : () -> !cir.double
// CHECK-NEXT: %{{.*}} = "cir.cmp"(%{{.*}}, %{{.*}}) <{"kind" = 4 : i32}> : (!cir.ptr<!cir.int<s, 32>>, !cir.ptr<!cir.int<s, 32>>) -> !cir.bool
// CHECK-NEXT: %{{.*}} = "cir.select"(%{{.*}}, %{{.*}}, %{{.*}}) : (!cir.bool, !cir.double, !cir.double) -> !cir.double
// CHECK-NEXT: %{{.*}} = "cir.get_global"() <{"name" = @counter}> : () -> !cir.ptr<!cir.int<s, 32>>
// CHECK-NEXT: "cir.return"(%{{.*}}) : (!cir.bool) -> ()
