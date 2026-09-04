// RUN: VEIR_ROUNDTRIP

// Every registered cir operation, in the generic form ClangIR prints after
// `cir-opt -cir-flatten-cfg`. Flag properties keep ClangIR's spelling; a `false`
// flag comes back as `0 : i1`.
"builtin.module"() ({
  "cir.func"() <{calling_conv = 0 : i32, function_type = !cir.func<(!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>>, global_visibility = 0 : i32, linkage = 0 : i32, sym_name = "ops"}> ({
  ^bb0(%a : !cir.int<s, 32>, %u : !cir.int<u, 8>):
    %c1 = "cir.const"() <{value = #cir.int<1> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %cn = "cir.const"() <{value = #cir.int<-128> : !cir.int<s, 8>}> : () -> !cir.int<s, 8>
    %cu = "cir.const"() <{value = #cir.int<255> : !cir.int<u, 8>}> : () -> !cir.int<u, 8>
    %t = "cir.const"() <{value = #cir.bool<true> : !cir.bool}> : () -> !cir.bool
    %add = "cir.add"(%a, %c1) <{no_signed_wrap, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %sub = "cir.sub"(%add, %c1) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %mul = "cir.mul"(%sub, %c1) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %div = "cir.div"(%mul, %c1) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %rem = "cir.rem"(%div, %c1) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %and = "cir.and"(%u, %cu) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %or = "cir.or"(%and, %cu) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %xor = "cir.xor"(%or, %cu) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %shl = "cir.shift"(%rem, %u) <{isShiftleft}> : (!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>
    %shr = "cir.shift"(%shl, %u) : (!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>
    %not = "cir.not"(%t) : (!cir.bool) -> !cir.bool
    %neg = "cir.minus"(%shr) <{no_signed_wrap = false}> : (!cir.int<s, 32>) -> !cir.int<s, 32>
    %min = "cir.min"(%neg, %c1) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %max = "cir.max"(%min, %c1) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %lt = "cir.cmp"(%max, %c1) <{kind = 0 : i32}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.bool
    %sel = "cir.select"(%lt, %max, %c1) : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %narrow = "cir.cast"(%sel) <{kind = 27 : i32}> : (!cir.int<s, 32>) -> !cir.int<s, 8>
    %b = "cir.cast"(%narrow) <{kind = 28 : i32}> : (!cir.int<s, 8>) -> !cir.bool
    %i = "cir.cast"(%b) <{kind = 38 : i32}> : (!cir.bool) -> !cir.int<s, 32>
    "cir.brcond"(%b, %i, %cn)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 8>) -> ()
  ^bb1(%x : !cir.int<s, 32>):
    "cir.br"(%x)[^bb3] : (!cir.int<s, 32>) -> ()
  ^bb2(%y : !cir.int<s, 8>):
    "cir.unreachable"() : () -> ()
  ^bb3(%r : !cir.int<s, 32>):
    "cir.return"(%r) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
  "cir.func"() <{function_type = !cir.func<()>, sym_name = "nothing"}> ({
    "cir.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "cir.func"() <{"calling_conv" = 0 : i32, "function_type" = !cir.func<(!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>>, "global_visibility" = 0 : i32, "linkage" = 0 : i32, "sym_name" = "ops"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !cir.int<s, 32>, %{{.*}} : !cir.int<u, 8>):
// CHECK-NEXT: %{{.*}} = "cir.const"() <{"value" = #cir.int<1> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.const"() <{"value" = #cir.int<-128> : !cir.int<s, 8>}> : () -> !cir.int<s, 8>
// CHECK-NEXT: %{{.*}} = "cir.const"() <{"value" = #cir.int<255> : !cir.int<u, 8>}> : () -> !cir.int<u, 8>
// CHECK-NEXT: %{{.*}} = "cir.const"() <{"value" = #cir.bool<true> : !cir.bool}> : () -> !cir.bool
// CHECK-NEXT: %{{.*}} = "cir.add"(%{{.*}}, %{{.*}}) <{no_signed_wrap, "no_unsigned_wrap" = 0 : i1, "saturated" = 0 : i1}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.sub"(%{{.*}}, %{{.*}}) <{"no_signed_wrap" = 0 : i1, "no_unsigned_wrap" = 0 : i1, "saturated" = 0 : i1}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.mul"(%{{.*}}, %{{.*}}) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.div"(%{{.*}}, %{{.*}}) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.rem"(%{{.*}}, %{{.*}}) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.and"(%{{.*}}, %{{.*}}) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
// CHECK-NEXT: %{{.*}} = "cir.or"(%{{.*}}, %{{.*}}) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
// CHECK-NEXT: %{{.*}} = "cir.xor"(%{{.*}}, %{{.*}}) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
// CHECK-NEXT: %{{.*}} = "cir.shift"(%{{.*}}, %{{.*}}) <{isShiftleft}> : (!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.shift"(%{{.*}}, %{{.*}}) : (!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.not"(%{{.*}}) : (!cir.bool) -> !cir.bool
// CHECK-NEXT: %{{.*}} = "cir.minus"(%{{.*}}) <{"no_signed_wrap" = 0 : i1}> : (!cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.min"(%{{.*}}, %{{.*}}) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.max"(%{{.*}}, %{{.*}}) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.cmp"(%{{.*}}, %{{.*}}) <{"kind" = 0 : i32}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.bool
// CHECK-NEXT: %{{.*}} = "cir.select"(%{{.*}}, %{{.*}}, %{{.*}}) : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK-NEXT: %{{.*}} = "cir.cast"(%{{.*}}) <{"kind" = 27 : i32}> : (!cir.int<s, 32>) -> !cir.int<s, 8>
// CHECK-NEXT: %{{.*}} = "cir.cast"(%{{.*}}) <{"kind" = 28 : i32}> : (!cir.int<s, 8>) -> !cir.bool
// CHECK-NEXT: %{{.*}} = "cir.cast"(%{{.*}}) <{"kind" = 38 : i32}> : (!cir.bool) -> !cir.int<s, 32>
// CHECK-NEXT: "cir.brcond"(%{{.*}}, %{{.*}}, %{{.*}}) [^{{.*}}, ^{{.*}}] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 8>) -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !cir.int<s, 32>):
// CHECK-NEXT: "cir.br"(%{{.*}}) [^{{.*}}] : (!cir.int<s, 32>) -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !cir.int<s, 8>):
// CHECK-NEXT: "cir.unreachable"() : () -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !cir.int<s, 32>):
// CHECK-NEXT: "cir.return"(%{{.*}}) : (!cir.int<s, 32>) -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: "cir.func"() <{"function_type" = !cir.func<()>, "sym_name" = "nothing"}> ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "cir.return"() : () -> ()
// CHECK-NEXT: }) : () -> ()
