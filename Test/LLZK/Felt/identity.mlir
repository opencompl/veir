// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
^bb0():
  %0 = "felt.const"() <{"value" = #felt<const 42> : !felt.type}> : () -> !felt.type
  %1 = "felt.const"() <{"value" = #felt<const 7> : !felt.type<"bn254">}> : () -> !felt.type<"bn254">
  %2 = "felt.add"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %3 = "felt.sub"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %4 = "felt.mul"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %5 = "felt.pow"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %6 = "felt.div"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %7 = "felt.uintdiv"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %8 = "felt.sintdiv"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %9 = "felt.umod"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %10 = "felt.smod"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %11 = "felt.neg"(%0) : (!felt.type) -> !felt.type
  %12 = "felt.inv"(%0) : (!felt.type) -> !felt.type
  %13 = "felt.bit_and"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %14 = "felt.bit_or"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %15 = "felt.bit_xor"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %16 = "felt.bit_not"(%0) : (!felt.type) -> !felt.type
  %17 = "felt.shl"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
  %18 = "felt.shr"(%0, %0) : (!felt.type, !felt.type) -> !felt.type
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
// CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 42> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 7> : !felt.type<"bn254">}> : () -> !felt.type<"bn254">
// CHECK-NEXT:      %{{.*}} = "felt.add"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.sub"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.mul"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.pow"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.div"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.uintdiv"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.sintdiv"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.umod"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.smod"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.neg"(%{{.*}}) : (!felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.inv"(%{{.*}}) : (!felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.bit_and"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.bit_or"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.bit_xor"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.bit_not"(%{{.*}}) : (!felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.shl"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "felt.shr"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT: }) : () -> ()
