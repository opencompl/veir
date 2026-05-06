// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^4():
  %a = "arith.constant"() <{ "value" = 13 : i32 }> : () -> i32
  %b = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %c = "arith.constant"() <{ "value" = 42 : i32 }> : () -> i32
  %true = "arith.constant"() <{ "value" = 1 : i1 }> : () -> i1
  %add1 = "comb.add"(%a) : (i32) -> i32
  %add2 = "comb.add"(%a, %b) : (i32, i32) -> i32
  %add3 = "comb.add"(%a, %b, %c) : (i32, i32, i32) -> i32
  %and1 = "comb.and"(%a) : (i32) -> i32
  %and2 = "comb.and"(%a, %b) : (i32, i32) -> i32
  %and3 = "comb.and"(%a, %b, %c) : (i32, i32, i32) -> i32
  %concat0 = "comb.concat"() : () -> i0
  %concat1 = "comb.concat"(%a) : (i32) -> i32
  %concat2 = "comb.concat"(%a, %b) : (i32, i32) -> i64
  %concat3 = "comb.concat"(%a, %b, %c) : (i32, i32, i32) -> i96
  %divs = "comb.divs"(%a, %b) : (i32, i32) -> i32
  %divu = "comb.divu"(%a, %b) : (i32, i32) -> i32
  %extract = "comb.extract"(%a) <{ "lowBit" = 2 : i32 }> : (i32) -> i8
  %icmp0 = "comb.icmp"(%a, %b) <{ "predicate" = 0 : i64 }> : (i32, i32) -> i1
  %icmp1 = "comb.icmp"(%a, %b) <{ "predicate" = 1 : i64 }> : (i32, i32) -> i1
  %icmp2 = "comb.icmp"(%a, %b) <{ "predicate" = 2 : i64 }> : (i32, i32) -> i1
  %icmp3 = "comb.icmp"(%a, %b) <{ "predicate" = 3 : i64 }> : (i32, i32) -> i1
  %icmp4 = "comb.icmp"(%a, %b) <{ "predicate" = 4 : i64 }> : (i32, i32) -> i1
  %icmp5 = "comb.icmp"(%a, %b) <{ "predicate" = 5 : i64 }> : (i32, i32) -> i1
  %icmp6 = "comb.icmp"(%a, %b) <{ "predicate" = 6 : i64 }> : (i32, i32) -> i1
  %icmp7 = "comb.icmp"(%a, %b) <{ "predicate" = 7 : i64 }> : (i32, i32) -> i1
  %icmp8 = "comb.icmp"(%a, %b) <{ "predicate" = 8 : i64 }> : (i32, i32) -> i1
  %icmp9 = "comb.icmp"(%a, %b) <{ "predicate" = 9 : i64 }> : (i32, i32) -> i1
  %icmp10 = "comb.icmp"(%a, %b) <{ "predicate" = 10 : i64 }> : (i32, i32) -> i1
  %icmp11 = "comb.icmp"(%a, %b) <{ "predicate" = 11 : i64 }> : (i32, i32) -> i1
  %icmp12 = "comb.icmp"(%a, %b) <{ "predicate" = 12 : i64 }> : (i32, i32) -> i1
  %icmp13 = "comb.icmp"(%a, %b) <{ "predicate" = 13 : i64 }> : (i32, i32) -> i1
  %mods = "comb.mods"(%a, %b) : (i32, i32) -> i32
  %modu = "comb.modu"(%a, %b) : (i32, i32) -> i32
  %mul1 = "comb.mul"(%a) : (i32) -> i32
  %mul2 = "comb.mul"(%a, %b) : (i32, i32) -> i32
  %mul3 = "comb.mul"(%a, %b, %c) : (i32, i32, i32) -> i32
  %mux = "comb.mux"(%true, %a, %b) : (i1, i32, i32) -> i32
  %or1 = "comb.or"(%a) : (i32) -> i32
  %or2 = "comb.or"(%a, %b) : (i32, i32) -> i32
  %or3 = "comb.or"(%a, %b, %c) : (i32, i32, i32) -> i32
  %parity = "comb.parity"(%a) : (i32) -> i1
  %replicate = "comb.replicate"(%a) : (i32) -> i64
  %reverse = "comb.reverse"(%a) : (i32) -> i32
  %shl = "comb.shl"(%a, %b) : (i32, i32) -> i32
  %shrs = "comb.shrs"(%a, %b) : (i32, i32) -> i32
  %shru = "comb.shru"(%a, %b) : (i32, i32) -> i32
  %sub = "comb.sub"(%a, %b) : (i32, i32) -> i32
  %xor1 = "comb.xor"(%a) : (i32) -> i32
  %xor2 = "comb.xor"(%a, %b) : (i32, i32) -> i32
  %xor3 = "comb.xor"(%a, %b, %c) : (i32, i32, i32) -> i32
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %{{.*}} = "arith.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:     %{{.*}} = "arith.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK-NEXT:     %{{.*}} = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
// CHECK-NEXT:     %{{.*}} = "arith.constant"() <{"value" = 1 : i1}> : () -> i1
// CHECK-NEXT:     %{{.*}} = "comb.add"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.add"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.and"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.and"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.concat"() : () -> i0
// CHECK-NEXT:     %{{.*}} = "comb.concat"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.concat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i64
// CHECK-NEXT:     %{{.*}} = "comb.concat"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i96
// CHECK-NEXT:     %{{.*}} = "comb.divs"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.divu"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.extract"(%{{.*}}) <{"lowBit" = 2 : i32}> : (i32) -> i8
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 3 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 4 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 5 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 6 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 7 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 8 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 9 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 10 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 11 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 12 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 13 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.mods"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.modu"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.mul"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.mul"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.mul"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.mux"(%8, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.or"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.or"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.parity"(%{{.*}}) : (i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.replicate"(%{{.*}}) : (i32) -> i64
// CHECK-NEXT:     %{{.*}} = "comb.reverse"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.shl"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.shrs"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.shru"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.xor"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.xor"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.xor"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT: }) : () -> ()
