// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0(%arg0: i32, %arg1: i32, %arg2: i32, %sel: i1, %b0: i1, %b1: i1, %lo: i16, %hi: i16):
  %add = "comb.add"(%arg0, %arg1, %arg2) : (i32, i32, i32) -> i32
  %and = "comb.and"(%arg0, %arg1, %arg2) : (i32, i32, i32) -> i32
  %concat = "comb.concat"(%lo, %hi) : (i16, i16) -> i32
  %divs = "comb.divs"(%arg0, %arg1) : (i32, i32) -> i32
  %divu = "comb.divu"(%arg0, %arg1) : (i32, i32) -> i32
  %extract = "comb.extract"(%arg0) : (i32) -> i8
  %icmp = "comb.icmp"(%arg0, %arg1): (i32, i32) -> i1
  %mods = "comb.mods"(%arg0, %arg1) : (i32, i32) -> i32
  %modu = "comb.modu"(%arg0, %arg1) : (i32, i32) -> i32
  %mul = "comb.mul"(%arg0, %arg1, %arg2) : (i32, i32, i32) -> i32
  %mux = "comb.mux"(%sel, %arg0, %arg1) : (i1, i32, i32) -> i32
  %or = "comb.or"(%arg0, %arg1, %arg2) : (i32, i32, i32) -> i32
  %parity = "comb.parity"(%arg0) : (i32) -> i1
  %replicate = "comb.replicate"(%lo) : (i16) -> i32
  %reverse = "comb.reverse"(%arg0) : (i32) -> i32
  %shl = "comb.shl"(%arg0, %arg1) : (i32, i32) -> i32
  %shrs = "comb.shrs"(%arg0, %arg1) : (i32, i32) -> i32
  %shru = "comb.shru"(%arg0, %arg1) : (i32, i32) -> i32
  %sub = "comb.sub"(%arg0, %arg1) : (i32, i32) -> i32
  %tt = "comb.truth_table"(%b0): (i1) -> i1
  %xor = "comb.xor"(%arg0, %arg1, %arg2) : (i32, i32, i32) -> i32
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32, %{{.*}} : i32, %{{.*}} : i1, %{{.*}} : i1, %{{.*}} : i1, %{{.*}} : i16, %{{.*}} : i16):
// CHECK-NEXT:     %{{.*}} = "comb.add"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.and"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.concat"(%{{.*}}, %{{.*}}) : (i16, i16) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.divs"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.divu"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.extract"(%{{.*}}) : (i32) -> i8
// CHECK-NEXT:     %{{.*}} = "comb.icmp"(%{{.*}}, %{{.*}}) : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.mods"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.modu"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.mul"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.mux"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.or"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.parity"(%{{.*}}) : (i32) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.replicate"(%{{.*}}) : (i16) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.reverse"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.shl"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.shrs"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.shru"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "comb.truth_table"(%{{.*}}) : (i1) -> i1
// CHECK-NEXT:     %{{.*}} = "comb.xor"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
// CHECK-NEXT: }) : () -> ()
