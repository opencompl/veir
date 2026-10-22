// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    ^bb0():
      %a = "llvm.mlir.constant"() <{value = 100 : i16}> : () -> i16
      %b = "llvm.mlir.constant"() <{value = 42 : i16}> : () -> i16
      %add = "llvm.add"(%a, %b) <{overflowFlags = 3 : i32}> : (i16, i16) -> i16
      %sub = "llvm.sub"(%a, %b) : (i16, i16) -> i16
      %cmp = "llvm.icmp"(%a, %b) <{predicate = 4 : i64}> : (i16, i16) -> i1
      %sext = "llvm.sext"(%a) : (i16) -> i32
      %zext = "llvm.zext"(%a) <{nonNeg}> : (i16) -> i32
      %trunc = "llvm.trunc"(%a) <{overflowFlags = 1 : i32}> : (i16) -> i8
      %and = "llvm.and"(%a, %b) : (i16, i16) -> i16
      %or = "llvm.or"(%a, %b) <{isDisjoint}> : (i16, i16) -> i16
      %xor = "llvm.xor"(%a, %b) : (i16, i16) -> i16
      %mul = "llvm.mul"(%a, %b) <{overflowFlags = 2 : i32}> : (i16, i16) -> i16
      %sdiv = "llvm.sdiv"(%a, %b) <{isExact}> : (i16, i16) -> i16
      %udiv = "llvm.udiv"(%a, %b) : (i16, i16) -> i16
      %srem = "llvm.srem"(%a, %b) : (i16, i16) -> i16
      %urem = "llvm.urem"(%a, %b) : (i16, i16) -> i16
      %byte = "llvm.mlir.poison"() : () -> !llvm.byte<16>
      %truncByte = "llvm.trunc"(%byte) <{overflowFlags = 1 : i32}> : (!llvm.byte<16>) -> !llvm.byte<8>
      %toByte = "llvm.bitcast"(%a) : (i16) -> !llvm.byte<16>
      %truncToByte = "llvm.trunc"(%toByte) : (!llvm.byte<16>) -> !llvm.byte<8>
      %fromByte = "llvm.bitcast"(%truncToByte) : (!llvm.byte<8>) -> i8
      %byteToInt = "llvm.bitcast"(%byte) : (!llvm.byte<16>) -> i16
      %intToByte = "llvm.bitcast"(%byteToInt) : (i16) -> !llvm.byte<16>
      "test.test"(%add, %sub, %cmp, %sext, %zext, %trunc, %and, %or, %xor) : (i16, i16, i1, i32, i32, i8, i16, i16, i16) -> ()
      "test.test"(%mul, %sdiv, %udiv, %srem, %urem) : (i16, i16, i16, i16, i16) -> ()
      "test.test"(%truncByte) : (!llvm.byte<8>) -> ()
      "test.test"(%fromByte) : (i8) -> ()
      "test.test"(%intToByte) : (!llvm.byte<16>) -> ()
      "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "builtin.module"
// CHECK: [[A:%.*]] = "gmir.g_constant"() <{"value" = 100 : i16}> : () -> i16
// CHECK: "gmir.g_constant"() <{"value" = 42 : i16}> : () -> i16
// CHECK: "gmir.g_add"
// CHECK-SAME: "overflowFlags" = 3 : i32
// CHECK: "gmir.g_sub"
// CHECK: "gmir.g_icmp"
// CHECK-SAME: "predicate" = 4 : i64
// CHECK: "gmir.g_sext"(%{{.*}}) : (i16) -> i32
// CHECK: "gmir.g_zext"(%{{.*}}) <{nonNeg}> : (i16) -> i32
// CHECK: "gmir.g_trunc"(%{{.*}}) <{"overflowFlags" = 1 : i32}> : (i16) -> i8
// CHECK: "gmir.g_and"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16
// CHECK: "gmir.g_or"(%{{.*}}, %{{.*}}) <{isDisjoint}> : (i16, i16) -> i16
// CHECK: "gmir.g_xor"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16
// CHECK: "gmir.g_mul"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 2 : i32}> : (i16, i16) -> i16
// CHECK: "gmir.g_sdiv"(%{{.*}}, %{{.*}}) <{isExact}> : (i16, i16) -> i16
// CHECK: "gmir.g_udiv"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16
// CHECK: "gmir.g_srem"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16
// CHECK: "gmir.g_urem"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16
// CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<16>) -> i16
// CHECK: "gmir.g_trunc"(%{{.*}}) <{"overflowFlags" = 1 : i32}> : (i16) -> i8
// CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> !llvm.byte<8>
// Bitcasts between integers and bytes become casts, and the casts between them fold away.
// CHECK: [[T:%.*]] = "gmir.g_trunc"([[A]]) : (i16) -> i8
// Casting a byte to an integer and back freezes its poison bits, so these casts stay.
// CHECK: [[I:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.byte<16>) -> i16
// CHECK: [[B:%.*]] = "builtin.unrealized_conversion_cast"([[I]]) : (i16) -> !llvm.byte<16>
// CHECK: "test.test"([[T]]) : (i8) -> ()
// CHECK: "test.test"([[B]]) : (!llvm.byte<16>) -> ()
