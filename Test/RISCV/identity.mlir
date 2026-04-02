// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  ^bb0():
    %0 = "riscv.li"() <{ "value" = 13 : i64 }>  : () -> !reg
    %1 = "riscv.li"() <{ "value" = 17 : i64 }> : () -> !reg
    // Immediate load 
    %2 = "riscv.lui"() <{"value" = 13 : i20}> : () -> !reg
    %3 = "riscv.auipc"(%0) <{"value" = 13 : i20}> : (!reg) -> !reg
    // Immediate operations 
    %4 = "riscv.addi"(%0) <{"value" = 5 : i12}> : (!reg) -> !reg
    %5 = "riscv.slti"(%0) <{"value" = 7 : i12}> : (!reg) -> !reg
    %6 = "riscv.sltiu"(%0) <{"value" = 11 : i12}> : (!reg) -> !reg
    %7 = "riscv.andi"(%0) <{"value" = 13 : i12}> : (!reg) -> !reg
    %8 = "riscv.ori"(%0) <{"value" = 17 : i12}> : (!reg) -> !reg
    %9 = "riscv.xori"(%0) <{"value" = 23 : i12}> : (!reg) -> !reg
    %10 = "riscv.addiw"(%0) <{"value" = 29 : i12}> : (!reg) -> !reg
    %11 = "riscv.slli"(%0) <{"value" = 31 : i6}> : (!reg) -> !reg
    %12 = "riscv.srli"(%0) <{"value" = 33 : i6}> : (!reg) -> !reg
    %13 = "riscv.srai"(%0) <{"value" = 37 : i6}> : (!reg) -> !reg
    %14 = "riscv.slliw"(%0) <{ "value" = 13 : i5 }> : (!reg) -> !reg
    %15 = "riscv.srliw"(%0) <{ "value" = 17 : i5 }> : (!reg) -> !reg
    %16 = "riscv.sraiw"(%0) <{ "value" = 19 : i5 }> : (!reg) -> !reg
    %17 = "riscv.slliuw"(%0) <{"value" = 13 : i6 }> : (!reg) -> !reg
    %18 = "riscv.roriw"(%0) <{"value" = 13 : i5 }> : (!reg) -> !reg
    %19 = "riscv.rori"(%0) <{"value" = 13 : i6 }> : (!reg) -> !reg
    %20 = "riscv.bclri"(%0) <{"value" = 13 : i6}> : (!reg) -> !reg
    %21 = "riscv.bexti"(%0) <{"value" = 13 : i6}> : (!reg) -> !reg
    %22 = "riscv.binvi"(%0) <{"value" = 13 : i6}> : (!reg) -> !reg
    %23 = "riscv.bseti"(%0) <{"value" = 13 : i6}> : (!reg) -> !reg
    // Unary operations 
    %24 = "riscv.sextb"(%0) : (!reg) -> !reg
    %25 = "riscv.sexth"(%0) : (!reg) -> !reg
    %26 = "riscv.zexth"(%0) : (!reg) -> !reg
    %27 = "riscv.clz"(%0) : (!reg) -> !reg
    %28 = "riscv.clzw"(%0) : (!reg) -> !reg
    %29 = "riscv.ctz"(%0) : (!reg) -> !reg
    %30 = "riscv.ctzw"(%0) : (!reg) -> !reg
    %84 = "riscv.cpop"(%0) : (!reg) -> !reg
    %85 = "riscv.cpopw"(%0) : (!reg) -> !reg
    // Binary operations 
    %31 = "riscv.add"(%0, %1) : (!reg, !reg) -> !reg
    %32 = "riscv.sub"(%0, %1) : (!reg, !reg) -> !reg
    %33 = "riscv.sll"(%0, %1) : (!reg, !reg) -> !reg
    %34 = "riscv.slt"(%0, %1) : (!reg, !reg) -> !reg
    %35 = "riscv.sltu"(%0, %1) : (!reg, !reg) -> !reg
    %36 = "riscv.xor"(%0, %1) : (!reg, !reg) -> !reg
    %37 = "riscv.srl"(%0, %1) : (!reg, !reg) -> !reg
    %38 = "riscv.sra"(%0, %1) : (!reg, !reg) -> !reg
    %39 = "riscv.or"(%0, %1) : (!reg, !reg) -> !reg
    %40 = "riscv.and"(%0, %1) : (!reg, !reg) -> !reg
    %41 = "riscv.addw"(%0, %1) : (!reg, !reg) -> !reg
    %42 = "riscv.subw"(%0, %1) : (!reg, !reg) -> !reg
    %43 = "riscv.sllw"(%0, %1) : (!reg, !reg) -> !reg
    %44 = "riscv.srlw"(%0, %1) : (!reg, !reg) -> !reg
    %45 = "riscv.sraw"(%0, %1) : (!reg, !reg) -> !reg
    %46 = "riscv.rem"(%0, %1) : (!reg, !reg) -> !reg
    %47 = "riscv.remu"(%0, %1) : (!reg, !reg) -> !reg
    %48 = "riscv.remw"(%0, %1) : (!reg, !reg) -> !reg
    %49 = "riscv.remuw"(%0, %1) : (!reg, !reg) -> !reg
    %50 = "riscv.mul"(%0, %1) : (!reg, !reg) -> !reg
    %51 = "riscv.mulh"(%0, %1) : (!reg, !reg) -> !reg
    %52 = "riscv.mulhu"(%0, %1) : (!reg, !reg) -> !reg
    %53 = "riscv.mulhsu"(%0, %1) : (!reg, !reg) -> !reg
    %54 = "riscv.mulw"(%0, %1) : (!reg, !reg) -> !reg
    %55 = "riscv.div"(%0, %1) : (!reg, !reg) -> !reg
    %56 = "riscv.divw"(%0, %1) : (!reg, !reg) -> !reg
    %57 = "riscv.divu"(%0, %1) : (!reg, !reg) -> !reg
    %58 = "riscv.divuw"(%0, %1) : (!reg, !reg) -> !reg
    %59 = "riscv.adduw"(%0, %1) : (!reg, !reg) -> !reg
    %60 = "riscv.sh1adduw"(%0, %1) : (!reg, !reg) -> !reg
    %61 = "riscv.sh2adduw"(%0, %1) : (!reg, !reg) -> !reg
    %62 = "riscv.sh3adduw"(%0, %1) : (!reg, !reg) -> !reg
    %63 = "riscv.sh1add"(%0, %1) : (!reg, !reg) -> !reg
    %64 = "riscv.sh2add"(%0, %1) : (!reg, !reg) -> !reg
    %65 = "riscv.sh3add"(%0, %1) : (!reg, !reg) -> !reg
    %66 = "riscv.andn"(%0, %1) : (!reg, !reg) -> !reg
    %67 = "riscv.orn"(%0, %1) : (!reg, !reg) -> !reg
    %68 = "riscv.xnor"(%0, %1) : (!reg, !reg) -> !reg
    %69 = "riscv.max"(%0, %1) : (!reg, !reg) -> !reg
    %70 = "riscv.maxu"(%0, %1) : (!reg, !reg) -> !reg
    %71 = "riscv.min"(%0, %1) : (!reg, !reg) -> !reg
    %72 = "riscv.minu"(%0, %1) : (!reg, !reg) -> !reg
    %73 = "riscv.rol"(%0, %1) : (!reg, !reg) -> !reg
    %74 = "riscv.ror"(%0, %1) : (!reg, !reg) -> !reg
    %75 = "riscv.rolw"(%0, %1) : (!reg, !reg) -> !reg
    %76 = "riscv.rorw"(%0, %1) : (!reg, !reg) -> !reg
    %77 = "riscv.bclr"(%0, %1) : (!reg, !reg) -> !reg
    %78 = "riscv.bext"(%0, %1) : (!reg, !reg) -> !reg
    %79 = "riscv.binv"(%0, %1) : (!reg, !reg) -> !reg
    %80 = "riscv.bset"(%0, %1) : (!reg, !reg) -> !reg
    %81 = "riscv.pack"(%0, %1) : (!reg, !reg) -> !reg
    %82 = "riscv.packh"(%0, %1) : (!reg, !reg) -> !reg
    %83 = "riscv.packw"(%0, %1) : (!reg, !reg) -> !reg
}) : () -> ()

// CHECK: "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %{{.*}} = "riscv.li"() <{"value" = 13 : i64}> : () -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.li"() <{"value" = 17 : i64}> : () -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.lui"() <{"value" = 13 : i20}> : () -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.auipc"(%{{.*}}) <{"value" = 13 : i20}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.addi"(%{{.*}}) <{"value" = 5 : i12}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.slti"(%{{.*}}) <{"value" = 7 : i12}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sltiu"(%{{.*}}) <{"value" = 11 : i12}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.andi"(%{{.*}}) <{"value" = 13 : i12}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.ori"(%{{.*}}) <{"value" = 17 : i12}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.xori"(%{{.*}}) <{"value" = 23 : i12}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.addiw"(%{{.*}}) <{"value" = 29 : i12}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.slli"(%{{.*}}) <{"value" = 31 : i6}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 33 : i6}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 37 : i6}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.slliw"(%{{.*}}) <{"value" = 13 : i5}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.srliw"(%{{.*}}) <{"value" = 17 : i5}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sraiw"(%{{.*}}) <{"value" = 19 : i5}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.slliuw"(%{{.*}}) <{"value" = 13 : i6}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.roriw"(%{{.*}}) <{"value" = 13 : i5}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.rori"(%{{.*}}) <{"value" = 13 : i6}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.bclri"(%{{.*}}) <{"value" = 13 : i6}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.bexti"(%{{.*}}) <{"value" = 13 : i6}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.binvi"(%{{.*}}) <{"value" = 13 : i6}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.bseti"(%{{.*}}) <{"value" = 13 : i6}> : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sextb"(%{{.*}}) : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sexth"(%{{.*}}) : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.zexth"(%{{.*}}) : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.clz"(%{{.*}}) : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.clzw"(%{{.*}}) : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.ctz"(%{{.*}}) : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.ctzw"(%{{.*}}) : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.cpop"(%{{.*}}) : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.cpopw"(%{{.*}}) : (!reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sll"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.slt"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sltu"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.xor"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.srl"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sra"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.addw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.subw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sllw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.srlw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sraw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.rem"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.remu"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.remw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.remuw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.mul"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.mulh"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.mulhu"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.mulhsu"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.mulw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.div"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.divw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.divu"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.divuw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.adduw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sh1adduw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sh2adduw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sh3adduw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sh1add"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sh2add"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.sh3add"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.andn"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.orn"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.xnor"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.max"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.maxu"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.min"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.minu"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.rol"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.ror"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.rolw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.rorw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.bclr"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.bext"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.binv"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.bset"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.pack"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.packh"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT:     %{{.*}} = "riscv.packw"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
// CHECK-NEXT: }) : () -> ()
