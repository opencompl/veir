// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  ^bb0():
    %0 = "riscv.li"() <{ "value" = 13 : i64 }>  : () -> i64
    %1 = "riscv.li"() <{ "value" = 17 : i64 }> : () -> i64
    // Immediate load 
    %2 = "riscv.lui"() <{"value" = 13 : i20}> : () -> i64
    %3 = "riscv.auipc"(%0) <{"value" = 13 : i20}> : (i64) -> i64
    // Immediate operations 
    %4 = "riscv.addi"(%0) : (i64) -> i64
    %5 = "riscv.slti"(%0) : (i64) -> i64
    %6 = "riscv.sltiu"(%0) : (i64) -> i64
    %7 = "riscv.andi"(%0) <{"value" = 13 : i12}> : (i64) -> i64
    %8 = "riscv.ori"(%0) <{"value" = 17 : i12}> : (i64) -> i64
    %9 = "riscv.xori"(%0) <{"value" = 23 : i12}> : (i64) -> i64
    %10 = "riscv.addiw"(%0) : (i64) -> i64
    %11 = "riscv.slli"(%0) : (i64) -> i64
    %12 = "riscv.srli"(%0) : (i64) -> i64
    %13 = "riscv.srai"(%0) : (i64) -> i64
    %14 = "riscv.slliw"(%0) : (i64) -> i64
    %15 = "riscv.srliw"(%0) : (i64) -> i64
    %16 = "riscv.sraiw"(%0) : (i64) -> i64
    %17 = "riscv.slliuw"(%0) : (i64) -> i64
    %18 = "riscv.roriw"(%0) : (i64) -> i64
    %19 = "riscv.rori"(%0) : (i64) -> i64
    %20 = "riscv.bclri"(%0) : (i64) -> i64
    %21 = "riscv.bexti"(%0) : (i64) -> i64
    %22 = "riscv.binvi"(%0) : (i64) -> i64
    %23 = "riscv.bseti"(%0) : (i64) -> i64
    // Unary operations 
    %24 = "riscv.sextb"(%0) : (i64) -> i64
    %25 = "riscv.sexth"(%0) : (i64) -> i64
    %26 = "riscv.zexth"(%0) : (i64) -> i64
    %27 = "riscv.clz"(%0) : (i64) -> i64
    %28 = "riscv.clzw"(%0) : (i64) -> i64
    %29 = "riscv.ctz"(%0) : (i64) -> i64
    %30 = "riscv.ctzw"(%0) : (i64) -> i64
    // Binary operations 
    %31 = "riscv.add"(%0, %1) : (i64, i64) -> i64
    %32 = "riscv.sub"(%0, %1) : (i64, i64) -> i64
    %33 = "riscv.sll"(%0, %1) : (i64, i64) -> i64
    %34 = "riscv.slt"(%0, %1) : (i64, i64) -> i64
    %35 = "riscv.sltu"(%0, %1) : (i64, i64) -> i64
    %36 = "riscv.xor"(%0, %1) : (i64, i64) -> i64
    %37 = "riscv.srl"(%0, %1) : (i64, i64) -> i64
    %38 = "riscv.sra"(%0, %1) : (i64, i64) -> i64
    %39 = "riscv.or"(%0, %1) : (i64, i64) -> i64
    %40 = "riscv.and"(%0, %1) : (i64, i64) -> i64
    %41 = "riscv.addw"(%0, %1) : (i64, i64) -> i64
    %42 = "riscv.subw"(%0, %1) : (i64, i64) -> i64
    %43 = "riscv.sllw"(%0, %1) : (i64, i64) -> i64
    %44 = "riscv.srlw"(%0, %1) : (i64, i64) -> i64
    %45 = "riscv.sraw"(%0, %1) : (i64, i64) -> i64
    %46 = "riscv.rem"(%0, %1) : (i64, i64) -> i64
    %47 = "riscv.remu"(%0, %1) : (i64, i64) -> i64
    %48 = "riscv.remw"(%0, %1) : (i64, i64) -> i64
    %49 = "riscv.remuw"(%0, %1) : (i64, i64) -> i64
    %50 = "riscv.mul"(%0, %1) : (i64, i64) -> i64
    %51 = "riscv.mulh"(%0, %1) : (i64, i64) -> i64
    %52 = "riscv.mulhu"(%0, %1) : (i64, i64) -> i64
    %53 = "riscv.mulhsu"(%0, %1) : (i64, i64) -> i64
    %54 = "riscv.mulw"(%0, %1) : (i64, i64) -> i64
    %55 = "riscv.div"(%0, %1) : (i64, i64) -> i64
    %56 = "riscv.divw"(%0, %1) : (i64, i64) -> i64
    %57 = "riscv.divu"(%0, %1) : (i64, i64) -> i64
    %58 = "riscv.divuw"(%0, %1) : (i64, i64) -> i64
    %59 = "riscv.adduw"(%0, %1) : (i64, i64) -> i64
    %60 = "riscv.sh1adduw"(%0, %1) : (i64, i64) -> i64
    %61 = "riscv.sh2adduw"(%0, %1) : (i64, i64) -> i64
    %62 = "riscv.sh3adduw"(%0, %1) : (i64, i64) -> i64
    %63 = "riscv.sh1add"(%0, %1) : (i64, i64) -> i64
    %64 = "riscv.sh2add"(%0, %1) : (i64, i64) -> i64
    %65 = "riscv.sh3add"(%0, %1) : (i64, i64) -> i64
    %66 = "riscv.andn"(%0, %1) : (i64, i64) -> i64
    %67 = "riscv.orn"(%0, %1) : (i64, i64) -> i64
    %68 = "riscv.xnor"(%0, %1) : (i64, i64) -> i64
    %69 = "riscv.max"(%0, %1) : (i64, i64) -> i64
    %70 = "riscv.maxu"(%0, %1) : (i64, i64) -> i64
    %71 = "riscv.min"(%0, %1) : (i64, i64) -> i64
    %72 = "riscv.minu"(%0, %1) : (i64, i64) -> i64
    %73 = "riscv.rol"(%0, %1) : (i64, i64) -> i64
    %74 = "riscv.ror"(%0, %1) : (i64, i64) -> i64
    %75 = "riscv.rolw"(%0, %1) : (i64, i64) -> i64
    %76 = "riscv.rorw"(%0, %1) : (i64, i64) -> i64
    %77 = "riscv.bclr"(%0, %1) : (i64, i64) -> i64
    %78 = "riscv.bext"(%0, %1) : (i64, i64) -> i64
    %79 = "riscv.binv"(%0, %1) : (i64, i64) -> i64
    %80 = "riscv.bset"(%0, %1) : (i64, i64) -> i64
    %81 = "riscv.pack"(%0, %1) : (i64, i64) -> i64
    %82 = "riscv.packh"(%0, %1) : (i64, i64) -> i64
    %83 = "riscv.packw"(%0, %1) : (i64, i64) -> i64
}) : () -> ()

// CHECK: "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %{{.*}} = "riscv.li"() <{"value" = 13 : i64}> : () -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.li"() <{"value" = 17 : i64}> : () -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.lui"() <{"value" = 13 : i20}> : () -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.auipc"(%{{.*}}) <{"value" = 13 : i20}> : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.addi"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.slti"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sltiu"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.andi"(%{{.*}}) <{"value" = 13 : i12}> : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.ori"(%{{.*}}) <{"value" = 17 : i12}> : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.xori"(%{{.*}}) <{"value" = 23 : i12}> : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.addiw"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.slli"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.srli"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.srai"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.slliw"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.srliw"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sraiw"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.slliuw"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.roriw"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.rori"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.bclri"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.bexti"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.binvi"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.bseti"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sextb"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sexth"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.zexth"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.clz"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.clzw"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.ctz"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.ctzw"(%{{.*}}) : (i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sll"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.slt"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sltu"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.xor"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.srl"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sra"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.addw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.subw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sllw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.srlw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sraw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.rem"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.remu"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.remw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.remuw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.mul"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.mulh"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.mulhu"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.mulhsu"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.mulw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.div"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.divw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.divu"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.divuw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.adduw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sh1adduw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sh2adduw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sh3adduw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sh1add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sh2add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.sh3add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.andn"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.orn"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.xnor"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.max"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.maxu"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.min"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.minu"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.rol"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.ror"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.rolw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.rorw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.bclr"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.bext"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.binv"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.bset"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.pack"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.packh"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:     %{{.*}} = "riscv.packw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT: }) : () -> ()
