// RUN: veir-opt %s -p=arith-to-llvm > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --check-prefix=LOWERED --input-file=%t

// The multi-operation expansions, on operands the folder cannot see through.
//
// `arith-to-llvm` builds its expansions with `createOrFold!`, so an expansion
// over constant operands collapses to a single `llvm.mlir.constant` -- which is
// what every other test in this directory now exercises. Routing the constants
// through a `cf.br` turns them into block arguments, which have no defining
// operation and so never fold, leaving the expansion trees themselves covered.
"builtin.module"() ({
  "func.func"() <{sym_name = "main",
                  function_type = () -> (i8, i8, i8, i8, i1, i8, i1, i8, i8, i8, i8)}> ({
    ^entry():
      %c255 = "arith.constant"() <{value = 255 : i8}> : () -> i8
      %c2 = "arith.constant"() <{value = 2 : i8}> : () -> i8
      %cn7 = "arith.constant"() <{value = -7 : i8}> : () -> i8
      %c0 = "arith.constant"() <{value = 0 : i8}> : () -> i8
      %c1 = "arith.constant"() <{value = 1 : i8}> : () -> i8
      %c16 = "arith.constant"() <{value = 16 : i8}> : () -> i8
      %cn16 = "arith.constant"() <{value = -16 : i8}> : () -> i8
      "cf.br"(%c255, %c2, %cn7, %c0, %c1, %c16, %cn16) [^body]
        : (i8, i8, i8, i8, i8, i8, i8) -> ()
    ^body(%a255 : i8, %a2 : i8, %an7 : i8, %a0 : i8, %a1 : i8, %a16 : i8, %an16 : i8):
      // ceil(255 / 2) = 128
      %r0 = "arith.ceildivui"(%a255, %a2) : (i8, i8) -> i8
      // ceil(-7 / 2) = -3, floor(-7 / 2) = -4
      %r1 = "arith.ceildivsi"(%an7, %a2) : (i8, i8) -> i8
      %r2 = "arith.floordivsi"(%an7, %a2) : (i8, i8) -> i8
      // 255 + 1 = 0 carry 1, and 0 - 1 = 255 borrow 1
      %s, %carry = "arith.addui_extended"(%a255, %a1) : (i8, i8) -> (i8, i1)
      %d, %borrow = "arith.subui_extended"(%a0, %a1) : (i8, i8) -> (i8, i1)
      // 16 * 16 = 256, and -16 * 16 = -256
      %ulo, %uhi = "arith.mului_extended"(%a16, %a16) : (i8, i8) -> (i8, i8)
      %slo, %shi = "arith.mulsi_extended"(%an16, %a16) : (i8, i8) -> (i8, i8)
      "func.return"(%r0, %r1, %r2, %s, %carry, %d, %borrow, %ulo, %uhi, %slo, %shi)
        : (i8, i8, i8, i8, i1, i8, i1, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x80#8, 0xfd#8, 0xfc#8, 0x00#8, 0x1#1, 0xff#8, 0x1#1, 0x00#8, 0x01#8, 0x00#8, 0xff#8]

// Nothing folded away: the expansions are still emitted as operation trees.
// LOWERED: "builtin.module"
// LOWERED-NOT: "arith.
// LOWERED-DAG: "llvm.udiv"
// LOWERED-DAG: "llvm.sdiv"
// LOWERED-DAG: "llvm.select"
// LOWERED-DAG: "llvm.icmp"
// LOWERED-DAG: "llvm.zext"
