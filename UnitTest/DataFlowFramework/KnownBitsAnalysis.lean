import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.KnownBitsAnalysis

open Veir

namespace KnownBitsDataflow

/-- Expected masks for one named SSA value. -/
private structure ExpectedKnownBits where
  name : String
  bitwidth : Nat
  zero : Nat
  one : Nat

private def knownBitsToString : KnownBitsLattice → String
  | .bottom => "bottom"
  | .known bits => s!"i{bits.bitwidth}(zero={bits.zero.toNat}, one={bits.one.toNat})"

private def compareKnownBits
    (dfCtx : DataFlowContext)
    (recovered : RecoveredNames)
    (expected : Array ExpectedKnownBits) : MismatchReport := Id.run do
  let mut report := #[]
  for e in expected do
    let some value := recovered.values[e.name]?
      | report := report.push s!"known bits {e.name}: missing SSA value"
        continue
    let observed : KnownBitsLattice := SparseFact.getElement .knownBits value dfCtx
    let expectedZero := BitVec.ofNat e.bitwidth e.zero
    let expectedOne := BitVec.ofNat e.bitwidth e.one
    let isMatch := match observed with
      | .known bits =>
          bits.bitwidth == e.bitwidth &&
          bits.zero.toNat == expectedZero.toNat &&
          bits.one.toNat == expectedOne.toNat
      | .bottom => false
    if !isMatch then
      report := report.push <|
        s!"known bits {e.name}: expected i{e.bitwidth}" ++
        s!"(zero={expectedZero.toNat}, one={expectedOne.toNat}), " ++
        s!"observed {knownBitsToString observed}"
  report

private def run (mlir : String) (expected : Array ExpectedKnownBits) : String :=
  runWithAnalyses mlir #[Veir.KnownBitsAnalysis] fun top dfCtx irCtx =>
    match recoverNames top irCtx mlir with
    | .error err => #[err]
    | .ok recovered => compareKnownBits dfCtx recovered expected

/-- Arith constants and bitwise operations preserve partial known-bit information. -/
def runArithKnownBitsExample : String :=
  let mlir := r#""builtin.module"() ({
^bb0:
  "func.func"() <{function_type = (i8) -> (), sym_name = "known_bits_arith"}> ({
  ^entry(%x : i8):
    %c240 = "arith.constant"() <{value = 240 : i8}> : () -> i8
    %c3 = "arith.constant"() <{value = 3 : i8}> : () -> i8
    %c5 = "arith.constant"() <{value = 5 : i8}> : () -> i8
    %sum = "arith.addi"(%c3, %c5) : (i8, i8) -> i8
    %anded = "arith.andi"(%x, %c240) : (i8, i8) -> i8
    %ored = "arith.ori"(%anded, %c3) : (i8, i8) -> i8
    %xored = "arith.xori"(%ored, %c5) : (i8, i8) -> i8
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#
  let expected :=
    #[ { name := "x",     bitwidth := 8, zero := 0,   one := 0 }
     , { name := "c240",  bitwidth := 8, zero := 15,  one := 240 }
     , { name := "c3",    bitwidth := 8, zero := 252, one := 3 }
     , { name := "c5",    bitwidth := 8, zero := 250, one := 5 }
     , { name := "sum",   bitwidth := 8, zero := 247, one := 8 }
     , { name := "anded", bitwidth := 8, zero := 15,  one := 0 }
     , { name := "ored",  bitwidth := 8, zero := 12,  one := 3 }
     , { name := "xored", bitwidth := 8, zero := 9,   one := 6 }
     ]
  run mlir expected

/-- LLVM spellings and variadic Comb operations use the same transfer functions. -/
def runLLVMAndCombKnownBitsExample : String :=
  let mlir := r#""builtin.module"() ({
^bb0:
  "func.func"() <{function_type = (i8) -> (), sym_name = "known_bits_dialects"}> ({
  ^entry(%x : i8):
    %lc240 = "llvm.mlir.constant"() <{value = 240 : i8}> : () -> i8
    %lc3 = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %lc5 = "llvm.mlir.constant"() <{value = 5 : i8}> : () -> i8
    %land = "llvm.and"(%x, %lc240) : (i8, i8) -> i8
    %lor = "llvm.or"(%land, %lc3) : (i8, i8) -> i8
    %lxor = "llvm.xor"(%lor, %lc5) : (i8, i8) -> i8
    %hc240 = "hw.constant"() <{value = 240 : i8}> : () -> i8
    %hc15 = "hw.constant"() <{value = 15 : i8}> : () -> i8
    %hc3 = "hw.constant"() <{value = 3 : i8}> : () -> i8
    %cand = "comb.and"(%hc240, %hc15, %hc3) : (i8, i8, i8) -> i8
    %cor = "comb.or"(%hc240, %hc15, %hc3) : (i8, i8, i8) -> i8
    %cxor = "comb.xor"(%hc240, %hc15, %hc3) : (i8, i8, i8) -> i8
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#
  let expected :=
    #[ { name := "land", bitwidth := 8, zero := 15,  one := 0 }
     , { name := "lor",  bitwidth := 8, zero := 12,  one := 3 }
     , { name := "lxor", bitwidth := 8, zero := 9,   one := 6 }
     , { name := "cand", bitwidth := 8, zero := 255, one := 0 }
     , { name := "cor",  bitwidth := 8, zero := 0,   one := 255 }
     , { name := "cxor", bitwidth := 8, zero := 3,   one := 252 }
     ]
  run mlir expected

/-- Arithmetic, shifts, casts, comparisons, and flags use LLVM-style known-bit transfer rules. -/
def runLLVMStyleTransfersExample : String :=
  let mlir := r#""builtin.module"() ({
^bb0:
  "func.func"() <{function_type = (i8) -> (), sym_name = "known_bits_transfers"}> ({
  ^entry(%x : i8):
    %c1 = "arith.constant"() <{value = 1 : i8}> : () -> i8
    %c3 = "arith.constant"() <{value = 3 : i8}> : () -> i8
    %c12 = "arith.constant"() <{value = 12 : i8}> : () -> i8
    %c16 = "arith.constant"() <{value = 16 : i8}> : () -> i8
    %c127 = "arith.constant"() <{value = 127 : i8}> : () -> i8
    %c128 = "arith.constant"() <{value = 128 : i8}> : () -> i8
    %low = "arith.andi"(%x, %c127) : (i8, i8) -> i8
    %shl = "arith.shli"(%x, %c3) : (i8, i8) -> i8
    %lshr = "arith.shrui"(%x, %c3) : (i8, i8) -> i8
    %mul = "arith.muli"(%x, %c12) : (i8, i8) -> i8
    %udiv = "arith.divui"(%x, %c16) : (i8, i8) -> i8
    %urem = "arith.remui"(%x, %c16) : (i8, i8) -> i8
    %self_add = "arith.addi"(%x, %x) : (i8, i8) -> i8
    %nuw = "arith.addi"(%x, %c128) <{overflowFlags = #arith.overflow<nuw>}> : (i8, i8) -> i8
    %nsw = "arith.addi"(%low, %c1) <{overflowFlags = #arith.overflow<nsw>}> : (i8, i8) -> i8
    %wide = "arith.extui"(%low) : (i8) -> i16
    %ult = "arith.cmpi"(%low, %c128) <{predicate = 6 : i64}> : (i8, i8) -> i1
    %pop = "llvm.intr.ctpop"(%low) : (i8) -> i8
    %clz = "llvm.intr.ctlz"(%low) <{is_zero_poison = 0 : i1}> : (i8) -> i8
    %reverse = "llvm.intr.bitreverse"(%low) : (i8) -> i8
    %fshl = "llvm.intr.fshl"(%x, %low, %c3) : (i8, i8, i8) -> i8
    %saturating = "llvm.intr.uadd.sat"(%x, %c128) : (i8, i8) -> i8
    %bswap = "llvm.intr.bswap"(%wide) : (i16) -> i16
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#
  let expected :=
    #[ { name := "low",  bitwidth := 8,  zero := 128,   one := 0 }
     , { name := "shl",  bitwidth := 8,  zero := 7,     one := 0 }
     , { name := "lshr", bitwidth := 8,  zero := 224,   one := 0 }
     , { name := "mul",  bitwidth := 8,  zero := 3,     one := 0 }
     , { name := "udiv", bitwidth := 8,  zero := 240,   one := 0 }
     , { name := "urem", bitwidth := 8,  zero := 240,   one := 0 }
     , { name := "self_add", bitwidth := 8, zero := 1,  one := 0 }
     , { name := "nuw",  bitwidth := 8,  zero := 0,     one := 128 }
     , { name := "nsw",  bitwidth := 8,  zero := 128,   one := 0 }
     , { name := "wide", bitwidth := 16, zero := 65408, one := 0 }
     , { name := "ult",  bitwidth := 1,  zero := 0,     one := 1 }
     , { name := "pop",  bitwidth := 8,  zero := 248,   one := 0 }
     , { name := "clz",  bitwidth := 8,  zero := 240,   one := 0 }
     , { name := "reverse",    bitwidth := 8,  zero := 1,     one := 0 }
     , { name := "fshl",       bitwidth := 8,  zero := 4,     one := 0 }
     , { name := "saturating", bitwidth := 8,  zero := 0,     one := 128 }
     , { name := "bswap",      bitwidth := 16, zero := 33023, one := 0 }
     ]
  run mlir expected

/-- Joining exact values retains only the bits on which both values agree. -/
def testKnownBitsJoin : String :=
  let joined :=
    KnownBitsLattice.join
      (.constant 8 165)
      (.constant 8 167)
  match joined with
  | .known bits =>
      if bits.bitwidth == 8 && bits.zero.toNat == 88 && bits.one.toNat == 165 then
        "ok"
      else
        s!"unexpected join: {knownBitsToString joined}"
  | .bottom => s!"unexpected join: {knownBitsToString joined}"

/--
info: "ok"
-/
#guard_msgs in
#eval! runArithKnownBitsExample

/--
info: "ok"
-/
#guard_msgs in
#eval! runLLVMAndCombKnownBitsExample

/--
info: "ok"
-/
#guard_msgs in
#eval! runLLVMStyleTransfersExample

/--
info: "ok"
-/
#guard_msgs in
#eval! testKnownBitsJoin

end KnownBitsDataflow
