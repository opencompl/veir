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
  | .top => "top"
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
    let expectedValue := KnownBitsLattice.known
      { bitwidth := e.bitwidth
        zero := BitVec.ofNat e.bitwidth e.zero
        one := BitVec.ofNat e.bitwidth e.one }
    if observed ≠ expectedValue then
      report := report.push <|
        s!"known bits {e.name}: expected {knownBitsToString expectedValue}, " ++
        s!"observed {knownBitsToString observed}"
  report

private def run (mlir : String) (expected : Array ExpectedKnownBits) : String :=
  runWithAnalyses mlir #[Veir.KnownBitsAnalysis] fun top dfCtx parserState =>
    match recoverNames top parserState.ctx mlir with
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

/-- Joining exact values retains only the bits on which both values agree. -/
def testKnownBitsJoin : String :=
  let joined :=
    KnownBitsLattice.join
      (.constant 8 165)
      (.constant 8 167)
  let expected : KnownBitsLattice :=
    .known
      { bitwidth := 8
        zero := BitVec.ofNat 8 88
        one := BitVec.ofNat 8 165 }
  if joined = expected then "ok" else s!"unexpected join: {knownBitsToString joined}"

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
#eval! testKnownBitsJoin

end KnownBitsDataflow
