module

import all Veir.Passes.InstCombine
import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Data.LLVM.Int.Basic
import Veir.PatternRewriter.Puddle.Validity

namespace Veir

open Puddle

private theorem mul_two_refines (w : Nat) (x : Data.LLVM.Int w)
    (c : BitVec w) (hc : c.toInt = 2) (nsw nuw : Bool) :
    RuntimeValue.int w (x.mul (.val c) nsw nuw) ⊒
      .int w (x.add x nsw nuw) := by
  cases x
  case poison => simp [Data.LLVM.Int.mul, Data.LLVM.Int.add]
  case val v =>
    have hSigned : v.smulOverflow c = v.saddOverflow v := by
      rw [BitVec.smulOverflow, BitVec.saddOverflow, hc, Int.mul_comm v.toInt 2, Int.two_mul]
    have hUnsigned : v.umulOverflow c = v.uaddOverflow v := by
      grind only [BitVec.umulOverflow, BitVec.uaddOverflow,
        BitVec.toInt_eq_toNat_of_msb, BitVec.msb_eq_toInt]
    have hValue : v * c = v + v := by
      have hcBits : c = BitVec.ofInt w 2 := by rw [← hc, BitVec.ofInt_toInt]
      simp [hcBits, BitVec.mul_two]
    simp [Data.LLVM.Int.mul, Data.LLVM.Int.add, hSigned, hUnsigned, hValue]

theorem mulITwoToAddi_valid : mulITwoToAddiPattern.Valid := by
  simp only [mulITwoToAddiPattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro ty x cstProps cstVal _ hCstEval
  intro mulProps old _ hMulEval hCstMatch
  exists RuntimeValue.int ty.bitwidth (x.add x mulProps.nsw mulProps.nuw)
  constructor
  · simp [InterpretsTo, interpretOp', Llvm.interpretOp']
  · have hCstRun := hCstEval.2 .empty
    cases hAttr : cstProps.value <;> simp [hAttr, ← Attribute.integerType_eq_of] at hCstMatch
    simp [interpretOp', Llvm.interpretOp', hAttr, ← Attribute.integerType_eq_of] at hCstRun
    rw [← hCstRun] at hMulEval
    have hMulRun := hMulEval.2 .empty
    simp [interpretOp', Llvm.interpretOp'] at hMulRun
    rw [← hMulRun]
    apply mul_two_refines
    simpa using hCstMatch
