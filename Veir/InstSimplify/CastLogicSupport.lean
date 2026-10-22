import Veir.InstSimplify.ArithmeticExtra
import Veir.InstSimplify.CmpSelectSupport
import Veir.InstSimplify.LogicExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

theorem logic_zext_width_lt (src dst : IntegerType)
    (p : propertiesOf (.llvm .zext : OpCode)) (x : LLVM.Int src.bitwidth) (v : RuntimeValue)
    (h : InterpretsTo (.llvm .zext) p #[dst] #[.int src.bitwidth x] #[v]) : src.bitwidth < dst.bitwidth := by
  by_cases hl : src.bitwidth < dst.bitwidth
  · exact hl
  have hn : dst.bitwidth ≤ src.bitwidth := by omega
  have h := h.2 MemoryState.empty
  cases src
  cases dst
  simp [interpretOp', Llvm.interpretOp', TypeAttr.of_val, Attribute.of,
    -Attribute.integerType_eq_of, hn] at h

theorem logic_zext_iff (src dst : IntegerType)
    (p : propertiesOf (.llvm .zext : OpCode)) (x : LLVM.Int src.bitwidth) (v : RuntimeValue)
    (hw : src.bitwidth < dst.bitwidth) :
    InterpretsTo (.llvm .zext) p #[dst] #[.int src.bitwidth x] #[v] ↔
      v = .int dst.bitwidth (LLVM.Int.zext x dst.bitwidth p.nneg hw) := by
  cases src
  cases dst
  simp [InterpretsTo, interpretOp', Llvm.interpretOp', TypeAttr.of_val, Attribute.of,
    -Attribute.integerType_eq_of, RuntimeValue.ArrayConforms, RuntimeValue.Conforms, Nat.not_le_of_gt hw]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem logic_zext_outcomes (a : BitVec w) (v : Nat) (nneg : Bool) (hw : w < v) :
    LLVM.Int.zext (.val a) v nneg hw = .poison ∨
    LLVM.Int.zext (.val a) v nneg hw = .val (a.zeroExtend v) := by
  simp only [LLVM.Int.zext,Id.run,pure]
  split <;> simp_all

theorem logic_zext_and_sext (a : BitVec w) (v : Nat) :
    (a.zeroExtend v) &&& (a.signExtend v) = a.zeroExtend v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < w
  · simp [BitVec.getLsbD_signExtend,BitVec.getElem_signExtend,h,hi]
  · have hz := BitVec.getLsbD_of_ge a i (by omega)
    simp [BitVec.getLsbD_signExtend,BitVec.getElem_signExtend,h,hi,hz]

theorem logic_zext_or_sext (a : BitVec w) (v : Nat) :
    (a.zeroExtend v) ||| (a.signExtend v) = a.signExtend v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < w
  · simp [BitVec.getLsbD_signExtend,BitVec.getElem_signExtend,h,hi]
  · have hz := BitVec.getLsbD_of_ge a i (by omega)
    simp [BitVec.getLsbD_signExtend,BitVec.getElem_signExtend,h,hi,hz]

theorem logic_zext_toInt (a : BitVec w) (hw : w < v) : (a.zeroExtend v).toInt = a.toNat := by
  simpa only [BitVec.setWidth'_eq] using (BitVec.toInt_setWidth'_of_lt hw (x := a))
end Veir.InstSimplify
namespace Veir.InstSimplify
 theorem logic_beq_comm (a b : BitVec w) : (a == b) = (b == a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact eq_comm
 theorem logic_icmp_swap (a b : LLVM.Int w) (p : LLVM.IntPred) :
    LLVM.Int.icmp b a (swapCmpPred p) = LLVM.Int.icmp a b p := by
  cases a <;> cases b <;> cases p <;>
    simp [LLVM.Int.icmp,LLVM.IntPred.eval,swapCmpPred,Id.run,pure,logic_beq_comm,bne_eq]
end Veir.InstSimplify
