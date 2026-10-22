import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
 theorem mask_shift_left (x mask : BitVec w) (n : Nat)
    (h : (~~~mask) >>> n = 0) : (x <<< n) &&& mask = x <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hn : n ≤ i
  · have hsub : n + (i - n) = i := by omega
    have hz := congrArg (fun v : BitVec w => v.getLsbD (i-n)) h
    simp [BitVec.getLsbD_ushiftRight, hsub, hi] at hz
    simp [BitVec.getLsbD_shiftLeft, hn, hi, hz]
  · have hn' : i < n := by omega
    simp [BitVec.getLsbD_shiftLeft, hn, hi, hn']
 theorem mask_shift_right (x mask : BitVec w) (n : Nat)
    (h : (~~~mask) <<< n = 0) : (x >>> n) &&& mask = x >>> n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hn : i+n < w
  · have hz := congrArg (fun v : BitVec w => v.getLsbD (i+n)) h
    simp [BitVec.getLsbD_shiftLeft, hn, hi] at hz
    have hm : mask.getLsbD i = true := by simpa only [BitVec.getLsbD_eq_getElem hi] using hz
    simp [BitVec.getLsbD_ushiftRight, hm]
  · have hz : x.getLsbD (n+i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [BitVec.getLsbD_ushiftRight, hz]
end Veir.InstSimplify
namespace Veir.InstSimplify
 theorem ofInt_complement (w : Nat) (n : Int) : BitVec.ofInt w (-n-1) = ~~~(BitVec.ofInt w n) := by
  rw [Int.sub_eq_add_neg,BitVec.ofInt_add]
  simp [BitVec.ofInt_neg,BitVec.not_eq_neg_add,BitVec.sub_eq_add_neg]
 theorem complement_sub (a c : BitVec w) : (~~~c)-a = ~~~(a+c) := by
  simp only [BitVec.not_eq_neg_add,BitVec.neg_add,BitVec.sub_eq_add_neg]
  ac_rfl
 theorem integerAttr_bits (ty : IntegerType) (n : Int) :
    BitVec.ofInt ty.bitwidth (IntegerAttr.ofInt n ty).value = BitVec.ofInt ty.bitwidth n := by
  simp only [IntegerAttr.ofInt,IntegerAttr.normalizeValue]
  split <;> simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_toInt] <;> simp
end Veir.InstSimplify
namespace Veir.InstSimplify
 theorem add_outcomes (a b : BitVec w) (nsw nuw : Bool) :
    LLVM.Int.add (.val a) (.val b) nsw nuw = .poison ∨
    LLVM.Int.add (.val a) (.val b) nsw nuw = .val (a+b) := by
  simp only [LLVM.Int.add,Id.run,pure]
  split <;> simp_all
 theorem sub_outcomes (a b : BitVec w) (nsw nuw : Bool) :
    LLVM.Int.sub (.val a) (.val b) nsw nuw = .poison ∨
    LLVM.Int.sub (.val a) (.val b) nsw nuw = .val (a-b) := by
  simp only [LLVM.Int.sub,Id.run,pure]
  split <;> simp_all
end Veir.InstSimplify
