import Veir.InstSimplify.ArithmeticSupport

open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

/-- Forgetting `disjoint` can only refine an LLVM bitwise or. -/
theorem or_refines_plain (w : Nat) (x y : LLVM.Int w) (d : Bool) :
    RuntimeValue.int w (LLVM.Int.or x y d) ⊒
      .int w (LLVM.Int.or x y false) := by
  cases x <;> cases y <;>
    simp only [LLVM.Int.or, Id.run, pure] <;>
    (try simp only [Bool.false_eq_true, false_and, ↓reduceIte]) <;>
    (try split) <;> simp [RuntimeValue.isRefinedBy, isRefinedBy]


 theorem and_self_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and x x) ⊒ .int w x := by
  cases x <;> simp [LLVM.Int.and, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.InstSimplify

namespace Veir.InstSimplify
 theorem const_negOne (w : Nat) : BitVec.ofInt w (-1) = BitVec.allOnes w := by
  simpa using (BitVec.ofInt_negSucc_eq_not_ofNat (w := w) (n := 0))
end Veir.InstSimplify

namespace Veir.InstSimplify

theorem logic_icmp_iff {t : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .icmp : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .icmp) props #[IntegerType.mk 1 t] #[.int w x, .int w y] #[v] ↔
      v = .int 1 (LLVM.Int.icmp x y props.predicate) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind
end Veir.InstSimplify
namespace Veir.InstSimplify
 theorem logic_and_comm (a b : LLVM.Int w) : LLVM.Int.and a b = LLVM.Int.and b a := by
  cases a <;> cases b <;> simp [LLVM.Int.and, Id.run, pure, BitVec.and_comm]
 theorem logic_xor_comm (a b : LLVM.Int w) : LLVM.Int.xor a b = LLVM.Int.xor b a := by
  cases a <;> cases b <;> simp [LLVM.Int.xor, Id.run, pure, BitVec.xor_comm]
 theorem logic_or_comm (a b : LLVM.Int w) (d : Bool) : LLVM.Int.or a b d = LLVM.Int.or b a d := by
  cases a <;> cases b <;> simp [LLVM.Int.or, Id.run, pure, BitVec.and_comm, BitVec.or_comm]
end Veir.InstSimplify
namespace Veir.InstSimplify
/-- Interpret a scalar APInt metadata guard in the defining module. -/
def bitConstantGuard (ty : TypeAttr) (p : propertiesOf (.llvm .mlir__constant : OpCode)) (n : Int) : Bool :=
  match ty.val,p.value with
  | .integerType t, .integer a => BitVec.ofInt t.bitwidth a.value == BitVec.ofInt t.bitwidth n
  | _,_ => false

/-- Match APInt bits, respecting normalized signed, unsigned, and i1 spellings. -/
def matchBitConstant (ty : Handle OpCode .type) (n : Int) : MatchProg.Builder (Handle OpCode .value) := do
  let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
  MatchProg.matchNative (ty,c.properties) (fun (ty,p) => bitConstantGuard ty p n)
  return c.res[0]!

theorem matched_bit_constant_eq (ty : IntegerType) (p : propertiesOf (.llvm .mlir__constant : OpCode))
    (n : Int) (v : RuntimeValue) (hi : InterpretsTo (.llvm .mlir__constant) p #[ty] #[] #[v])
    (hc : bitConstantGuard ty p n = true) :
    v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth n)) := by
  cases hp : p.value with
  | integer a =>
    have hc : BitVec.ofInt ty.bitwidth a.value = BitVec.ofInt ty.bitwidth n := by
      simpa [bitConstantGuard, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, hp] using hc
    simpa [hc] using (constant_iff ty p a hp v).mp hi
  | _ => simp [bitConstantGuard, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, hp] at hc
end Veir.InstSimplify
namespace Veir.InstSimplify
 theorem bitvec_zero_test (y : BitVec w) : (y == 0) = decide (y.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp [← BitVec.toNat_inj]
end Veir.InstSimplify
