import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0767
/-- X-X → 0, all scalar widths and all overflow flags. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .sub) #[x,x] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x p v hi
  obtain rfl := (sub_iff w p x x v).mp hi
  exists (.int w (.val (BitVec.ofNat w 0)))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, isRefinedBy, Id.run, pure]
    grind
end Veir.InstSimplify.IS0767
