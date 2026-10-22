import Veir.InstSimplify.GEPSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- One static index into a zero-allocation element type, with arbitrary index and no-wrap flags. -/
def IS5359_static (index : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType)
    let p ← MatchProg.value ty
    let r ← MatchProg.root (.llvm .getelementptr) #[p] #[ty]
      (fun props => props.rawConstantIndices.values == #[index] && index != -2147483648 &&
        DataLayout.riscv64.getTypeAllocSize props.elem_type.val == some 0)
    return p)
  pure (fun p => p)

theorem IS5359_static_valid (index : Int) : Pattern.Valid (IS5359_static index) := by
  simp only [IS5359_static]
  provePuddleValid
  rintro ⟨⟩
  simp only [RuntimeValue.Conforms.llvmPointerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro p rp rv hraw hindex hsize hi
  exact gep_zero_size_static_refines rp index (by simpa using hindex) hraw hsize p rv hi

/-- One dynamic index into a zero-allocation element type, every scalar index width and poison included. -/
def IS5359_dynamic : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType)
    let ity ← MatchProg.type (Attr := IntegerType)
    let p ← MatchProg.value ty
    let index ← MatchProg.value ity
    let _ ← MatchProg.root (.llvm .getelementptr) #[p,index] #[ty]
      (fun props => props.rawConstantIndices.values == #[-2147483648] &&
        DataLayout.riscv64.getTypeAllocSize props.elem_type.val == some 0)
    return p)
  pure (fun p => p)

theorem IS5359_dynamic_valid : Pattern.Valid IS5359_dynamic := by
  simp only [IS5359_dynamic]
  provePuddleValid
  rintro ⟨⟩ ⟨w,s⟩
  simp only [RuntimeValue.Conforms.llvmPointerType, RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  intro p index rp rv hraw hsize hi
  exact gep_zero_size_dynamic_refines rp hraw hsize p index rv hi
end Veir.InstSimplify
