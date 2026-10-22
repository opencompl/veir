import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000

theorem gep_zero_size_static_refines (props : propertiesOf (.llvm .getelementptr : OpCode))
    (index : Int) (hindex : index ≠ -2147483648)
    (hraw : props.rawConstantIndices.values = #[index])
    (hsize : DataLayout.riscv64.getTypeAllocSize props.elem_type.val = some 0)
    (p : LLVM.Ptr) (v : RuntimeValue)
    (hi : InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)] #[.addr p] #[v]) :
    v ⊒ .addr p := by
  have he := hi.2 .empty
  cases p with
  | poison =>
    simp [interpretOp', Llvm.interpretOp', hraw, GEPIndex.decode, hindex, DataLayout.gepOffsets, Attribute.of, -Attribute.llvmArrayType_eq_of, hsize] at he
    subst v
    simp [RuntimeValue.isRefinedBy, isRefinedBy]
  | val p =>
    have hu : UInt64.ofInt (p.address.toNat : Int) = p.address := by
      have hlt : (p.address.toNat : Int) < 18446744073709551616 := by
        have := UInt64.toNat_lt p.address
        omega
      simp [UInt64.ofInt, Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt]
    simp [interpretOp', Llvm.interpretOp', hraw, GEPIndex.decode, hindex, DataLayout.gepOffsets, Attribute.of, -Attribute.llvmArrayType_eq_of, hsize, hu] at he
    subst v
    simp [RuntimeValue.isRefinedBy, isRefinedBy]

theorem gep_zero_size_dynamic_refines (props : propertiesOf (.llvm .getelementptr : OpCode))
    (hraw : props.rawConstantIndices.values = #[-2147483648])
    (hsize : DataLayout.riscv64.getTypeAllocSize props.elem_type.val = some 0)
    (p : LLVM.Ptr) (index : LLVM.Int w) (v : RuntimeValue)
    (hi : InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)] #[.addr p, .int w index] #[v]) :
    v ⊒ .addr p := by
  have he := hi.2 .empty
  cases p with
  | poison =>
    simp [interpretOp', Llvm.interpretOp', hraw, GEPIndex.decode, DataLayout.gepOffsets,
      Attribute.of, -Attribute.llvmArrayType_eq_of, hsize] at he
    subst v
    simp [RuntimeValue.isRefinedBy, isRefinedBy]
  | val p =>
    have hu : UInt64.ofInt (p.address.toNat : Int) = p.address := by
      have hlt : (p.address.toNat : Int) < 18446744073709551616 := by
        have := UInt64.toNat_lt p.address
        omega
      simp [UInt64.ofInt, Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt]
    cases index <;>
      simp [interpretOp', Llvm.interpretOp', hraw, GEPIndex.decode, DataLayout.gepOffsets,
        Attribute.of, -Attribute.llvmArrayType_eq_of, hsize, hu] at he <;>
      subst v <;> simp [RuntimeValue.isRefinedBy, isRefinedBy]

theorem gep_poison_base_static (props : propertiesOf (.llvm .getelementptr : OpCode)) (v : RuntimeValue)
    (hi : InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)] #[.addr .poison] #[v]) :
    v = .addr .poison := by
  have he := hi.2 .empty
  cases ho : DataLayout.riscv64.gepOffsets props.elem_type.val
      (GEPIndex.decode props.rawConstantIndices.values (#[] : Array RuntimeValue)) with
  | none => simp [interpretOp', Llvm.interpretOp', ho] at he
  | some offsets =>
    rcases offsets with ⟨offset,dynamic⟩
    simpa [interpretOp', Llvm.interpretOp', ho] using he.symm

theorem ptr_poison_iff (props : propertiesOf (.llvm .mlir__poison : OpCode)) (v : RuntimeValue) :
    InterpretsTo (.llvm .mlir__poison) props #[(LLVM.PointerType.mk : TypeAttr)] #[] #[v] ↔
      v = .addr .poison := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp', Attribute.of, -Attribute.llvmPointerType_eq_of, -Attribute.integerType_eq_of, RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem gep_poison_base_refines (props : propertiesOf (.llvm .getelementptr : OpCode))
    (indices : Array RuntimeValue) (v : RuntimeValue)
    (hi : InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)]
      (#[.addr .poison] ++ indices) #[v]) : v = .addr .poison := by
  have he := hi.2 .empty
  cases ho : DataLayout.riscv64.gepOffsets props.elem_type.val
      (GEPIndex.decode props.rawConstantIndices.values indices) with
  | none => simp [interpretOp', Llvm.interpretOp', ho] at he
  | some offsets =>
    rcases offsets with ⟨offset,dynamic⟩
    simpa [interpretOp', Llvm.interpretOp', ho] using he.symm

end Veir.InstSimplify
