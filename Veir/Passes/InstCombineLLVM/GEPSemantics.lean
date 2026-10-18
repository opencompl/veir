module

public import Veir.Passes.InstCombineLLVM.Semantics
public import Veir.DataLayout.RISCV64
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.GEPSemantics

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- Property bundle for a scalar one-dynamic-index, unflagged GEP. -/
@[expose] public def dynamicGepProperties (elementType : TypeAttr) : GetelementptrProperties :=
  { rawConstantIndices :=
      { elementType := IntegerType.signless 32, values := #[(-2147483648 : Int)] }
    elem_type := elementType
    noWrapFlags := { value := 0, type := IntegerType.signless 32 } }

@[expose] public def dynamicGepI8Properties : GetelementptrProperties :=
  dynamicGepProperties ({ bitwidth := 8, signedness := .signless } : IntegerType)

@[expose] public def dynamicGepI32Properties : GetelementptrProperties :=
  dynamicGepProperties ({ bitwidth := 32, signedness := .signless } : IntegerType)

/-- The pointer result used by Puddle's modeled one-index scalar GEP. -/
@[expose] public def gepResult {w : Nat} (stride : Nat) (ptr : LLVM.Ptr)
    (idx : LLVM.Int w) : LLVM.Ptr :=
  match ptr, idx with
  | .val ptr, .val idx =>
      .val ⟨ptr.object, UInt64.ofNat (ptr.address.toNat + idx.toNat * stride)⟩
  | _, _ => .poison

/-- Address addition distributes over an unflagged integer add at pointer-index width. -/
public theorem gepResult_add_i64 (stride : Nat) (ptr : LLVM.Ptr)
    (x y : LLVM.Int 64) :
    gepResult stride ptr (LLVM.Int.add x y false false) =
      gepResult stride (gepResult stride ptr x) y := by
  cases ptr <;> cases x <;> cases y <;>
    simp [gepResult, LLVM.Int.add, Id.run]
  simp only [UInt64.ofNat_mod_size', UInt64.ofNat_add, UInt64.ofNat_mul,
    UInt64.ofNat_toNat]
  simp
  rw [UInt64.add_mul]
  ac_rfl

public theorem gep_iff {w : Nat} (ptrTy : LLVM.PointerType)
    (props : GetelementptrProperties) (stride : Nat)
    (hStride : DataLayout.riscv64.getTypeAllocSize props.elem_type.val = some stride)
    (ptr : LLVM.Ptr) (idx : LLVM.Int w) (result : RuntimeValue) :
    InterpretsTo (.llvm .getelementptr) props #[ptrTy]
      #[.addr ptr, .int w idx] #[result] ↔
      result = .addr (gepResult stride ptr idx) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_add_one,
    Nat.lt_one_iff, RuntimeValue.Conforms, List.getElem!_toArray,
    List.getElem!_eq_getElem?_getD, getElem?_pos, List.getElem_cons_zero,
    List.getElem_cons_succ, Option.getD_some, forall_eq, true_and,
    interpretOp', Llvm.interpretOp', hStride, Interp.pure_eq, Interp.ok.injEq,
    Prod.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    have hv := h .empty
    cases ptr <;> cases idx <;> simp [gepResult] at hv ⊢ <;> exact hv.symm
  · rintro rfl
    constructor
    · exact RuntimeValue.Conforms.llvmPointerType.mpr ⟨gepResult stride ptr idx, rfl⟩
    · intro memory
      cases ptr <;> cases idx <;> simp [gepResult]

@[simp] public theorem gep_i8_iff {w : Nat} (ptrTy : LLVM.PointerType)
    (ptr : LLVM.Ptr) (idx : LLVM.Int w) (result : RuntimeValue) :
    InterpretsTo (.llvm .getelementptr) dynamicGepI8Properties #[ptrTy]
      #[.addr ptr, .int w idx] #[result] ↔
      result = .addr (gepResult 1 ptr idx) := by
  apply gep_iff
  simpa [dynamicGepI8Properties, dynamicGepProperties, TypeAttr.of_val] using
    DataLayout.riscv64_getTypeAllocSize_i8

@[simp] public theorem gep_i32_iff {w : Nat} (ptrTy : LLVM.PointerType)
    (ptr : LLVM.Ptr) (idx : LLVM.Int w) (result : RuntimeValue) :
    InterpretsTo (.llvm .getelementptr) dynamicGepI32Properties #[ptrTy]
      #[.addr ptr, .int w idx] #[result] ↔
      result = .addr (gepResult 4 ptr idx) := by
  apply gep_iff
  simpa [dynamicGepI32Properties, dynamicGepProperties, TypeAttr.of_val] using
    DataLayout.riscv64_getTypeAllocSize_i32

end Veir.Passes.InstCombineLLVM.GEPSemantics
