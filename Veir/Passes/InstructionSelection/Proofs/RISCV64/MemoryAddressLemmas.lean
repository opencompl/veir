module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Interfaces.DataLayoutInterfaces
import all Veir.Data.Pointer.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Casting
import all Init.Data.UInt.Basic

namespace Veir

attribute [local implicit_reducible] TypeAttr

private def mapIndex (f : α → β) : GEPIndex α → GEPIndex β
  | .const c => .const c
  | .dynamic x => .dynamic (f x)

private def decodeStep [Inhabited α] (dynamic : Array α)
    (s : Nat × Array (GEPIndex α)) (raw : Int) : Nat × Array (GEPIndex α) :=
  if raw = -2147483648 then (s.1 + 1, s.2.push (.dynamic dynamic[s.1]!))
  else (s.1, s.2.push (.const raw))

private theorem decode_fold [Inhabited α] (raw : Array Int) (dynamic : Array α) :
    GEPIndex.decode raw dynamic = (raw.foldl (decodeStep dynamic) (0, #[])).2 := by
  unfold GEPIndex.decode
  simp only [←apply_ite (pure (f := Id)), ←apply_ite ForInStep.yield,
    Array.forIn_pure_yield_eq_foldl]
  rfl

private theorem decode_fold_map [Inhabited α] [Inhabited β] (f : α → β)
    (raw : List Int) (dynamic : Array α) (n : Nat) (out : Array (GEPIndex α))
    (h : n + (raw.filter (· == -2147483648)).length ≤ dynamic.size) :
    raw.foldl (decodeStep (dynamic.map f)) (n, out.map (mapIndex f)) =
      let result := raw.foldl (decodeStep dynamic) (n, out)
      (result.1, result.2.map (mapIndex f)) := by
  induction raw generalizing n out with
  | nil => rfl
  | cons a raw ih =>
    by_cases ha : a = -2147483648
    · have hn : n < dynamic.size := by simp [ha] at h; grind
      simp only [List.foldl_cons, decodeStep, ha, ↓reduceIte]
      simpa [mapIndex, Array.map_push, getElem!_pos, hn] using
        ih (n + 1) (out.push (.dynamic dynamic[n]!)) (by simp [ha] at h; grind)
    · simp only [List.foldl_cons, decodeStep, ha, ↓reduceIte]
      simpa [mapIndex, Array.map_push] using
        ih n (out.push (.const a)) (by simpa [ha] using h)

private theorem decode_map [Inhabited α] [Inhabited β] (f : α → β)
    (raw : Array Int) (dynamic : Array α)
    (h : (raw.filter (· == -2147483648)).size ≤ dynamic.size) :
    GEPIndex.decode raw (dynamic.map f) = (GEPIndex.decode raw dynamic).map (mapIndex f) := by
  simp only [decode_fold, ←Array.foldl_toList]
  have hm := decode_fold_map f raw.toList dynamic 0 #[]
    (by simpa only [←Array.toList_filter, Array.length_toList, Nat.zero_add] using h)
  simpa using congrArg Prod.snd hm

private def mapStep (f : σ → τ) : ForInStep σ → ForInStep τ
  | .done s => .done (f s)
  | .yield s => .yield (f s)

private theorem forIn_state_map (xs : List α) (f : σ → τ)
    (step : α → σ → Option (ForInStep σ)) (step' : α → τ → Option (ForInStep τ))
    (h : ∀ a s, step' a (f s) = (step a s).map (mapStep f)) (init : σ) :
    forIn xs (f init) step' = (forIn xs init step).map f := by
  induction xs generalizing init with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.forIn_cons, h]
    cases he : step a init with
    | none => simp [he]
    | some s => cases s <;> simp [he, mapStep, ih]

private def gepStep (layout : DataLayout) (index : GEPIndex α)
    (s : Int × Array (α × Nat) × Attribute) : Option (ForInStep (Int × Array (α × Nat) × Attribute)) := do
  match s.2.2, index with
  | .llvmArrayType {type, ..}, index =>
    let stride ← layout.getTypeAllocSize type
    match index with
    | .const c => return .yield (s.1 + c * stride, s.2.1, type)
    | .dynamic v => return .yield (s.1, s.2.1.push (v, stride), type)
  | .llvmStructType {packed, body, ..}, .const c =>
    let (offsets, _) := structLayout (←body.mapM layout.query) packed
    return .yield (s.1 + offsets[c.toNat]!, s.2.1, body[c.toNat]!)
  | _, _ => none

private theorem gepOffsets_forIn (layout : DataLayout) (ty : Attribute) (xs : Array (GEPIndex α)) :
    layout.gepOffsets ty xs = do
      let s ← forIn xs (0, #[], Attribute.llvmArrayType {size := 0, type := ty}) (gepStep layout)
      return (s.1, s.2.1) := by
  unfold DataLayout.gepOffsets gepStep
  rfl

private def mapGepState (f : α → β) (s : Int × Array (α × Nat) × Attribute) :
    Int × Array (β × Nat) × Attribute :=
  (s.1, s.2.1.map (fun (a, n) => (f a, n)), s.2.2)

private theorem gepStep_map (f : α → β) (layout : DataLayout) (index : GEPIndex α)
    (s : Int × Array (α × Nat) × Attribute) :
    gepStep layout (mapIndex f index) (mapGepState f s) =
      (gepStep layout index s).map (mapStep (mapGepState f)) := by
  rcases s with ⟨offset, dynamic, ty⟩
  cases ty <;> cases index <;>
    simp only [gepStep, mapIndex, mapGepState, mapStep, Array.map_push,
      Option.map_bind, Option.map_some, Option.map_none, pure, Option.pure_def]
  all_goals rename_i type value
  all_goals cases type
  all_goals simp only [mapGepState, mapStep, Option.map_bind, Option.map_some,
    Array.map_push, bind, Option.bind]
  all_goals split <;> simp_all only [Option.map_none, Option.map_some,
    mapStep, mapGepState, Array.map_push]

private theorem gepOffsets_map (f : α → β) (layout : DataLayout)
    (ty : Attribute) (xs : Array (GEPIndex α)) :
    layout.gepOffsets ty (xs.map (mapIndex f)) =
      (layout.gepOffsets ty xs).map
        (fun (offset, dynamic) => (offset, dynamic.map (fun (a, n) => (f a, n)))) := by
  simp only [gepOffsets_forIn, Array.forIn_map, ←Array.forIn_toList]
  simp only [Array.toList_map, List.forIn_map]
  let init : Int × Array (α × Nat) × Attribute :=
    (0, #[], .llvmArrayType {size := 0, type := ty})
  have hm := forIn_state_map xs.toList (mapGepState f) (gepStep layout)
    (fun index => gepStep layout (mapIndex f index)) (gepStep_map f layout) init
  have hm' :
      forIn xs.toList (0, #[], Attribute.llvmArrayType {size := 0, type := ty})
        (fun index => gepStep layout (mapIndex f index)) =
      (forIn xs.toList init (gepStep layout)).map (mapGepState f) := by
    simpa only [init, mapGepState, Array.map_empty] using hm
  rw [hm']
  cases hloop : forIn xs.toList init (gepStep layout) <;> rfl

private def constantBits (idxs : Array GMIRConstantProperties) : Array (BitVec 64) :=
  idxs.map (fun idx => BitVec.ofInt 64 idx.value.value)

/-- Selection exposes the same offset decomposition as execution of constant indices. -/
theorem selectAddrRegImm_decomposition (gep : GetelementptrProperties)
    (idxs : Array GMIRConstantProperties) (off : Int)
    (hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ idxs.size)
    (hselect : selectAddrRegImm gep idxs = some off) :
    ∃ base dynamic,
      DataLayout.riscv64.gepOffsets gep.elem_type.val
        (GEPIndex.decode gep.rawConstantIndices.values (constantBits idxs)) = some (base, dynamic) ∧
      dynamic.foldl (fun n (b, stride) => n + b.toInt * stride) base = off ∧
      -2048 ≤ off ∧ off ≤ 2047 := by
  unfold selectAddrRegImm at hselect
  have hbits : idxs.map (fun idx => (BitVec.ofInt 64 idx.value.value).toInt) =
      (constantBits idxs).map BitVec.toInt := by
    simp only [constantBits, Array.map_map, Function.comp_def]
  rw [hbits] at hselect
  dsimp only at hselect
  rw [decode_map _ _ _ (by simpa only [constantBits, Array.size_map] using hcount),
    gepOffsets_map] at hselect
  cases hparts : DataLayout.riscv64.gepOffsets gep.elem_type.val
      (GEPIndex.decode gep.rawConstantIndices.values (constantBits idxs)) with
  | none => simp [hparts] at hselect
  | some parts =>
    rcases parts with ⟨base, dynamic⟩
    simp only [hparts, Option.map_some, bind, Option.bind] at hselect
    simp only [Array.foldl_map' rfl, Array.foldl_map] at hselect
    by_cases bounds : -2048 ≤ dynamic.foldl (fun n (b, stride) => n + b.toInt * stride) base ∧
        dynamic.foldl (fun n (b, stride) => n + b.toInt * stride) base ≤ 2047
    · simp [guard, bounds, pure, bind, Option.bind] at hselect
      exact ⟨base, dynamic, rfl, hselect, hselect ▸ bounds⟩
    · simp [guard, bounds, pure, bind, Option.bind] at hselect

private def gepRead (entry : RuntimeValue × Nat) : Option (Option Int × Nat) :=
  match entry.1 with
  | .int _ (.val bits) => some (some bits.toInt, entry.2)
  | .int _ .poison => some (none, entry.2)
  | _ => none

private theorem selectedGEP_indices (gep : GetelementptrProperties)
    (idxs : Array GMIRConstantProperties) (off : Int) (ptr : Data.LLVM.Ptr)
    (hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ idxs.size)
    (hselect : selectAddrRegImm gep idxs = some off) :
    let operands := #[RuntimeValue.addr ptr] ++
      idxs.map (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value)))
    ∃ (base : Int) (dynamic : Array (Option Nat × Nat)) (values : Array (BitVec 64 × Nat)),
      DataLayout.riscv64.gepOffsets gep.elem_type.val
        (GEPIndex.decode gep.rawConstantIndices.values
          ((Array.range (operands.size - 1)).map some)) = some (base, dynamic) ∧
      dynamic.mapM (Llvm.gepIndex operands) = some (values.map (fun (b, n) => (some b.toInt, n))) ∧
      values.foldl (fun n (entry : BitVec 64 × Nat) => n + entry.1.toInt * entry.2) base = off := by
  let bits := constantBits idxs
  let toValue := fun b : BitVec 64 => RuntimeValue.int 64 (.val b)
  let operands := #[RuntimeValue.addr ptr] ++ bits.map toValue
  let positions := (Array.range bits.size).map some
  have hsize : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ bits.size := by
    simpa [bits, constantBits] using hcount
  have hextract : operands.extract 1 = bits.map toValue := by
    simp [operands, Array.extract_append]
  have hread : positions.map (Llvm.gepOperand operands) = bits.map toValue := by
    apply Array.ext
    · simp [positions]
    · intro i hi hj
      have hiBits : i < bits.size := by simpa using hj
      simp [positions, Llvm.gepOperand, hextract, getElem!_pos, hiBits]
  have hdecode : (GEPIndex.decode gep.rawConstantIndices.values positions).map
      (mapIndex (Llvm.gepOperand operands)) =
      (GEPIndex.decode gep.rawConstantIndices.values bits).map (mapIndex toValue) := by
    rw [←decode_map _ _ _ (by simpa [positions] using hsize), hread,
      decode_map _ _ _ hsize]
  obtain ⟨base, values, hparts, hoff, _⟩ :=
    selectAddrRegImm_decomposition gep idxs off hcount hselect
  have heq := congrArg (DataLayout.riscv64.gepOffsets gep.elem_type.val) hdecode
  rw [gepOffsets_map, gepOffsets_map, hparts] at heq
  cases hp : DataLayout.riscv64.gepOffsets gep.elem_type.val
      (GEPIndex.decode gep.rawConstantIndices.values positions) with
  | none => simp [hp] at heq
  | some parts =>
    rcases parts with ⟨base', dynamic⟩
    simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, hvalues⟩ := heq
    have hindices : dynamic.mapM (Llvm.gepIndex operands) =
        some (values.map (fun (b, n) => (some b.toInt, n))) := by
      calc
        _ = (dynamic.map (fun (a, n) => (Llvm.gepOperand operands a, n))).mapM gepRead := by
          rw [Array.mapM_map]
          rfl
        _ = _ := by
          rw [hvalues]
          rw [Array.mapM_map]
          change values.mapM (pure ∘ fun x => (some x.1.toInt, x.2)) = _
          exact Array.mapM_pure
    refine ⟨base', dynamic, values, ?_, ?_, hoff⟩
    · simpa [operands, positions, bits, constantBits, toValue] using hp
    · simpa [operands, bits, constantBits, toValue, Array.map_map, Function.comp_def] using hindices

/-- The selected immediate computes the same address as the matched constant-index GEP. -/
theorem interpretGEP_selected (gep : GetelementptrProperties) (idxs : Array GMIRConstantProperties)
    (off : Int) (types : Array TypeAttr) (memory : MemoryState) (p : Data.Pointer)
    (hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ idxs.size)
    (hselect : selectAddrRegImm gep idxs = some off) :
    Llvm.interpretOp' .getelementptr gep types
      (#[.addr (.val p)] ++ idxs.map (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))))
      #[] memory DataLayout.riscv64 =
      Interp.ok (#[.addr (.val ⟨UInt64.ofInt (p.address.toNat + off)⟩)], memory, none) := by
  obtain ⟨base, dynamic, values, hparts, hindices, hoff⟩ :=
    selectedGEP_indices gep idxs off (.val p) hcount hselect
  simp only [Llvm.interpretOp', Array.toList_append, List.singleton_append, hparts,
    Interp.liftOption_some, Interp.bind_ok, hindices, Array.mapM_map, Function.comp_def,
    Option.map_some]
  rw [show values.mapM (fun x => some (x.1.toInt * (x.2 : Int))) =
    some (values.map (fun x => x.1.toInt * (x.2 : Int))) from Array.mapM_pure]
  simp only [Interp.pure_eq]
  congr 4
  rw [←hoff, Array.foldl_map]
  have hfold := Array.foldl_hom (fun n : Int => base + n)
    (g₁ := fun n (entry : BitVec 64 × Nat) => n + entry.1.toInt * entry.2)
    (g₂ := fun n (entry : BitVec 64 × Nat) => n + entry.1.toInt * entry.2)
    (by intros; simp only [Int.add_assoc]) (xs := values) (init := 0)
  simp only [Int.add_zero] at hfold
  rw [hfold]
  simp [Int.add_assoc]

/-- A selected GEP preserves a poison base, so a following memory access has source UB. -/
theorem interpretGEP_selected_poison (gep : GetelementptrProperties) (idxs : Array GMIRConstantProperties)
    (off : Int) (types : Array TypeAttr) (memory : MemoryState)
    (hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ idxs.size)
    (hselect : selectAddrRegImm gep idxs = some off) :
    Llvm.interpretOp' .getelementptr gep types
      (#[.addr .poison] ++ idxs.map (fun idx => RuntimeValue.int 64 (.val (BitVec.ofInt 64 idx.value.value))))
      #[] memory DataLayout.riscv64 = Interp.ok (#[.addr .poison], memory, none) := by
  obtain ⟨base, dynamic, values, hparts, hindices, _⟩ :=
    selectedGEP_indices gep idxs off .poison hcount hselect
  simp only [Llvm.interpretOp', Array.toList_append, List.singleton_append, hparts,
    Interp.liftOption_some, Interp.bind_ok, hindices, Interp.pure_eq]

/-- A selected signed twelve-bit offset is unchanged by the memory instruction field. -/
theorem selectedOffset_signExtend (gep : GetelementptrProperties) (idxs : Array GMIRConstantProperties)
    (off : Int) (hcount : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ idxs.size)
    (hselect : selectAddrRegImm gep idxs = some off) :
    ((BitVec.ofInt 64 off).setWidth 12).signExtend 64 = BitVec.ofInt 64 off := by
  obtain ⟨_, _, _, _, lo, hi⟩ := selectAddrRegImm_decomposition gep idxs off hcount hselect
  have hmod : off.bmod (2 ^ 64) = off := Int.bmod_eq_of_le
    (by change -9223372036854775808 ≤ off; grind)
    (by change off < 9223372036854775808; grind)
  have lo' : (-2048#64).sle (BitVec.ofInt 64 off) := by
    simpa [BitVec.sle_iff_toInt_le, BitVec.toInt_ofInt, hmod] using lo
  have hi' : (BitVec.ofInt 64 off).sle 2047#64 := by
    simpa [BitVec.sle_iff_toInt_le, BitVec.toInt_ofInt, hmod] using hi
  generalize BitVec.ofInt 64 off = bits at lo' hi' ⊢
  veir_bv_decide

/-- The LLVM integer-address calculation and RISC-V modular addition agree. -/
theorem pointer_add_offset (address : UInt64) (off : Int) :
    UInt64.ofInt (address.toNat + off) =
      UInt64.ofBitVec (address.toBitVec + BitVec.ofInt 64 off) := by
  have ofInt_bits (n : Int) : UInt64.ofInt n = UInt64.ofBitVec (BitVec.ofInt 64 n) := by
    apply UInt64.toNat_inj.mp
    simp [UInt64.ofInt, BitVec.ofInt]
    exact Int.emod_lt_of_pos n (by veir_bv_decide)
  rw [ofInt_bits, BitVec.ofInt_add]
  simp

end Veir
