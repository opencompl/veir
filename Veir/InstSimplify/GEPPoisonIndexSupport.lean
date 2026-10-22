import Veir.InstSimplify.GEPZeroSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

private theorem gep_decode_coverage {α : Type} [Inhabited α]
    (raw : List Int) (dynamic : Array α) (b : Nat × Array (GEPIndex α))
    (hb : ∀ j < b.1, GEPIndex.dynamic dynamic[j]! ∈ b.2) :
    (raw.foldl (gepDecodeStep dynamic) b).1 = b.1 + (raw.filter (· == -2147483648)).length ∧
    ∀ j < (raw.foldl (gepDecodeStep dynamic) b).1,
      GEPIndex.dynamic dynamic[j]! ∈ (raw.foldl (gepDecodeStep dynamic) b).2 := by
  induction raw generalizing b with
  | nil => exact ⟨by simp, hb⟩
  | cons a raw ih =>
    by_cases ha : a = -2147483648
    · subst a
      have hn : ∀ j < b.1 + 1, GEPIndex.dynamic dynamic[j]! ∈ b.2.push (.dynamic dynamic[b.1]!) := by
        intro j hj
        by_cases hlt : j < b.1
        · exact Array.mem_push.mpr (Or.inl (hb j hlt))
        · have he : j = b.1 := by omega
          subst j
          simp
      obtain ⟨hc, hm⟩ := ih (b.1+1,b.2.push (.dynamic dynamic[b.1]!)) hn
      constructor
      · simpa [gepDecodeStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
      · simpa [gepDecodeStep] using hm
    · have hn : ∀ j < b.1, GEPIndex.dynamic dynamic[j]! ∈ b.2.push (.const a) := by
        intro j hj
        exact Array.mem_push.mpr (Or.inl (hb j hj))
      obtain ⟨hc, hm⟩ := ih (b.1,b.2.push (.const a)) hn
      constructor
      · simpa [gepDecodeStep, ha] using hc
      · simpa [gepDecodeStep, ha] using hm

private theorem gep_decode_dynamic_mem {α : Type} [Inhabited α]
    (raw : Array Int) (dynamic : Array α)
    (hcount : (raw.filter (· == -2147483648)).size = dynamic.size)
    (a : α) (ha : a ∈ dynamic) : .dynamic a ∈ GEPIndex.decode raw dynamic := by
  obtain ⟨j,hj,he⟩ := Array.mem_iff_getElem.mp ha
  have hc : (raw.toList.filter (· == -2147483648)).length = dynamic.size := by
    have hc : (raw.filter (· == -2147483648)).toList.length = dynamic.size := hcount
    rw [Array.toList_filter] at hc
    exact hc
  obtain ⟨hn,hm⟩ := gep_decode_coverage raw.toList dynamic (0,#[]) (by simp)
  rw [gep_decode_eq_foldl, ← Array.foldl_toList]
  have hj' : j < (raw.toList.foldl (gepDecodeStep dynamic) (0,#[])).1 := by
    rw [hn,hc]
    simpa using hj
  have hp := hm j hj'
  simpa [getElem!_pos dynamic j hj,he] using hp

private theorem gep_layout_step_tracks {α : Type} (layout : DataLayout)
    (index : GEPIndex α) (s : GEPLayoutState α) (v : α) :
    gepLayoutStep layout index s = none ∨ ∃ next,
      gepLayoutStep layout index s = some (.yield next) ∧
      ((∃ stride, (v,stride) ∈ s.2.1) → ∃ stride, (v,stride) ∈ next.2.1) ∧
      (index = .dynamic v → ∃ stride, (v,stride) ∈ next.2.1) := by
  rcases s with ⟨offset,dynamic,outer⟩
  cases outer <;> cases index <;>
    simp [gepLayoutStep, -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]
  case llvmArrayType.const t c =>
    rcases t with ⟨n,ty⟩
    cases h : layout.getTypeAllocSize ty <;>
      simp [h, -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]
    exact ⟨_,dynamic,⟨rfl,rfl⟩,fun n hn => ⟨n,hn⟩⟩
  case llvmArrayType.dynamic t a =>
    rcases t with ⟨n,ty⟩
    cases h : layout.getTypeAllocSize ty with
    | none => simp [h]
    | some stride =>
      simp [h]
      refine ⟨offset,dynamic.push (a,stride),⟨rfl,rfl⟩,?_,?_⟩
      · intro n hn
        exact ⟨n, Array.mem_push.mpr (Or.inl hn)⟩
      · intro he
        subst a
        exact ⟨stride, by simp⟩
  case llvmStructType.const t c =>
    rcases t with ⟨name,packed,body⟩
    cases h : body.mapM layout.query <;>
      simp [h, -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]
    exact ⟨_,dynamic,⟨rfl,rfl⟩,fun n hn => ⟨n,hn⟩⟩

private theorem gep_layout_loop_tracks {α : Type} (layout : DataLayout)
    (indices : List (GEPIndex α)) (s : GEPLayoutState α) (v : α)
    (hp : .dynamic v ∈ indices ∨ ∃ stride, (v,stride) ∈ s.2.1) :
    forIn indices s (gepLayoutStep layout) = none ∨ ∃ next,
      forIn indices s (gepLayoutStep layout) = some next ∧
      ∃ stride, (v,stride) ∈ next.2.1 := by
  induction indices generalizing s with
  | nil =>
    right
    exact ⟨s,rfl, hp.resolve_left (by simp)⟩
  | cons a indices ih =>
    rcases gep_layout_step_tracks layout a s v with hn | ⟨next,hn,hpres,hnew⟩
    · left
      rw [List.forIn_cons,hn]
      rfl
    · have hp' : .dynamic v ∈ indices ∨ ∃ stride, (v,stride) ∈ next.2.1 := by
        rcases hp with hp | hp
        · rcases List.mem_cons.mp hp with he | ht
          · exact Or.inr (hnew he.symm)
          · exact Or.inl ht
        · exact Or.inr (hpres hp)
      rcases ih next hp' with hl | ⟨last,hl,hp⟩
      · left
        rw [List.forIn_cons,hn]
        exact hl
      · right
        refine ⟨last,?_,hp⟩
        rw [List.forIn_cons,hn]
        exact hl

private theorem gep_offsets_dynamic_mem {α : Type} (layout : DataLayout)
    (elem : Attribute) (indices : Array (GEPIndex α)) (v : α) (hp : .dynamic v ∈ indices) :
    layout.gepOffsets elem indices = none ∨ ∃ offset dynamic,
      layout.gepOffsets elem indices = some (offset,dynamic) ∧
      ∃ stride, (v,stride) ∈ dynamic := by
  have hl : forIn indices (0,#[],.llvmArrayType {size := 0,type := elem}) (gepLayoutStep layout) = none ∨
      ∃ next, forIn indices (0,#[],.llvmArrayType {size := 0,type := elem}) (gepLayoutStep layout) = some next ∧
        ∃ stride, (v,stride) ∈ next.2.1 := by
    cases indices with
    | mk indices =>
      simpa only [List.forIn_toArray] using gep_layout_loop_tracks layout indices
        (0,#[],.llvmArrayType {size := 0,type := elem}) v (Or.inl (by simpa using hp))
  unfold DataLayout.gepOffsets
  change (do let st ← forIn indices (0,#[],.llvmArrayType {size := 0,type := elem}) (gepLayoutStep layout)
             pure (st.1,st.2.1)) = none ∨ _
  rcases hl with hn | ⟨next,hn,hp⟩
  · left
    rw [hn]
    rfl
  · right
    refine ⟨next.1,next.2.1,?_,hp⟩
    change (do let st ← forIn indices (0,#[],.llvmArrayType {size := 0,type := elem}) (gepLayoutStep layout)
               pure (st.1,st.2.1)) = some (next.1,next.2.1)
    rw [hn]
    rfl

private def gepPoisonAddressStep (mem : MemoryState) (pair : RuntimeValue × Nat)
    (s : Option (Array RuntimeValue × MemoryState × Option ControlFlowAction) × Int) :
    Interp (ForInStep (Option (Array RuntimeValue × MemoryState × Option ControlFlowAction) × Int)) :=
  match pair.1 with
  | .int _ index =>
    match index with
    | .val index => .ok (.yield (none,s.2 + index.toInt * pair.2))
    | _ => .ok (.done (some (#[.addr .poison],mem,none),s.2))
  | _ => .fail none

private theorem gep_address_poison_loop_list (mem : MemoryState)
    (dynamic : List (RuntimeValue × Nat))
    (hp : ∃ w stride, (RuntimeValue.int w .poison,stride) ∈ dynamic) (address : Int) :
    forIn dynamic (none,address) (gepPoisonAddressStep mem) = .fail none ∨ ∃ last,
      forIn dynamic (none,address) (gepPoisonAddressStep mem) =
        .ok (some (#[.addr .poison],mem,none),last) := by
  induction dynamic generalizing address with
  | nil => simp at hp
  | cons pair dynamic ih =>
    rcases pair with ⟨value,stride⟩
    by_cases hh : ∃ w, value = .int w .poison
    · obtain ⟨w,rfl⟩ := hh
      right
      exact ⟨address, by simp [List.forIn_cons,gepPoisonAddressStep]⟩
    · have ht : ∃ w stride, (RuntimeValue.int w .poison,stride) ∈ dynamic := by
        obtain ⟨w,n,hm⟩ := hp
        rcases List.mem_cons.mp hm with he | hm
        · have hv : value = .int w .poison := (Prod.mk.inj he).1.symm
          exact False.elim (hh ⟨w,hv⟩)
        · exact ⟨w,n,hm⟩
      cases value <;> simp [List.forIn_cons,gepPoisonAddressStep]
      case int w index =>
        cases index with
        | poison => exact False.elim (hh ⟨w,rfl⟩)
        | val index =>
          simpa [List.forIn_cons,gepPoisonAddressStep] using ih ht (address + index.toInt * stride)

private theorem gep_address_poison_loop (mem : MemoryState)
    (dynamic : Array (RuntimeValue × Nat))
    (hp : ∃ w stride, (RuntimeValue.int w .poison,stride) ∈ dynamic) (address : Int) :
    forIn dynamic (none,address) (gepPoisonAddressStep mem) = .fail none ∨ ∃ last,
      forIn dynamic (none,address) (gepPoisonAddressStep mem) =
        .ok (some (#[.addr .poison],mem,none),last) := by
  cases dynamic with
  | mk dynamic =>
    simpa only [List.forIn_toArray] using gep_address_poison_loop_list mem dynamic (by simpa using hp) address

theorem gep_poison_index_refines (props : propertiesOf (.llvm .getelementptr : OpCode))
    (indices : Array RuntimeValue)
    (hcount : (props.rawConstantIndices.values.filter (· == -2147483648)).size = indices.size)
    (hp : ∃ w, RuntimeValue.int w .poison ∈ indices)
    (p : LLVM.Ptr) (v : RuntimeValue)
    (hi : InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)]
      (#[.addr p] ++ indices) #[v]) : v = .addr .poison := by
  obtain ⟨w,hp⟩ := hp
  have hd := gep_decode_dynamic_mem props.rawConstantIndices.values indices hcount (RuntimeValue.int w .poison) hp
  have he := hi.2 .empty
  rcases gep_offsets_dynamic_mem DataLayout.riscv64 props.elem_type.val _ (RuntimeValue.int w .poison) hd with
    hn | ⟨offset,dynamic,hn,stride,hp⟩
  · simp [interpretOp', Llvm.interpretOp',hn] at he
  · cases p with
    | poison => simpa [interpretOp',Llvm.interpretOp',hn] using he.symm
    | val p =>
      have hl := gep_address_poison_loop MemoryState.empty dynamic ⟨w,stride,hp⟩
        ((p.address.toNat : Int) + offset)
      simp [interpretOp',Llvm.interpretOp',hn] at he
      conv at he =>
        lhs
        arg 1
        arg 3
        tactic =>
          refine show _ = gepPoisonAddressStep MemoryState.empty from ?_
          funext x s
          rcases x with ⟨value,stride⟩
          cases value <;> try rfl
      rcases hl with hl | ⟨last,hl⟩
      · rw [hl] at he
        simp at he
      · rw [hl] at he
        simpa using he.symm

end Veir.InstSimplify
