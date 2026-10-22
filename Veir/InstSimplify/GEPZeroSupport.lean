import Veir.InstSimplify.GEPSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
theorem gep_align_zero (a : Nat) : alignTo 0 a = 0 := by
  by_cases ha : a = 0
  · simp [alignTo, ha]
  · simp [alignTo, ha, Nat.div_eq_of_lt (show a-1 < a by omega)]
theorem gep_struct_first_offset (fields : Array DataLayoutTypeInfo) (packed : Bool) :
    (structLayout fields packed).1[0]! = 0 := by
  unfold structLayout
  simp only [Array.forIn_pure_yield_eq_foldl, bind, pure, Id.run]
  have h := Array.foldl_induction (as := fields)
    (motive := fun _ (b : Array Nat × Nat × Nat) =>
      (b.1.size = 0 → b.2.1 = 0) ∧ b.1[0]! = 0)
    (init := (#[], 0, 1))
    (h0 := by simp)
    (f := fun b a => (b.1.push (alignTo b.2.1 (if packed then 1 else a.abiAlignment)),
      alignTo b.2.1 (if packed then 1 else a.abiAlignment) + a.allocSize,
      max b.2.2 (if packed then 1 else a.abiAlignment)))
    (hf := by
      intro i b hb
      constructor
      · simp
      · by_cases hz : b.1.size = 0
        · have he : b.1 = #[] := Array.eq_empty_of_size_eq_zero hz
          simp [he, hb.1 hz, gep_align_zero]
        · have hpos : 0 < b.1.size := by omega
          simpa [getElem!_pos, Array.getElem_push_lt, hpos] using hb.2)
  change ((forIn fields (#[], 0, 1) (fun a b => pure (ForInStep.yield
    (b.1.push (alignTo b.2.1 (if packed then 1 else a.abiAlignment)),
      alignTo b.2.1 (if packed then 1 else a.abiAlignment) + a.allocSize,
      max b.2.2 (if packed then 1 else a.abiAlignment)))) : Id (Array Nat × Nat × Nat)).run).1[0]! = 0
  rw [Array.forIn_pure_yield_eq_foldl]
  exact h.2

def gepDecodeStep {α : Type} [Inhabited α] (dynamic : Array α)
    (b : Nat × Array (GEPIndex α)) (raw : Int) : Nat × Array (GEPIndex α) :=
  if raw = -2147483648 then (b.1+1, b.2.push (.dynamic dynamic[b.1]!))
  else (b.1, b.2.push (.const raw))

theorem gep_decode_all_zero {α : Type} [Inhabited α] (raw : Array Int) (dynamic : Array α)
    (hz : ∀ i ∈ raw, i = 0) : ∀ index ∈ GEPIndex.decode raw dynamic, index = .const 0 := by
  have h := Array.foldl_induction (as := raw)
    (motive := fun _ (b : Nat × Array (GEPIndex α)) => ∀ index ∈ b.2, index = .const 0)
    (init := (0, #[])) (h0 := by simp)
    (f := gepDecodeStep dynamic)
    (hf := by
      intro i b hb
      have hi : raw[i] = 0 := hz _ (Array.getElem_mem i.isLt)
      simp only [gepDecodeStep, hi, show (0 : Int) ≠ -2147483648 by decide, ↓reduceIte]
      intro index hm
      rcases Array.mem_push.mp hm with hm | hm
      · exact hb index hm
      · exact hm)
  unfold GEPIndex.decode
  simp only [bind, pure, Id.run]
  simp only [← apply_ite]
  change ∀ index ∈ ((forIn raw (0, #[]) (fun a b => pure (ForInStep.yield (gepDecodeStep dynamic b a))) :
    Id (Nat × Array (GEPIndex α))).run).2, index = .const 0
  rw [Array.forIn_pure_yield_eq_foldl]
  exact h

abbrev GEPLayoutState (α : Type) := Int × Array (α × Nat) × Attribute

def gepLayoutStep {α : Type} (layout : DataLayout) (index : GEPIndex α)
    (s : GEPLayoutState α) : Option (ForInStep (GEPLayoutState α)) :=
  match s.2.2, index with
  | .llvmArrayType {type, ..}, index => do
    let stride ← layout.getTypeAllocSize type
    match index with
    | .const c => pure (.yield (s.1 + c * stride, s.2.1, type))
    | .dynamic v => pure (.yield (s.1, s.2.1.push (v,stride), type))
  | .llvmStructType {packed, body, ..}, .const c => do
    let (offsets, _) := structLayout (← body.mapM layout.query) packed
    pure (.yield (s.1 + offsets[c.toNat]!, s.2.1, body[c.toNat]!))
  | _, _ => none

theorem gepLayoutStep_zero {α : Type} (layout : DataLayout) (outer : Attribute) :
    gepLayoutStep layout (.const 0) (0, (#[] : Array (α × Nat)), outer) = none ∨
    ∃ next, gepLayoutStep layout (.const 0) (0, (#[] : Array (α × Nat)), outer) =
      some (.yield (0, #[], next)) := by
  cases outer <;> simp [gepLayoutStep, -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]
  case llvmArrayType t =>
    rcases t with ⟨n,ty⟩
    cases h : layout.getTypeAllocSize ty <;>
      simp [h, -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]
  case llvmStructType t =>
    rcases t with ⟨name,packed,body⟩
    cases h : body.mapM layout.query <;>
      simp [h, gep_struct_first_offset, -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]

theorem gep_zero_loop_list {α : Type} (layout : DataLayout) (indices : List (GEPIndex α))
    (hz : ∀ index ∈ indices, index = .const 0) (outer : Attribute) :
    forIn indices (0, (#[] : Array (α × Nat)), outer) (gepLayoutStep layout) = none ∨
    ∃ next, forIn indices (0, (#[] : Array (α × Nat)), outer) (gepLayoutStep layout) =
      some (0, #[], next) := by
  induction indices generalizing outer with
  | nil => exact Or.inr ⟨outer,rfl⟩
  | cons index indices ih =>
    obtain rfl := hz index (by simp)
    have ht : ∀ index ∈ indices, index = .const 0 := by
      intro index hi
      exact hz index (by simp [hi])
    rcases gepLayoutStep_zero layout outer with hn | ⟨next,hs⟩
    · left
      rw [List.forIn_cons, hn]
      rfl
    · rcases ih ht next with hn | ⟨last,hl⟩
      · left
        rw [List.forIn_cons, hs]
        exact hn
      · right
        exact ⟨last, by rw [List.forIn_cons, hs]; exact hl⟩

theorem gep_zero_loop {α : Type} (layout : DataLayout) (indices : Array (GEPIndex α))
    (hz : ∀ index ∈ indices, index = .const 0) (outer : Attribute) :
    forIn indices (0, (#[] : Array (α × Nat)), outer) (gepLayoutStep layout) = none ∨
    ∃ next, forIn indices (0, (#[] : Array (α × Nat)), outer) (gepLayoutStep layout) =
      some (0, #[], next) := by
  cases indices with
  | mk indices =>
    simpa only [List.forIn_toArray] using
      gep_zero_loop_list layout indices (by simpa using hz) outer

theorem gep_offsets_zero {α : Type} (layout : DataLayout) (elem : Attribute)
    (indices : Array (GEPIndex α)) (hz : ∀ index ∈ indices, index = .const 0) :
    layout.gepOffsets elem indices = none ∨ layout.gepOffsets elem indices = some (0, #[]) := by
  rcases gep_zero_loop layout indices hz (.llvmArrayType {size := 0, type := elem}) with hn | ⟨next,hs⟩
  · left
    unfold DataLayout.gepOffsets
    change (do let st ← forIn indices (0, #[], .llvmArrayType {size := 0, type := elem}) (gepLayoutStep layout)
               pure (st.1, st.2.1)) = none
    rw [hn]
    rfl
  · right
    unfold DataLayout.gepOffsets
    change (do let st ← forIn indices (0, #[], .llvmArrayType {size := 0, type := elem}) (gepLayoutStep layout)
               pure (st.1, st.2.1)) = some (0, #[])
    rw [hs]
    rfl

theorem gep_all_zero_static_refines (props : propertiesOf (.llvm .getelementptr : OpCode))
    (hz : ∀ index ∈ props.rawConstantIndices.values, index = 0)
    (p : LLVM.Ptr) (v : RuntimeValue)
    (hi : InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)] #[.addr p] #[v]) :
    v ⊒ .addr p := by
  have hd := gep_decode_all_zero props.rawConstantIndices.values (#[] : Array RuntimeValue) hz
  have he := hi.2 .empty
  rcases gep_offsets_zero DataLayout.riscv64 props.elem_type.val _ hd with hn | hn
  · simp [interpretOp', Llvm.interpretOp', hn] at he
  · cases p with
    | poison =>
      simp [interpretOp', Llvm.interpretOp', hn] at he
      subst v
      simp [RuntimeValue.isRefinedBy, isRefinedBy]
    | val p =>
      have hu : UInt64.ofInt (p.address.toNat : Int) = p.address := by
        have hlt : (p.address.toNat : Int) < 18446744073709551616 := by
          have := UInt64.toNat_lt p.address
          omega
        simp [UInt64.ofInt, Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt]
      simp [interpretOp', Llvm.interpretOp', hn, hu] at he
      subst v
      simp [RuntimeValue.isRefinedBy, isRefinedBy]

def GEPValueZero (v : RuntimeValue) : Prop := ∃ w, v = .int w (.val 0#w)

def GEPIndexZero : GEPIndex RuntimeValue → Prop
  | .const i => i = 0
  | .dynamic v => GEPValueZero v

theorem gep_decode_eq_foldl {α : Type} [Inhabited α] (raw : Array Int) (dynamic : Array α) :
    GEPIndex.decode raw dynamic = (raw.foldl (gepDecodeStep dynamic) (0,#[])).2 := by
  unfold GEPIndex.decode
  simp only [bind, pure, Id.run, ← apply_ite]
  change ((forIn raw (0, #[]) (fun a b => pure (ForInStep.yield (gepDecodeStep dynamic b a))) :
    Id (Nat × Array (GEPIndex α))).run).2 = _
  rw [Array.forIn_pure_yield_eq_foldl]
  rfl

theorem gep_decode_zero_fold (raw : List Int) (dynamic : Array RuntimeValue)
    (b : Nat × Array (GEPIndex RuntimeValue))
    (hz : ∀ i ∈ raw, i = 0 ∨ i = -2147483648)
    (hd : ∀ v ∈ dynamic, GEPValueZero v)
    (hb : ∀ i ∈ b.2, GEPIndexZero i)
    (hcount : b.1 + (raw.filter (· == -2147483648)).length ≤ dynamic.size) :
    ∀ i ∈ (raw.foldl (gepDecodeStep dynamic) b).2, GEPIndexZero i := by
  induction raw generalizing b with
  | nil => exact hb
  | cons index raw ih =>
    have ht : ∀ i ∈ raw, i = 0 ∨ i = -2147483648 := by
      intro i hi
      exact hz i (by simp [hi])
    rcases hz index (by simp) with rfl | rfl
    · apply ih _ ht
      · simp only [gepDecodeStep, show (0 : Int) ≠ -2147483648 by decide, ↓reduceIte]
        intro i hi
        rcases Array.mem_push.mp hi with hi | hi
        · exact hb i hi
        · subst i
          rfl
      · simpa [gepDecodeStep] using hcount
    · have hn : b.1 < dynamic.size := by
        simp only [List.filter_cons, beq_self_eq_true, ↓reduceIte, List.length_cons] at hcount
        omega
      have hv : GEPValueZero dynamic[b.1]! := by
        rw [getElem!_pos dynamic b.1 hn]
        exact hd _ (Array.getElem_mem hn)
      apply ih _ ht
      · simp only [gepDecodeStep, ↓reduceIte]
        intro i hi
        rcases Array.mem_push.mp hi with hi | hi
        · exact hb i hi
        · subst i
          exact hv
      · simpa [gepDecodeStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount

theorem gep_decode_zero_indices (raw : Array Int) (dynamic : Array RuntimeValue)
    (hz : ∀ i ∈ raw, i = 0 ∨ i = -2147483648)
    (hd : ∀ v ∈ dynamic, GEPValueZero v)
    (hcount : (raw.filter (· == -2147483648)).size = dynamic.size) :
    ∀ i ∈ GEPIndex.decode raw dynamic, GEPIndexZero i := by
  rw [gep_decode_eq_foldl, ← Array.foldl_toList]
  apply gep_decode_zero_fold raw.toList dynamic (0,#[])
  · simpa using hz
  · exact hd
  · simp
  · have hc : (raw.filter (· == -2147483648)).toList.length ≤ dynamic.size := Nat.le_of_eq hcount
    rw [Array.toList_filter] at hc
    simpa using hc

def GEPLayoutZero (s : GEPLayoutState RuntimeValue) : Prop :=
  s.1 = 0 ∧ ∀ pair ∈ s.2.1, GEPValueZero pair.1

theorem gepLayoutStep_zeroish (layout : DataLayout) (index : GEPIndex RuntimeValue)
    (hi : GEPIndexZero index) (s : GEPLayoutState RuntimeValue) (hs : GEPLayoutZero s) :
    gepLayoutStep layout index s = none ∨ ∃ next,
      gepLayoutStep layout index s = some (.yield next) ∧ GEPLayoutZero next := by
  rcases s with ⟨offset,dynamic,outer⟩
  rcases hs with ⟨rfl,hd⟩
  cases index with
  | const c =>
    have hc : c = 0 := hi
    subst c
    cases outer <;> simp [gepLayoutStep, -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]
    case llvmArrayType t =>
      rcases t with ⟨n,ty⟩
      cases h : layout.getTypeAllocSize ty <;>
        simp [h, GEPLayoutZero, -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]
      refine ⟨0,dynamic,⟨rfl,rfl⟩,rfl,?_⟩
      intro a b hm
      exact hd (a,b) hm
    case llvmStructType t =>
      rcases t with ⟨name,packed,body⟩
      cases h : body.mapM layout.query <;>
        simp [h, gep_struct_first_offset, GEPLayoutZero,
          -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]
      refine ⟨0,dynamic,⟨rfl,rfl⟩,rfl,?_⟩
      intro a b hm
      exact hd (a,b) hm
  | dynamic v =>
    cases outer <;> simp [gepLayoutStep, -Attribute.llvmArrayType_eq_of, -Attribute.llvmStructType_eq_of]
    case llvmArrayType t =>
      rcases t with ⟨n,ty⟩
      cases h : layout.getTypeAllocSize ty with
      | none => simp [h]
      | some stride =>
        simp [h, GEPLayoutZero]
        refine ⟨0,dynamic.push (v,stride),⟨rfl,rfl⟩,rfl,?_⟩
        intro a b hm
        rcases Array.mem_push.mp hm with hm | hm
        · exact hd (a,b) hm
        · cases hm
          exact hi

theorem gep_zeroish_loop_list (layout : DataLayout) (indices : List (GEPIndex RuntimeValue))
    (hz : ∀ index ∈ indices, GEPIndexZero index)
    (s : GEPLayoutState RuntimeValue) (hs : GEPLayoutZero s) :
    forIn indices s (gepLayoutStep layout) = none ∨
    ∃ next, forIn indices s (gepLayoutStep layout) = some next ∧ GEPLayoutZero next := by
  induction indices generalizing s with
  | nil => exact Or.inr ⟨s,rfl,hs⟩
  | cons index indices ih =>
    have ht : ∀ index ∈ indices, GEPIndexZero index := by
      intro index hi
      exact hz index (by simp [hi])
    rcases gepLayoutStep_zeroish layout index (hz index (by simp)) s hs with hn | ⟨next,hn,hnext⟩
    · left
      rw [List.forIn_cons, hn]
      rfl
    · rcases ih ht next hnext with hl | ⟨last,hl,hlast⟩
      · left
        rw [List.forIn_cons, hn]
        exact hl
      · right
        refine ⟨last,?_,hlast⟩
        rw [List.forIn_cons, hn]
        exact hl

theorem gep_zeroish_offsets (layout : DataLayout) (elem : Attribute)
    (indices : Array (GEPIndex RuntimeValue)) (hz : ∀ index ∈ indices, GEPIndexZero index) :
    layout.gepOffsets elem indices = none ∨ ∃ dynamic,
      layout.gepOffsets elem indices = some (0,dynamic) ∧ ∀ pair ∈ dynamic, GEPValueZero pair.1 := by
  have hloop : forIn indices (0,#[],.llvmArrayType {size := 0, type := elem}) (gepLayoutStep layout) = none ∨
      ∃ next, forIn indices (0,#[],.llvmArrayType {size := 0, type := elem}) (gepLayoutStep layout) = some next ∧ GEPLayoutZero next := by
    cases indices with
    | mk indices =>
      simpa only [List.forIn_toArray] using
        gep_zeroish_loop_list layout indices (by simpa using hz) (0,#[],.llvmArrayType {size := 0, type := elem}) (by simp [GEPLayoutZero])
  rcases hloop with hn | ⟨next,hn,hgood⟩
  · left
    unfold DataLayout.gepOffsets
    change (do let st ← forIn indices (0, #[], .llvmArrayType {size := 0, type := elem}) (gepLayoutStep layout)
               pure (st.1, st.2.1)) = none
    rw [hn]
    rfl
  · right
    refine ⟨next.2.1,?_,hgood.2⟩
    unfold DataLayout.gepOffsets
    change (do let st ← forIn indices (0, #[], .llvmArrayType {size := 0, type := elem}) (gepLayoutStep layout)
               pure (st.1, st.2.1)) = some (0,next.2.1)
    rw [hn]
    simp [hgood.1]

abbrev GEPAddressState := Option (Array RuntimeValue × MemoryState × Option ControlFlowAction) × Int

def gepAddressStep (mem : MemoryState) (pair : RuntimeValue × Nat) (s : GEPAddressState) :
    Interp (ForInStep GEPAddressState) :=
  match pair.1 with
  | .int _ index =>
    match index with
    | .val index => .ok (.yield (none,s.2 + index.toInt * pair.2))
    | _ => .ok (.done (some (#[.addr .poison],mem,none),s.2))
  | _ => .fail none

theorem gep_address_zero_loop_list (mem : MemoryState) (dynamic : List (RuntimeValue × Nat))
    (hz : ∀ pair ∈ dynamic, GEPValueZero pair.1) (address : Int) :
    forIn dynamic (none,address) (gepAddressStep mem) = .ok (none,address) := by
  induction dynamic generalizing address with
  | nil => rfl
  | cons pair dynamic ih =>
    have ht : ∀ pair ∈ dynamic, GEPValueZero pair.1 := by
      intro pair hi
      exact hz pair (by simp [hi])
    rcases pair with ⟨value,stride⟩
    obtain ⟨w,hv⟩ := hz (value,stride) (by simp)
    dsimp at hv
    subst value
    simpa [List.forIn_cons, gepAddressStep] using ih ht address

theorem gep_address_zero_loop (mem : MemoryState) (dynamic : Array (RuntimeValue × Nat))
    (hz : ∀ pair ∈ dynamic, GEPValueZero pair.1) (address : Int) :
    forIn dynamic (none,address) (gepAddressStep mem) = .ok (none,address) := by
  cases dynamic with
  | mk dynamic =>
    simpa only [List.forIn_toArray] using
      gep_address_zero_loop_list mem dynamic (by simpa using hz) address

end Veir.InstSimplify
