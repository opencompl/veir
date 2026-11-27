module

/-!
# Functional model of tensors

Shape plus index→element function. Flat arrays connect via `ofArray` / `toArray`.
-/

public section

namespace Veir.Data.Tensor

@[expose]
def numElements : List Nat → Nat
  | [] => 1
  | dim :: dims => dim * numElements dims

private theorem foldl_mul_eq_mul_foldl (a : Nat) (l : List Nat) :
    l.foldl Nat.mul a = a * l.foldl Nat.mul 1 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    change List.foldl Nat.mul (Nat.mul a x) xs =
      Nat.mul a (List.foldl Nat.mul (Nat.mul 1 x) xs)
    have hax : List.foldl Nat.mul (Nat.mul a x) xs =
        Nat.mul (Nat.mul a x) (List.foldl Nat.mul 1 xs) := ih (Nat.mul a x)
    have hx : List.foldl Nat.mul x xs =
        Nat.mul x (List.foldl Nat.mul 1 xs) := ih x
    rw [hax, show Nat.mul 1 x = x from Nat.one_mul x, hx]
    exact Nat.mul_assoc a x (List.foldl Nat.mul 1 xs)

theorem numElements_eq_foldl (shape : List Nat) :
    numElements shape = shape.foldl Nat.mul 1 := by
  induction shape with
  | nil => rfl
  | cons d ds ih =>
    change Nat.mul d (numElements ds) = List.foldl Nat.mul (Nat.mul 1 d) ds
    rw [ih, show Nat.mul 1 d = d from Nat.one_mul d]
    exact (foldl_mul_eq_mul_foldl d ds).symm

theorem numElements_toList (shape : Array Nat) :
    numElements shape.toList = shape.foldl Nat.mul 1 := by
  rw [numElements_eq_foldl, Array.foldl_toList]

@[expose]
def InBounds : List Nat → List Nat → Prop
  | [], [] => True
  | dim :: dims, i :: idx => i < dim ∧ InBounds dims idx
  | _, _ => False

@[simp] theorem inBounds_nil : InBounds [] [] := by simp [InBounds]

@[simp] theorem inBounds_cons {dim i : Nat} {dims idx : List Nat} :
    InBounds (dim :: dims) (i :: idx) ↔ i < dim ∧ InBounds dims idx := by
  simp [InBounds]

@[simp] theorem not_inBounds_nil_cons {i : Nat} {idx : List Nat} :
    ¬ InBounds [] (i :: idx) := by simp [InBounds]

@[simp] theorem not_inBounds_cons_nil {dim : Nat} {dims : List Nat} :
    ¬ InBounds (dim :: dims) [] := by simp [InBounds]

instance instDecidableInBounds : (shape idx : List Nat) → Decidable (InBounds shape idx)
  | [], [] => isTrue inBounds_nil
  | [], _ :: _ => isFalse not_inBounds_nil_cons
  | _ :: _, [] => isFalse not_inBounds_cons_nil
  | dim :: dims, i :: idx =>
    have := instDecidableInBounds dims idx
    decidable_of_iff (i < dim ∧ InBounds dims idx) inBounds_cons.symm

/-- Row-major flat index. -/
@[expose]
def linearize : List Nat → List Nat → Nat
  | _ :: dims, i :: idx => i * numElements dims + linearize dims idx
  | _, _ => 0

/-- Inverse of `linearize`. -/
@[expose]
def delinearize : List Nat → Nat → List Nat
  | [], _ => []
  | _ :: dims, pos => pos / numElements dims :: delinearize dims (pos % numElements dims)

theorem linearize_lt {shape idx : List Nat} (h : InBounds shape idx) :
    linearize shape idx < numElements shape := by
  induction shape generalizing idx with
  | nil => cases idx <;> simp_all [linearize, numElements]
  | cons dim dims ih =>
    cases idx with
    | nil => simp at h
    | cons i idx =>
      obtain ⟨hi, hidx⟩ := inBounds_cons.mp h
      have hlt := ih hidx
      simp only [linearize, numElements]
      calc i * numElements dims + linearize dims idx
          < i * numElements dims + numElements dims := by omega
        _ = (i + 1) * numElements dims := (Nat.succ_mul _ _).symm
        _ ≤ dim * numElements dims := Nat.mul_le_mul_right _ hi

@[simp]
theorem delinearize_linearize {shape idx : List Nat} (h : InBounds shape idx) :
    delinearize shape (linearize shape idx) = idx := by
  induction shape generalizing idx with
  | nil => cases idx <;> simp_all [delinearize]
  | cons dim dims ih =>
    cases idx with
    | nil => simp at h
    | cons i idx =>
      obtain ⟨-, hidx⟩ := inBounds_cons.mp h
      have hlt := linearize_lt hidx
      have hpos : 0 < numElements dims := by omega
      simp only [linearize]
      rw [delinearize, Nat.mul_comm i, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, Nat.add_zero,
        Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, ih hidx]

@[simp]
theorem linearize_delinearize {shape : List Nat} {pos : Nat} (h : pos < numElements shape) :
    linearize shape (delinearize shape pos) = pos := by
  induction shape generalizing pos with
  | nil =>
    simp only [numElements] at h
    simp only [linearize]
    omega
  | cons dim dims ih =>
    simp only [numElements] at h
    have hpos : 0 < numElements dims := by
      apply Nat.pos_of_ne_zero
      intro hzero
      simp [hzero] at h
    simp only [delinearize, linearize]
    rw [ih (Nat.mod_lt _ hpos)]
    exact Nat.div_add_mod' pos (numElements dims)

theorem inBounds_delinearize {shape : List Nat} {pos : Nat}
    (h : pos < numElements shape) : InBounds shape (delinearize shape pos) := by
  induction shape generalizing pos with
  | nil =>
    simp only [numElements] at h
    simp [delinearize]
  | cons dim dims ih =>
    simp only [numElements] at h
    have hpos : 0 < numElements dims := by
      apply Nat.pos_of_ne_zero
      intro hzero
      simp [hzero] at h
    simp only [delinearize, InBounds]
    exact ⟨Nat.div_lt_of_lt_mul (Nat.mul_comm dim _ ▸ h), ih (Nat.mod_lt pos hpos)⟩

/--
  Index in the source tensor for a slice at relative index `idx`, with
  per-dimension offsets and strides: `source[i] = offset[i] + idx[i] * stride[i]`.
-/
@[expose]
def sliceIndex : List Nat → List Nat → List Nat → List Nat
  | o :: os, st :: sts, i :: idx => (o + i * st) :: sliceIndex os sts idx
  | _, _, _ => []

/-- Compose nested slice offsets: `o1 + o2 * st1` (pointwise). -/
@[expose]
def composeSliceOffsets (o1 st1 o2 : List Nat) : List Nat :=
  match o1, st1, o2 with
  | o :: os, st :: sts, o' :: os' => (o + o' * st) :: composeSliceOffsets os sts os'
  | _, _, _ => []

/-- Compose nested slice strides: `st1 * st2` (pointwise). -/
@[expose]
def composeSliceStrides (st1 st2 : List Nat) : List Nat :=
  match st1, st2 with
  | st :: sts, st' :: sts' => (st * st') :: composeSliceStrides sts sts'
  | _, _ => []

theorem sliceIndex_compose (o1 st1 o2 st2 idx : List Nat) :
    sliceIndex o1 st1 (sliceIndex o2 st2 idx) =
      sliceIndex (composeSliceOffsets o1 st1 o2) (composeSliceStrides st1 st2) idx := by
  induction o1 generalizing st1 o2 st2 idx with
  | nil => cases st1 <;> cases o2 <;> cases st2 <;> cases idx <;> simp [sliceIndex, composeSliceOffsets, composeSliceStrides]
  | cons o os ih =>
    cases st1 with
    | nil => cases o2 <;> cases st2 <;> cases idx <;> simp [sliceIndex, composeSliceOffsets, composeSliceStrides]
    | cons st sts =>
      cases o2 with
      | nil => cases st2 <;> cases idx <;> simp [sliceIndex, composeSliceOffsets, composeSliceStrides]
      | cons o' os' =>
        cases st2 with
        | nil => cases idx <;> simp [sliceIndex, composeSliceOffsets, composeSliceStrides]
        | cons st' sts' =>
          cases idx with
          | nil => simp [sliceIndex, composeSliceOffsets, composeSliceStrides]
          | cons i is =>
            simp only [sliceIndex, composeSliceOffsets, composeSliceStrides]
            congr 1
            · simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm st' st]
            · exact ih sts os' sts' is

/--
  Ranks agree, each offset is in-bounds, and if `size ≠ 0` then
  `offset + (size - 1) * stride < dim`.
-/
@[expose]
def fitsSlice : List Nat → List Nat → List Nat → List Nat → Bool
  | [], [], [], [] => true
  | dim :: dims, o :: os, s :: ss, st :: sts =>
    decide (o < dim) && (decide (s = 0) || decide (o + (s - 1) * st < dim)) &&
      fitsSlice dims os ss sts
  | _, _, _, _ => false

/-- Error for the first out-of-bounds dimension, if any. -/
def sliceBoundsError? (shape offsets sizes strides : List Nat) (dimIdx : Nat := 0) :
    Option String :=
  match shape, offsets, sizes, strides with
  | [], [], [], [] => none
  | dim :: dims, o :: os, s :: ss, st :: sts =>
    if o ≥ dim then
      some s!"offset {dimIdx} is out-of-bounds: {o} >= {dim}"
    else if s ≠ 0 && o + (s - 1) * st ≥ dim then
      let lastPos := o + (s - 1) * st
      some s!"slice along dimension {dimIdx} runs out-of-bounds: {lastPos} >= {dim}"
    else
      sliceBoundsError? dims os ss sts (dimIdx + 1)
  | _, _, _, _ => none

/-- Reject negatives; otherwise `Int` → `Nat`. -/
@[expose]
def staticIndices? : List Int → Option (List Nat)
  | [] => some []
  | v :: vs => if 0 ≤ v then (staticIndices? vs).map (v.toNat :: ·) else none

/-- Attribute-level `composeSliceOffsets`. -/
@[expose]
def composeSliceOffsetInts : List Int → List Int → List Int → List Int
  | o :: os, st :: sts, o' :: os' => (o + o' * st) :: composeSliceOffsetInts os sts os'
  | _, _, _ => []

/-- Attribute-level `composeSliceStrides`. -/
@[expose]
def composeSliceStrideInts : List Int → List Int → List Int
  | st :: sts, st' :: sts' => (st * st') :: composeSliceStrideInts sts sts'
  | _, _ => []

theorem fitsSlice_lengths {shape offsets sizes strides : List Nat}
    (h : fitsSlice shape offsets sizes strides = true) :
    offsets.length = shape.length ∧ sizes.length = shape.length ∧
      strides.length = shape.length := by
  induction shape generalizing offsets sizes strides with
  | nil => cases offsets <;> cases sizes <;> cases strides <;> simp_all [fitsSlice]
  | cons d ds ih =>
    cases offsets with
    | nil => simp [fitsSlice] at h
    | cons o os =>
      cases sizes with
      | nil => simp [fitsSlice] at h
      | cons s ss =>
        cases strides with
        | nil => simp [fitsSlice] at h
        | cons st sts =>
          simp only [fitsSlice, Bool.and_eq_true] at h
          have := ih h.2
          simp [this.1, this.2.1, this.2.2]

theorem inBounds_sliceIndex {shape offsets sizes strides idx : List Nat}
    (hfit : fitsSlice shape offsets sizes strides = true)
    (hidx : InBounds sizes idx) :
    InBounds shape (sliceIndex offsets strides idx) := by
  induction shape generalizing offsets sizes strides idx with
  | nil =>
    cases offsets <;> cases sizes <;> cases strides <;> cases idx
      <;> simp_all [fitsSlice, sliceIndex, InBounds]
  | cons dim dims ih =>
    cases offsets with
    | nil => simp [fitsSlice] at hfit
    | cons o os =>
      cases sizes with
      | nil => simp [fitsSlice] at hfit
      | cons s ss =>
        cases strides with
        | nil => simp [fitsSlice] at hfit
        | cons st sts =>
          cases idx with
          | nil => simp [InBounds] at hidx
          | cons i is =>
            simp only [fitsSlice, Bool.and_eq_true, Bool.or_eq_true,
              decide_eq_true_eq] at hfit
            obtain ⟨⟨ho, hs⟩, hfit'⟩ := hfit
            obtain ⟨hi, hidx'⟩ := inBounds_cons.mp hidx
            simp only [sliceIndex, InBounds]
            refine ⟨?_, ih hfit' hidx'⟩
            rcases hs with h0 | hlt
            · subst h0
              cases hi
            · have : i ≤ s - 1 := Nat.le_pred_of_lt hi
              have : o + i * st ≤ o + (s - 1) * st :=
                Nat.add_le_add_left (Nat.mul_le_mul_right st this) _
              omega

theorem fitsSlice_compose {shape o1 s1 st1 o2 s2 st2 : List Nat}
    (hinner : fitsSlice shape o1 s1 st1 = true)
    (houter : fitsSlice s1 o2 s2 st2 = true) :
    fitsSlice shape (composeSliceOffsets o1 st1 o2) s2 (composeSliceStrides st1 st2) = true := by
  induction shape generalizing o1 s1 st1 o2 s2 st2 with
  | nil =>
    cases o1 <;> cases s1 <;> cases st1 <;> cases o2 <;> cases s2 <;> cases st2
      <;> simp_all [fitsSlice, composeSliceOffsets, composeSliceStrides]
  | cons dim dims ih =>
    cases o1 with
    | nil => simp [fitsSlice] at hinner
    | cons o os =>
      cases s1 with
      | nil => simp [fitsSlice] at hinner
      | cons s ss =>
        cases st1 with
        | nil => simp [fitsSlice] at hinner
        | cons st sts =>
          cases o2 with
          | nil => simp [fitsSlice] at houter
          | cons o' os' =>
            cases s2 with
            | nil => simp [fitsSlice] at houter
            | cons s' ss' =>
              cases st2 with
              | nil => simp [fitsSlice] at houter
              | cons st' sts' =>
                simp only [fitsSlice, Bool.and_eq_true, Bool.or_eq_true,
                  decide_eq_true_eq] at hinner houter
                obtain ⟨⟨ho, hs⟩, hinner'⟩ := hinner
                obtain ⟨⟨ho', hs'⟩, houter'⟩ := houter
                have hrec := ih hinner' houter'
                simp only [composeSliceOffsets, composeSliceStrides, fitsSlice,
                  Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
                refine ⟨⟨?hoff, ?hsize⟩, hrec⟩
                · -- composed offset < dim
                  rcases hs with h0 | hlt
                  · subst h0
                    cases ho'
                  · have : o' ≤ s - 1 := Nat.le_pred_of_lt ho'
                    have : o + o' * st ≤ o + (s - 1) * st :=
                      Nat.add_le_add_left (Nat.mul_le_mul_right st this) _
                    omega
                · -- size conjunct for the composed window
                  rcases hs' with h0 | hlt'
                  · exact Or.inl h0
                  · right
                    have hmid : o' + (s' - 1) * st' < s := hlt'
                    have hle : o + (o' + (s' - 1) * st') * st ≤ o + (s - 1) * st := by
                      have : o' + (s' - 1) * st' ≤ s - 1 := Nat.le_pred_of_lt hmid
                      exact Nat.add_le_add_left (Nat.mul_le_mul_right st this) _
                    have hinnerBound : o + (s - 1) * st < dim := by
                      rcases hs with h0 | hlt
                      · subst h0
                        cases (Nat.not_lt_zero _ hmid)
                      · exact hlt
                    have hrew :
                        o + o' * st + (s' - 1) * (st * st') =
                          o + (o' + (s' - 1) * st') * st := by
                      simp [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm st' st]
                    omega

theorem length_staticIndices? {values : List Int} {result : List Nat}
    (h : staticIndices? values = some result) :
    result.length = values.length := by
  induction values generalizing result with
  | nil =>
    simp [staticIndices?] at h
    subst h
    rfl
  | cons v vs ih =>
    simp only [staticIndices?] at h
    split at h
    · rename_i hnonneg
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      simp [ih hrest]
    · cases h

theorem staticIndices?_compose_offsets
    {o1Ints st1Ints o2Ints : List Int} {o1 st1 o2 : List Nat}
    (h1 : staticIndices? o1Ints = some o1)
    (hst : staticIndices? st1Ints = some st1)
    (h2 : staticIndices? o2Ints = some o2)
    (hlen1 : o1Ints.length = st1Ints.length)
    (hlen2 : o1Ints.length = o2Ints.length) :
    staticIndices? (composeSliceOffsetInts o1Ints st1Ints o2Ints) =
      some (composeSliceOffsets o1 st1 o2) := by
  induction o1Ints generalizing st1Ints o2Ints o1 st1 o2 with
  | nil =>
    cases st1Ints <;> cases o2Ints <;> cases o1 <;> cases st1 <;> cases o2
      <;> simp_all [staticIndices?, composeSliceOffsetInts, composeSliceOffsets]
  | cons o os ih =>
    cases st1Ints with
    | nil => simp at hlen1
    | cons st sts =>
      cases o2Ints with
      | nil => simp at hlen2
      | cons o' os' =>
        simp only [staticIndices?] at h1 hst h2
        split at h1 <;> try cases h1
        split at hst <;> try cases hst
        split at h2 <;> try cases h2
        rename_i ho hst0 ho'
        simp only [Option.map_eq_some_iff] at h1 hst h2
        obtain ⟨o1', h1', rfl⟩ := h1
        obtain ⟨st1', hst', rfl⟩ := hst
        obtain ⟨o2', h2', rfl⟩ := h2
        have hrec := ih h1' hst' h2' (by simpa using hlen1) (by simpa using hlen2)
        have hsum : 0 ≤ o + o' * st :=
          Int.add_nonneg ho (Int.mul_nonneg ho' hst0)
        simp only [composeSliceOffsetInts, composeSliceOffsets, staticIndices?, hsum]
        rw [hrec]
        simp [Int.toNat_add ho (Int.mul_nonneg ho' hst0), Int.toNat_mul ho' hst0]

theorem staticIndices?_compose_strides
    {st1Ints st2Ints : List Int} {st1 st2 : List Nat}
    (h1 : staticIndices? st1Ints = some st1)
    (h2 : staticIndices? st2Ints = some st2)
    (hlen : st1Ints.length = st2Ints.length) :
    staticIndices? (composeSliceStrideInts st1Ints st2Ints) =
      some (composeSliceStrides st1 st2) := by
  induction st1Ints generalizing st2Ints st1 st2 with
  | nil =>
    cases st2Ints <;> cases st1 <;> cases st2
      <;> simp_all [staticIndices?, composeSliceStrideInts, composeSliceStrides]
  | cons st sts ih =>
    cases st2Ints with
    | nil => simp at hlen
    | cons st' sts' =>
      simp only [staticIndices?] at h1 h2
      split at h1 <;> try cases h1
      split at h2 <;> try cases h2
      rename_i hst0 hst0'
      simp only [Option.map_eq_some_iff] at h1 h2
      obtain ⟨st1', h1', rfl⟩ := h1
      obtain ⟨st2', h2', rfl⟩ := h2
      have hrec := ih h1' h2' (by simpa using hlen)
      have hprod : 0 ≤ st * st' := Int.mul_nonneg hst0 hst0'
      simp only [composeSliceStrideInts, composeSliceStrides, staticIndices?, hprod]
      rw [hrec]
      simp [Int.toNat_mul hst0 hst0']

structure TensorFunctionalModel (α : Type u) where
  shape : List Nat
  get : List Nat → α

namespace TensorFunctionalModel

variable {α : Type u}

@[expose]
def extract (t : TensorFunctionalModel α) (idx : List Nat) : α := t.get idx

@[expose]
def ofArray (shape : List Nat) (elems : Array α) (default : α) :
    TensorFunctionalModel α :=
  ⟨shape, fun idx => elems.getD (linearize shape idx) default⟩

@[expose]
def toArray (t : TensorFunctionalModel α) : Array α :=
  Array.ofFn (n := numElements t.shape) fun pos => t.get (delinearize t.shape pos)

@[simp] theorem ofArray_shape (shape : List Nat) (elems : Array α) (default : α) :
    (ofArray shape elems default).shape = shape := rfl

@[simp] theorem extract_ofArray (shape : List Nat) (elems : Array α) (default : α)
    (idx : List Nat) :
    (ofArray shape elems default).extract idx =
      elems.getD (linearize shape idx) default := rfl

@[simp] theorem size_toArray (t : TensorFunctionalModel α) :
    t.toArray.size = numElements t.shape := by
  simp [toArray]

theorem extract_ofArray_toArray (t : TensorFunctionalModel α) (default : α)
    (idx : List Nat) (hidx : InBounds t.shape idx) :
    (ofArray t.shape t.toArray default).extract idx = t.extract idx := by
  have hlin : linearize t.shape idx < numElements t.shape := linearize_lt hidx
  have hlinArr : linearize t.shape idx < t.toArray.size := by
    simpa [size_toArray] using hlin
  have hget : t.toArray[linearize t.shape idx]'hlinArr = t.get idx := by
    simp [toArray, delinearize_linearize hidx]
  simp [extract, ofArray, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hlinArr, hget]

theorem toArray_ofArray (shape : List Nat) (elems : Array α) (default : α)
    (hsize : elems.size = numElements shape) :
    (ofArray shape elems default).toArray = elems := by
  refine Array.ext (by simp [hsize]) fun pos hpos hpos' => ?_
  have hposShape : pos < numElements shape := by simpa [size_toArray] using hpos
  have hposElems : pos < elems.size := by simpa [hsize] using hposShape
  simp only [toArray, Array.getElem_ofFn, ofArray, linearize_delinearize hposShape,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hposElems, Option.getD_some]

/-- Result shape is `sizes`; index `idx` reads `offset + idx * stride` in the source. -/
@[expose]
def slice (t : TensorFunctionalModel α) (offsets sizes strides : List Nat) :
    TensorFunctionalModel α :=
  ⟨sizes, fun idx => t.get (sliceIndex offsets strides idx)⟩

@[simp] theorem slice_shape (t : TensorFunctionalModel α)
    (offsets sizes strides : List Nat) :
    (t.slice offsets sizes strides).shape = sizes := rfl

@[simp] theorem extract_slice (t : TensorFunctionalModel α)
    (offsets sizes strides idx : List Nat) :
    (t.slice offsets sizes strides).extract idx =
      t.extract (sliceIndex offsets strides idx) := rfl

theorem toArray_slice_slice (t : TensorFunctionalModel α)
    (o1 s1 st1 o2 s2 st2 : List Nat) :
    ((t.slice o1 s1 st1).slice o2 s2 st2).toArray =
      (t.slice (composeSliceOffsets o1 st1 o2) s2 (composeSliceStrides st1 st2)).toArray := by
  refine Array.ext (by simp [slice_shape]) fun pos hpos hpos' => ?_
  simp only [toArray, Array.getElem_ofFn, slice, sliceIndex_compose]

/-- `ofArray ∘ toArray` does not change a fitted slice's flat contents. -/
theorem toArray_slice_ofArray_toArray (t : TensorFunctionalModel α) (default : α)
    (offsets sizes strides : List Nat)
    (hfit : fitsSlice t.shape offsets sizes strides = true) :
    ((ofArray t.shape t.toArray default).slice offsets sizes strides).toArray =
      (t.slice offsets sizes strides).toArray := by
  refine Array.ext (by simp [slice_shape]) fun pos hpos hpos' => ?_
  have hposShape : pos < numElements sizes := by
    simpa [size_toArray, slice_shape] using hpos
  have hidx := inBounds_delinearize hposShape
  have hsrc := inBounds_sliceIndex hfit hidx
  simp only [toArray, Array.getElem_ofFn, slice]
  change (ofArray t.shape t.toArray default).get
      (sliceIndex offsets strides (delinearize sizes pos)) =
    t.get (sliceIndex offsets strides (delinearize sizes pos))
  simpa [extract] using
    extract_ofArray_toArray t default (sliceIndex offsets strides (delinearize sizes pos)) hsrc

end TensorFunctionalModel

/-- Gather a slice from a flat row-major array (executable form of `ofArray` / `slice` / `toArray`). -/
@[expose]
def flatExtractSlice {α : Type u} (shape : List Nat) (elems : Array α) (default : α)
    (offsets sizes strides : List Nat) : Array α :=
  Array.ofFn (n := numElements sizes) fun pos =>
    elems.getD (linearize shape (sliceIndex offsets strides (delinearize sizes pos))) default

@[simp] theorem flatExtractSlice_eq_toArray_slice {α : Type u}
    (shape : List Nat) (elems : Array α) (default : α)
    (offsets sizes strides : List Nat) :
    flatExtractSlice shape elems default offsets sizes strides =
      ((TensorFunctionalModel.ofArray shape elems default).slice offsets sizes strides).toArray :=
  rfl

end Veir.Data.Tensor
