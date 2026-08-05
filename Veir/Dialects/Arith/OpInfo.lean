module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties
public import Veir.IR.Buffed.RawAccessors
public import Veir.Dialects.BuffedProperties

namespace Veir

public section

@[expose, properties_of]
def Arith.propertiesOf (op : Arith) : Type :=
match op with
-- TODO: Temporarily removed this as properties aren't supported in buffed yet, so we encode properties with attributes
| .subi => NswNuwProperties
| .divsi => ExactProperties
| .divui => ExactProperties
| .cmpi => IcmpProperties
| .shli => NswNuwProperties
| .shrsi => ExactProperties
| .shrui => ExactProperties
| .ori => DisjointProperties
| .trunci => NswNuwProperties
| .extui => NnegProperties
| .constant => ArithConstantProperties
| _ => Unit

@[expose]
def Arith.propertySize (op : Arith) : UInt64 :=
match op with
-- TODO: Temporarily removed this as properties aren't supported in buffed yet, so we encode properties with attributes
| .subi => 1
| .divsi => 1
| .divui => 1
| .cmpi => 1
| .shli => 1
| .shrsi => 1
| .shrui => 1
| .ori => 1
| .trunci => 1
| .extui => 1
| .constant => 8
| _ => 0

instance : HasDialectOpInfo Arith where
  propertiesOf := Arith.propertiesOf
  propertySize op := op.propertySize
  propertySize_small {op} := by cases op <;> simp [Arith.propertySize]

/-- A constant is stored inline in its 8-byte property slot when the value fits in 48 bits (two's complement) and the bitwidth in 15 bits. -/
abbrev ArithConstantProperties.IsInline (a : ArithConstantProperties) : Prop :=
  -(2^47) ≤ a.value.value ∧ a.value.value < 2^47 ∧ a.value.type.bitwidth < 2^15

/-- Store the constant's value in the 8-byte property slot:
* small constants (`IsInline`) are stored inline with the MSB 0: bits 62–48 hold the bitwidth and bits 47–0 the two's-complement value;
* otherwise the value is appended to the attribute table and the slot holds its index with the MSB set to 1. -/
def ArithConstantProperties.writeProperty (a : ArithConstantProperties) (addr: UInt64) (bctx : Buffed.IRBufContext)
    (h : addr.toNat + 8 ≤ bctx.mem.size) (_hattrs : bctx.attributes.size < 2^63) : Buffed.IRBufContext :=
  if a.IsInline then
    let w : UInt64 := UInt64.ofNat (a.value.type.bitwidth * 2^48 + (a.value.value % 2^48).toNat)
    { bctx with mem := bctx.mem.blit64 addr w (by grind) }
  else
    let idx : UInt64 := UInt64.ofNat (2^63 + bctx.attributes.size)
    { mem := bctx.mem.blit64 addr idx (by grind),
      attributes := bctx.attributes.push (.integerAttr a.value) }

def ArithConstantProperties.readProperty (addr: UInt64) (bctx : Buffed.IRBufContext) (_h : addr.toNat + 8 ≤ bctx.mem.size) : Option ArithConstantProperties :=
  let w : Nat := (bctx.mem.read64! addr).toNat
  if w < 2^63 then
    -- inline: bits 62–48 are the bitwidth, bits 47–0 the two's-complement value
    let bw : Nat := w / 2^48
    let raw : Nat := w % 2^48
    let v : Int := if raw < 2^47 then (raw : Int) else (raw : Int) - 2^48
    some { value := IntegerAttr.mk v (IntegerType.mk bw) }
  else
    -- MSB set: the remaining 63 bits index the attribute table
    match bctx.attributes[w - 2^63]? with
    | some (Attribute.integerAttr v) => some { value := v }
    | _ => none

@[simp, grind =]
theorem ArithConstantProperties.writeProperty_size (a : ArithConstantProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h hattrs) :
    (a.writeProperty addr bctx h hattrs).mem.size = bctx.mem.size := by
  unfold writeProperty
  split <;> simp

/-- The write at most appends to the attribute table, so existing entries keep their index. -/
theorem ArithConstantProperties.writeProperty_attributes (a : ArithConstantProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h hattrs)
    {i : Nat} {attr : Attribute} (hsome : bctx.attributes[i]? = some attr) :
    (a.writeProperty addr bctx h hattrs).attributes[i]? = some attr := by
  unfold writeProperty
  split
  · exact hsome
  · grind

/-- `readProperty` returns the inline constant when the slot holds an inline encoding (MSB 0). -/
theorem ArithConstantProperties.readProperty_inline (addr : UInt64) (bctx : Buffed.IRBufContext) (h) (bw : Nat) (v : Int)
    (h1 : -(2^47) ≤ v) (h2 : v < 2^47) (h3 : bw < 2^15)
    (hread : (bctx.mem.read64! addr).toNat = bw * 2^48 + (v % 2^48).toNat) :
    ArithConstantProperties.readProperty addr bctx h = some { value := IntegerAttr.mk v (IntegerType.mk bw) } := by
  have ht : (v % 2^48).toNat < 2^48 := by omega
  have he : bw * 2^48 + (v % 2^48).toNat < 2^63 := by omega
  unfold readProperty
  simp only [hread]
  rw [if_pos he]
  simp only [Option.some.injEq, ArithConstantProperties.mk.injEq, IntegerAttr.mk.injEq,
    IntegerType.mk.injEq]
  refine ⟨?_, by omega⟩
  split <;> omega

/-- `readProperty` looks up the attribute table when the slot holds a tagged index (MSB 1). -/
theorem ArithConstantProperties.readProperty_spilled (addr : UInt64) (bctx : Buffed.IRBufContext) (h) {idx : Nat} {v : IntegerAttr}
    (hidx : idx < 2^63)
    (hread : (bctx.mem.read64! addr).toNat = 2^63 + idx)
    (hattr : bctx.attributes[idx]? = some (Attribute.integerAttr v)) :
    ArithConstantProperties.readProperty addr bctx h = some { value := v } := by
  have hsub : 2^63 + idx - 2^63 = idx := by omega
  unfold readProperty
  simp only [hread]
  rw [if_neg (by omega), hsub, hattr]

theorem ArithConstantProperties.readProperty_writeProperty (a : ArithConstantProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h hattrs h') :
    ArithConstantProperties.readProperty addr (a.writeProperty addr bctx h hattrs) h' = some a := by
  obtain ⟨⟨v, ⟨bw⟩⟩⟩ := a
  unfold writeProperty
  split
  next hsm =>
    have h1 : -(2^47) ≤ v := hsm.1
    have h2 : v < 2^47 := hsm.2.1
    have h3 : bw < 2^15 := hsm.2.2
    have ht : (v % 2^48).toNat < 2^48 := by omega
    refine ArithConstantProperties.readProperty_inline addr _ _ bw v h1 h2 h3 ?_
    rw [ExArray.read64!_blit64_self]
    exact _root_UInt64.toNat_UInt64_ofNat_of_lt (by simp only [UInt64.size]; omega)
  next hsm =>
    refine ArithConstantProperties.readProperty_spilled addr _ _ (idx := bctx.attributes.size) hattrs ?_ ?_
    · rw [ExArray.read64!_blit64_self]
      exact _root_UInt64.toNat_UInt64_ofNat_of_lt (by simp only [UInt64.size]; omega)
    · simp

/-- `readProperty` after `writeProperty`, with the bounds check of the instance's `readPropertyAt` still in place. -/
theorem ArithConstantProperties.read_after_write_dite (a : ArithConstantProperties) (addr : UInt64) (bctx : Buffed.IRBufContext)
    (h : addr.toNat + 8 ≤ bctx.mem.size) (hattrs : bctx.attributes.size < 2^63) :
    (if h' : addr.toNat + 8 ≤ (a.writeProperty addr bctx h hattrs).mem.size then
       ArithConstantProperties.readProperty addr (a.writeProperty addr bctx h hattrs) h'
     else none) = some a := by
  rw [dif_pos (by simpa using h)]
  exact readProperty_writeProperty a addr bctx h hattrs _

theorem ArithConstantProperties.writeProperty_read_disjoint {w : Nat} (a : ArithConstantProperties) (addr n len : UInt64) (bctx : Buffed.IRBufContext) (h hattrs)
    (hd : IsDisjoint (n.toNat...(n.toNat + len.toNat)) (addr.toNat...(addr.toNat + 8))) :
    (a.writeProperty addr bctx h hattrs).mem.read! (w := w) n len = bctx.mem.read! n len := by
  unfold writeProperty
  split <;> exact ExArray.read!_blit64_disjoint _ _ _ _ _ (by simpa using hd)

instance : HasBuffedProperties Arith where
  writePropertyAt op p addr bctx h hattrs :=
    match op, p, h with
    | .subi, p, h | .shli, p, h | .trunci, p, h => NswNuwProperties.writeProperty p addr bctx h
    | .divsi, p, h | .divui, p, h | .shrsi, p, h | .shrui, p, h => ExactProperties.writeProperty p addr bctx h
    | .ori, p, h => DisjointProperties.writeProperty p addr bctx h
    | .cmpi, p, h => IcmpProperties.writeProperty p addr bctx h
    | .extui, p, h => NnegProperties.writeProperty p addr bctx h
    | .constant, p, h => ArithConstantProperties.writeProperty p addr bctx h hattrs
    -- the remaining ops have `Unit` properties: nothing to store
    | _, _, _ => bctx
  readPropertyAt op addr bctx :=
    match op with
    | .subi | .shli | .trunci =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then
        NswNuwProperties.readProperty addr bctx h
      else
        none
    | .divsi | .divui | .shrsi | .shrui =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then
        ExactProperties.readProperty addr bctx h
      else
        none
    | .ori =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then
        DisjointProperties.readProperty addr bctx h
      else
        none
    | .cmpi =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then
        IcmpProperties.readProperty addr bctx h
      else
        none
    | .extui =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then
        NnegProperties.readProperty addr bctx h
      else
        none
    | .constant =>
      if h : addr.toNat + 8 ≤ bctx.mem.size then
        ArithConstantProperties.readProperty addr bctx h
      else
        none
    -- the remaining ops have `Unit` properties: nothing to read
    | .addi | .addui_extended | .andi | .ceildivsi | .ceildivui | .extsi
    | .floordivsi | .maxsi | .maxui | .minsi | .minui | .muli | .mulsi_extended
    | .mului_extended | .remsi | .remui | .select | .xori => some ()
  read_after_write {op addr p bctx h hattrs} := by
    cases op
    case constant => exact ArithConstantProperties.read_after_write_dite p addr bctx h hattrs
    case subi => exact NswNuwProperties.read_after_write_dite p addr bctx h
    case shli => exact NswNuwProperties.read_after_write_dite p addr bctx h
    case trunci => exact NswNuwProperties.read_after_write_dite p addr bctx h
    case divsi => exact ExactProperties.read_after_write_dite p addr bctx h
    case divui => exact ExactProperties.read_after_write_dite p addr bctx h
    case shrsi => exact ExactProperties.read_after_write_dite p addr bctx h
    case shrui => exact ExactProperties.read_after_write_dite p addr bctx h
    case ori => exact DisjointProperties.read_after_write_dite p addr bctx h
    case cmpi => exact IcmpProperties.read_after_write_dite p addr bctx h
    case extui => exact NnegProperties.read_after_write_dite p addr bctx h
    all_goals rfl
  only_adds_attributes {a op p addr bctx h hattrs} i hsome := by
    cases op
    case constant => exact ArithConstantProperties.writeProperty_attributes p addr bctx h hattrs hsome
    case subi => simpa using hsome
    case shli => simpa using hsome
    case trunci => simpa using hsome
    case divsi => simpa using hsome
    case divui => simpa using hsome
    case shrsi => simpa using hsome
    case shrui => simpa using hsome
    case ori => simpa using hsome
    case cmpi => simpa using hsome
    case extui => simpa using hsome
    all_goals exact hsome
  preserves_size {op p addr bctx h hattrs} := by
    cases op
    case constant => simp
    case subi => simp
    case shli => simp
    case trunci => simp
    case divsi => simp
    case divui => simp
    case shrsi => simp
    case shrui => simp
    case ori => simp
    case cmpi => simp
    case extui => simp
    all_goals rfl
  only_modifies_properties {op p addr bctx h hattrs w n len} hd := by
    cases op
    case constant => exact ArithConstantProperties.writeProperty_read_disjoint p addr n len bctx h hattrs hd
    case subi => exact NswNuwProperties.writeProperty_read_disjoint p addr n len bctx h hd
    case shli => exact NswNuwProperties.writeProperty_read_disjoint p addr n len bctx h hd
    case trunci => exact NswNuwProperties.writeProperty_read_disjoint p addr n len bctx h hd
    case divsi => exact ExactProperties.writeProperty_read_disjoint p addr n len bctx h hd
    case divui => exact ExactProperties.writeProperty_read_disjoint p addr n len bctx h hd
    case shrsi => exact ExactProperties.writeProperty_read_disjoint p addr n len bctx h hd
    case shrui => exact ExactProperties.writeProperty_read_disjoint p addr n len bctx h hd
    case ori => exact DisjointProperties.writeProperty_read_disjoint p addr n len bctx h hd
    case cmpi => exact IcmpProperties.writeProperty_read_disjoint p addr n len bctx h hd
    case extui => exact NnegProperties.writeProperty_read_disjoint p addr n len bctx h hd
    all_goals rfl


end

end Veir
