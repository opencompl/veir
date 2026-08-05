module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties
public import Veir.IR.Buffed.RawAccessors

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

/-- Encode the two flags in the low bits of a single byte: bit 0 is `nsw`, bit 1 is `nuw` (the same layout as MLIR's `overflowFlags`). -/
def NswNuwProperties.writeProperty (a : NswNuwProperties) (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Buffed.IRBufContext :=
  let byte : BitVec 8 := (if a.nsw then 1 else 0) ||| (if a.nuw then 2 else 0)
  { bctx with mem := bctx.mem.blit addr 1 byte (by grind) }

def NswNuwProperties.readProperty (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Option NswNuwProperties :=
  let byte : BitVec 8 := bctx.mem.read addr 1 (by grind)
  some { nsw := byte &&& 1 != 0, nuw := byte &&& 2 != 0 }

@[simp, grind =]
theorem NswNuwProperties.writeProperty_size (a : NswNuwProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).mem.size = bctx.mem.size := by
  simp [writeProperty]

@[simp, grind =]
theorem NswNuwProperties.writeProperty_attributes (a : NswNuwProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).attributes = bctx.attributes := by
  simp [writeProperty]

theorem NswNuwProperties.readProperty_writeProperty (a : NswNuwProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h h') :
    NswNuwProperties.readProperty addr (a.writeProperty addr bctx h) h' = some a := by
  obtain ⟨nsw, nuw⟩ := a
  simp only [readProperty, writeProperty, ExArray.read_eq_read!]
  rw [ExArray.read!_blit_self_aligned 8 8 _ _ 1 _ _ rfl (by decide)]
  cases nsw <;> cases nuw <;> simp

/-- `readProperty` after `writeProperty`, with the bounds check of the instance's `readPropertyAt` still in place. -/
theorem NswNuwProperties.read_after_write_dite (a : NswNuwProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) :
    (if h' : addr.toNat + 1 ≤ (a.writeProperty addr bctx h).mem.size then
       NswNuwProperties.readProperty addr (a.writeProperty addr bctx h) h'
     else none) = some a := by
  rw [dif_pos (by simpa using h)]
  exact readProperty_writeProperty a addr bctx h _

theorem NswNuwProperties.writeProperty_read_disjoint {w : Nat} (a : NswNuwProperties) (addr n len : UInt64) (bctx : Buffed.IRBufContext) (h)
    (hd : IsDisjoint (n.toNat...(n.toNat + len.toNat)) (addr.toNat...(addr.toNat + 1))) :
    (a.writeProperty addr bctx h).mem.read! (w := w) n len = bctx.mem.read! n len := by
  simp only [writeProperty]
  exact ExArray.read!_blit_disjoint _ _ _ _ _ (by simpa using hd)

/-- Encode the `exact` flag in bit 0 of a single byte. -/
def ExactProperties.writeProperty (a : ExactProperties) (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Buffed.IRBufContext :=
  let byte : BitVec 8 := if a.exact then 1 else 0
  { bctx with mem := bctx.mem.blit addr 1 byte (by grind) }

def ExactProperties.readProperty (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Option ExactProperties :=
  let byte : BitVec 8 := bctx.mem.read addr 1 (by grind)
  some { exact := byte &&& 1 != 0 }

@[simp, grind =]
theorem ExactProperties.writeProperty_size (a : ExactProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).mem.size = bctx.mem.size := by
  simp [writeProperty]

@[simp, grind =]
theorem ExactProperties.writeProperty_attributes (a : ExactProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).attributes = bctx.attributes := by
  simp [writeProperty]

theorem ExactProperties.readProperty_writeProperty (a : ExactProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h h') :
    ExactProperties.readProperty addr (a.writeProperty addr bctx h) h' = some a := by
  obtain ⟨e⟩ := a
  simp only [readProperty, writeProperty, ExArray.read_eq_read!]
  rw [ExArray.read!_blit_self_aligned 8 8 _ _ 1 _ _ rfl (by decide)]
  cases e <;> simp

/-- `readProperty` after `writeProperty`, with the bounds check of the instance's `readPropertyAt` still in place. -/
theorem ExactProperties.read_after_write_dite (a : ExactProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) :
    (if h' : addr.toNat + 1 ≤ (a.writeProperty addr bctx h).mem.size then
       ExactProperties.readProperty addr (a.writeProperty addr bctx h) h'
     else none) = some a := by
  rw [dif_pos (by simpa using h)]
  exact readProperty_writeProperty a addr bctx h _

theorem ExactProperties.writeProperty_read_disjoint {w : Nat} (a : ExactProperties) (addr n len : UInt64) (bctx : Buffed.IRBufContext) (h)
    (hd : IsDisjoint (n.toNat...(n.toNat + len.toNat)) (addr.toNat...(addr.toNat + 1))) :
    (a.writeProperty addr bctx h).mem.read! (w := w) n len = bctx.mem.read! n len := by
  simp only [writeProperty]
  exact ExArray.read!_blit_disjoint _ _ _ _ _ (by simpa using hd)

/-- Encode the `disjoint` flag in bit 0 of a single byte. -/
def DisjointProperties.writeProperty (a : DisjointProperties) (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Buffed.IRBufContext :=
  let byte : BitVec 8 := if a.disjoint then 1 else 0
  { bctx with mem := bctx.mem.blit addr 1 byte (by grind) }

def DisjointProperties.readProperty (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Option DisjointProperties :=
  let byte : BitVec 8 := bctx.mem.read addr 1 (by grind)
  some { disjoint := byte &&& 1 != 0 }

@[simp, grind =]
theorem DisjointProperties.writeProperty_size (a : DisjointProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).mem.size = bctx.mem.size := by
  simp [writeProperty]

@[simp, grind =]
theorem DisjointProperties.writeProperty_attributes (a : DisjointProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).attributes = bctx.attributes := by
  simp [writeProperty]

theorem DisjointProperties.readProperty_writeProperty (a : DisjointProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h h') :
    DisjointProperties.readProperty addr (a.writeProperty addr bctx h) h' = some a := by
  obtain ⟨d⟩ := a
  simp only [readProperty, writeProperty, ExArray.read_eq_read!]
  rw [ExArray.read!_blit_self_aligned 8 8 _ _ 1 _ _ rfl (by decide)]
  cases d <;> simp

/-- `readProperty` after `writeProperty`, with the bounds check of the instance's `readPropertyAt` still in place. -/
theorem DisjointProperties.read_after_write_dite (a : DisjointProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) :
    (if h' : addr.toNat + 1 ≤ (a.writeProperty addr bctx h).mem.size then
       DisjointProperties.readProperty addr (a.writeProperty addr bctx h) h'
     else none) = some a := by
  rw [dif_pos (by simpa using h)]
  exact readProperty_writeProperty a addr bctx h _

theorem DisjointProperties.writeProperty_read_disjoint {w : Nat} (a : DisjointProperties) (addr n len : UInt64) (bctx : Buffed.IRBufContext) (h)
    (hd : IsDisjoint (n.toNat...(n.toNat + len.toNat)) (addr.toNat...(addr.toNat + 1))) :
    (a.writeProperty addr bctx h).mem.read! (w := w) n len = bctx.mem.read! n len := by
  simp only [writeProperty]
  exact ExArray.read!_blit_disjoint _ _ _ _ _ (by simpa using hd)

/-- Encode the `nneg` flag in bit 0 of a single byte. -/
def NnegProperties.writeProperty (a : NnegProperties) (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Buffed.IRBufContext :=
  let byte : BitVec 8 := if a.nneg then 1 else 0
  { bctx with mem := bctx.mem.blit addr 1 byte (by grind) }

def NnegProperties.readProperty (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Option NnegProperties :=
  let byte : BitVec 8 := bctx.mem.read addr 1 (by grind)
  some { nneg := byte &&& 1 != 0 }

@[simp, grind =]
theorem NnegProperties.writeProperty_size (a : NnegProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).mem.size = bctx.mem.size := by
  simp [writeProperty]

@[simp, grind =]
theorem NnegProperties.writeProperty_attributes (a : NnegProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).attributes = bctx.attributes := by
  simp [writeProperty]

theorem NnegProperties.readProperty_writeProperty (a : NnegProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h h') :
    NnegProperties.readProperty addr (a.writeProperty addr bctx h) h' = some a := by
  obtain ⟨n⟩ := a
  simp only [readProperty, writeProperty, ExArray.read_eq_read!]
  rw [ExArray.read!_blit_self_aligned 8 8 _ _ 1 _ _ rfl (by decide)]
  cases n <;> simp

/-- `readProperty` after `writeProperty`, with the bounds check of the instance's `readPropertyAt` still in place. -/
theorem NnegProperties.read_after_write_dite (a : NnegProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) :
    (if h' : addr.toNat + 1 ≤ (a.writeProperty addr bctx h).mem.size then
       NnegProperties.readProperty addr (a.writeProperty addr bctx h) h'
     else none) = some a := by
  rw [dif_pos (by simpa using h)]
  exact readProperty_writeProperty a addr bctx h _

theorem NnegProperties.writeProperty_read_disjoint {w : Nat} (a : NnegProperties) (addr n len : UInt64) (bctx : Buffed.IRBufContext) (h)
    (hd : IsDisjoint (n.toNat...(n.toNat + len.toNat)) (addr.toNat...(addr.toNat + 1))) :
    (a.writeProperty addr bctx h).mem.read! (w := w) n len = bctx.mem.read! n len := by
  simp only [writeProperty]
  exact ExArray.read!_blit_disjoint _ _ _ _ _ (by simpa using hd)

/-- Encode the comparison predicate as its MLIR numeric code (0–9, see `IntPred.fromNat`) in a single byte. -/
def IcmpProperties.writeProperty (a : IcmpProperties) (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Buffed.IRBufContext :=
  let byte : BitVec 8 := BitVec.ofNat 8 a.predicate.toNat
  { bctx with mem := bctx.mem.blit addr 1 byte (by grind) }

def IcmpProperties.readProperty (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Option IcmpProperties :=
  let byte : BitVec 8 := bctx.mem.read addr 1 (by grind)
  (Data.LLVM.IntPred.fromNat byte.toNat).map ({ predicate := · })

@[simp, grind =]
theorem IcmpProperties.writeProperty_size (a : IcmpProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).mem.size = bctx.mem.size := by
  simp [writeProperty]

@[simp, grind =]
theorem IcmpProperties.writeProperty_attributes (a : IcmpProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).attributes = bctx.attributes := by
  simp [writeProperty]

theorem IcmpProperties.readProperty_writeProperty (a : IcmpProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h h') :
    IcmpProperties.readProperty addr (a.writeProperty addr bctx h) h' = some a := by
  obtain ⟨p⟩ := a
  simp only [readProperty, writeProperty, ExArray.read_eq_read!]
  rw [ExArray.read!_blit_self_aligned 8 8 _ _ 1 _ _ rfl (by decide)]
  cases p <;> simp [Data.LLVM.IntPred.toNat, Data.LLVM.IntPred.fromNat]

/-- `readProperty` after `writeProperty`, with the bounds check of the instance's `readPropertyAt` still in place. -/
theorem IcmpProperties.read_after_write_dite (a : IcmpProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) :
    (if h' : addr.toNat + 1 ≤ (a.writeProperty addr bctx h).mem.size then
       IcmpProperties.readProperty addr (a.writeProperty addr bctx h) h'
     else none) = some a := by
  rw [dif_pos (by simpa using h)]
  exact readProperty_writeProperty a addr bctx h _

theorem IcmpProperties.writeProperty_read_disjoint {w : Nat} (a : IcmpProperties) (addr n len : UInt64) (bctx : Buffed.IRBufContext) (h)
    (hd : IsDisjoint (n.toNat...(n.toNat + len.toNat)) (addr.toNat...(addr.toNat + 1))) :
    (a.writeProperty addr bctx h).mem.read! (w := w) n len = bctx.mem.read! n len := by
  simp only [writeProperty]
  exact ExArray.read!_blit_disjoint _ _ _ _ _ (by simpa using hd)

/-- Store the constant's value: append it to the attribute table and write its index as the 8-byte property. -/
def ArithConstantProperties.writeProperty (a : ArithConstantProperties) (addr: UInt64) (bctx : Buffed.IRBufContext)
    (h : addr.toNat + 8 ≤ bctx.mem.size) (_hattrs : bctx.attributes.size < UInt64.size) : Buffed.IRBufContext :=
  let idx : UInt64 := UInt64.ofNat bctx.attributes.size
  { mem := bctx.mem.blit64 addr idx (by grind),
    attributes := bctx.attributes.push (.integerAttr a.value) }

def ArithConstantProperties.readProperty (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 8 ≤ bctx.mem.size) : Option ArithConstantProperties :=
  let idx := bctx.mem.read64 addr (by grind)
  match bctx.attributes[idx.toNat]? with
  | some (.integerAttr v) => some { value := v }
  | _ => none

@[simp, grind =]
theorem ArithConstantProperties.writeProperty_size (a : ArithConstantProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h hattrs) :
    (a.writeProperty addr bctx h hattrs).mem.size = bctx.mem.size := by
  simp [writeProperty]

/-- The write only appends to the attribute table, so existing entries keep their index. -/
theorem ArithConstantProperties.writeProperty_attributes (a : ArithConstantProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h hattrs)
    {i : Nat} {attr : Attribute} (hsome : bctx.attributes[i]? = some attr) :
    (a.writeProperty addr bctx h hattrs).attributes[i]? = some attr := by
  simp only [writeProperty]
  grind

theorem ArithConstantProperties.readProperty_writeProperty (a : ArithConstantProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h hattrs h') :
    ArithConstantProperties.readProperty addr (a.writeProperty addr bctx h hattrs) h' = some a := by
  obtain ⟨v⟩ := a
  simp only [readProperty, writeProperty, ExArray.read64_eq_read64!, ExArray.read64!_blit64_self]
  rw [show (UInt64.ofNat bctx.attributes.size).toNat = bctx.attributes.size from by grind]
  simp

/-- `readProperty` after `writeProperty`, with the bounds check of the instance's `readPropertyAt` still in place. -/
theorem ArithConstantProperties.read_after_write_dite (a : ArithConstantProperties) (addr : UInt64) (bctx : Buffed.IRBufContext)
    (h : addr.toNat + 8 ≤ bctx.mem.size) (hattrs : bctx.attributes.size < UInt64.size) :
    (if h' : addr.toNat + 8 ≤ (a.writeProperty addr bctx h hattrs).mem.size then
       ArithConstantProperties.readProperty addr (a.writeProperty addr bctx h hattrs) h'
     else none) = some a := by
  rw [dif_pos (by simpa using h)]
  exact readProperty_writeProperty a addr bctx h hattrs _

theorem ArithConstantProperties.writeProperty_read_disjoint {w : Nat} (a : ArithConstantProperties) (addr n len : UInt64) (bctx : Buffed.IRBufContext) (h hattrs)
    (hd : IsDisjoint (n.toNat...(n.toNat + len.toNat)) (addr.toNat...(addr.toNat + 8))) :
    (a.writeProperty addr bctx h hattrs).mem.read! (w := w) n len = bctx.mem.read! n len := by
  simp only [writeProperty]
  exact ExArray.read!_blit64_disjoint _ _ _ _ _ (by simpa using hd)

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
