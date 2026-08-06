module

public import Veir.Properties
public import Veir.IR.Buffed.RawAccessors

/-!
# Buffered encodings of operation properties

Shared `writeProperty`/`readProperty` implementations (and their laws) for the property
types used by the dialects' `HasBuffedProperties` instances.

Small flag-like properties are stored directly in the operation's property bytes.
Rich properties are spilled: their `Attribute` encoding (an `AttrCodec`) is appended to the
context's attribute table and the property slot stores the entry's 8-byte index.
-/

namespace Veir

public section

/-- Lift a per-type `readProperty` transfer to the bounds-checked read used by
`readPropertyAt`: a successful read survives on any buffer that is at least as large. -/
theorem Buffed.dite_read_frame {P : Type} {sz : Nat} {addr : UInt64} {bctx bctx' : Buffed.IRBufContext} {p : P}
    {read : (b : Buffed.IRBufContext) → addr.toNat + sz ≤ b.mem.size → Option P}
    (hp : (if h : addr.toNat + sz ≤ bctx.mem.size then read bctx h else none) = some p)
    (hsz : bctx.mem.size ≤ bctx'.mem.size)
    (htrans : ∀ h h', read bctx h = some p → read bctx' h' = some p) :
    (if h : addr.toNat + sz ≤ bctx'.mem.size then read bctx' h else none) = some p := by
  split at hp
  next hb => rw [dif_pos (by omega)]; exact htrans hb (by omega) hp
  next => simp at hp

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

/-- The read depends only on the property byte at `addr`. -/
theorem NswNuwProperties.readProperty_frame {addr : UInt64} {bctx bctx' : Buffed.IRBufContext} (h h')
    (hmem : bctx'.mem.read! (w := 8) addr 1 = bctx.mem.read! addr 1) :
    NswNuwProperties.readProperty addr bctx' h' = NswNuwProperties.readProperty addr bctx h := by
  simp only [readProperty, ExArray.read_eq_read!, hmem]

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

/-- The read depends only on the property byte at `addr`. -/
theorem ExactProperties.readProperty_frame {addr : UInt64} {bctx bctx' : Buffed.IRBufContext} (h h')
    (hmem : bctx'.mem.read! (w := 8) addr 1 = bctx.mem.read! addr 1) :
    ExactProperties.readProperty addr bctx' h' = ExactProperties.readProperty addr bctx h := by
  simp only [readProperty, ExArray.read_eq_read!, hmem]

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

/-- The read depends only on the property byte at `addr`. -/
theorem DisjointProperties.readProperty_frame {addr : UInt64} {bctx bctx' : Buffed.IRBufContext} (h h')
    (hmem : bctx'.mem.read! (w := 8) addr 1 = bctx.mem.read! addr 1) :
    DisjointProperties.readProperty addr bctx' h' = DisjointProperties.readProperty addr bctx h := by
  simp only [readProperty, ExArray.read_eq_read!, hmem]

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

/-- The read depends only on the property byte at `addr`. -/
theorem NnegProperties.readProperty_frame {addr : UInt64} {bctx bctx' : Buffed.IRBufContext} (h h')
    (hmem : bctx'.mem.read! (w := 8) addr 1 = bctx.mem.read! addr 1) :
    NnegProperties.readProperty addr bctx' h' = NnegProperties.readProperty addr bctx h := by
  simp only [readProperty, ExArray.read_eq_read!, hmem]

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

/-- The read depends only on the property byte at `addr`. -/
theorem IcmpProperties.readProperty_frame {addr : UInt64} {bctx bctx' : Buffed.IRBufContext} (h h')
    (hmem : bctx'.mem.read! (w := 8) addr 1 = bctx.mem.read! addr 1) :
    IcmpProperties.readProperty addr bctx' h' = IcmpProperties.readProperty addr bctx h := by
  simp only [readProperty, ExArray.read_eq_read!, hmem]

/-- Encode the three fast-math flags in the low bits of a single byte: bit 0 is `nnan`, bit 1 is `ninf`, bit 2 is `nsz`. -/
def FastMathFlagsProperties.writeProperty (a : FastMathFlagsProperties) (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Buffed.IRBufContext :=
  let byte : BitVec 8 := (if a.attr.nnan then 1 else 0) ||| (if a.attr.ninf then 2 else 0) ||| (if a.attr.nsz then 4 else 0)
  { bctx with mem := bctx.mem.blit addr 1 byte (by grind) }

def FastMathFlagsProperties.readProperty (addr: UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) : Option FastMathFlagsProperties :=
  let byte : BitVec 8 := bctx.mem.read addr 1 (by grind)
  some { attr := { nnan := byte &&& 1 != 0, ninf := byte &&& 2 != 0, nsz := byte &&& 4 != 0 } }

@[simp, grind =]
theorem FastMathFlagsProperties.writeProperty_size (a : FastMathFlagsProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).mem.size = bctx.mem.size := by
  simp [writeProperty]

@[simp, grind =]
theorem FastMathFlagsProperties.writeProperty_attributes (a : FastMathFlagsProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h) :
    (a.writeProperty addr bctx h).attributes = bctx.attributes := by
  simp [writeProperty]

theorem FastMathFlagsProperties.readProperty_writeProperty (a : FastMathFlagsProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h h') :
    FastMathFlagsProperties.readProperty addr (a.writeProperty addr bctx h) h' = some a := by
  obtain ⟨⟨nnan, ninf, nsz⟩⟩ := a
  simp only [readProperty, writeProperty, ExArray.read_eq_read!]
  rw [ExArray.read!_blit_self_aligned 8 8 _ _ 1 _ _ rfl (by decide)]
  cases nnan <;> cases ninf <;> cases nsz <;> simp

/-- `readProperty` after `writeProperty`, with the bounds check of the instance's `readPropertyAt` still in place. -/
theorem FastMathFlagsProperties.read_after_write_dite (a : FastMathFlagsProperties) (addr : UInt64) (bctx : Buffed.IRBufContext) (h : addr.toNat + 1 ≤ bctx.mem.size) :
    (if h' : addr.toNat + 1 ≤ (a.writeProperty addr bctx h).mem.size then
       FastMathFlagsProperties.readProperty addr (a.writeProperty addr bctx h) h'
     else none) = some a := by
  rw [dif_pos (by simpa using h)]
  exact readProperty_writeProperty a addr bctx h _

theorem FastMathFlagsProperties.writeProperty_read_disjoint {w : Nat} (a : FastMathFlagsProperties) (addr n len : UInt64) (bctx : Buffed.IRBufContext) (h)
    (hd : IsDisjoint (n.toNat...(n.toNat + len.toNat)) (addr.toNat...(addr.toNat + 1))) :
    (a.writeProperty addr bctx h).mem.read! (w := w) n len = bctx.mem.read! n len := by
  simp only [writeProperty]
  exact ExArray.read!_blit_disjoint _ _ _ _ _ (by simpa using hd)

/-- The read depends only on the property byte at `addr`. -/
theorem FastMathFlagsProperties.readProperty_frame {addr : UInt64} {bctx bctx' : Buffed.IRBufContext} (h h')
    (hmem : bctx'.mem.read! (w := 8) addr 1 = bctx.mem.read! addr 1) :
    FastMathFlagsProperties.readProperty addr bctx' h' = FastMathFlagsProperties.readProperty addr bctx h := by
  simp only [readProperty, ExArray.read_eq_read!, hmem]

/-! ## Encoding property fields as `Attribute`s -/

def Attribute.ofBool (b : Bool) : Attribute :=
  .integerAttr ⟨if b then 1 else 0, ⟨1⟩⟩

def Attribute.toBool? : Attribute → Option Bool
  | .integerAttr v => some (v.value != 0)
  | _ => none

@[simp]
theorem Attribute.toBool?_ofBool (b : Bool) : (Attribute.ofBool b).toBool? = some b := by
  cases b <;> simp [ofBool, toBool?]

def Attribute.ofOptStringAttr : Option StringAttr → Attribute
  | none => .unitAttr ⟨⟩
  | some s => .stringAttr s

def Attribute.toOptStringAttr? : Attribute → Option (Option StringAttr)
  | .unitAttr _ => some none
  | .stringAttr s => some (some s)
  | _ => none

@[simp]
theorem Attribute.toOptStringAttr?_ofOptStringAttr (o : Option StringAttr) :
    (Attribute.ofOptStringAttr o).toOptStringAttr? = some o := by
  cases o <;> simp [ofOptStringAttr, toOptStringAttr?]

def Attribute.toTypeAttr? (a : Attribute) : Option TypeAttr :=
  if h : a.isType then some ⟨a, h⟩ else none

@[simp]
theorem Attribute.toTypeAttr?_val (t : TypeAttr) : t.val.toTypeAttr? = some t := by
  unfold toTypeAttr?
  rw [dif_pos t.property]
  rfl

/-- `none` is encoded as the unit attribute, which is never a type, so the encoding is unambiguous. -/
def Attribute.ofOptTypeAttr : Option TypeAttr → Attribute
  | none => .unitAttr ⟨⟩
  | some t => t.val

def Attribute.toOptTypeAttr? (a : Attribute) : Option (Option TypeAttr) :=
  if h : a.isType then some (some ⟨a, h⟩)
  else match a with
    | .unitAttr _ => some none
    | _ => none

@[simp]
theorem Attribute.toOptTypeAttr?_ofOptTypeAttr (o : Option TypeAttr) :
    (Attribute.ofOptTypeAttr o).toOptTypeAttr? = some o := by
  cases o with
  | none => simp [ofOptTypeAttr, toOptTypeAttr?, Attribute.isType_unitAttr]
  | some t =>
    show Attribute.toOptTypeAttr? t.val = some (some t)
    unfold toOptTypeAttr?
    rw [dif_pos t.property]
    rfl

/-! ## Spilled properties: an `Attribute` encoding stored in the attribute table -/

/-- An injection of a property type into `Attribute`, used to spill rich properties into the
attribute table: `writeProperty` appends `enc p` to the table and stores its index in the
8-byte property slot. -/
structure AttrCodec (P : Type) where
  enc : P → Attribute
  dec : Attribute → Option P
  dec_enc : ∀ p, dec (enc p) = some p

namespace AttrCodec

variable {P : Type} (c : AttrCodec P)

def writeProperty (p : P) (addr: UInt64) (bctx : Buffed.IRBufContext)
    (h : addr.toNat + 8 ≤ bctx.mem.size) (_hattrs : bctx.attributes.size < 2^63) : Buffed.IRBufContext :=
  let idx : UInt64 := UInt64.ofNat bctx.attributes.size
  { mem := bctx.mem.blit64 addr idx (by grind),
    attributes := bctx.attributes.push (c.enc p) }

def readProperty (addr: UInt64) (bctx : Buffed.IRBufContext) (_h : addr.toNat + 8 ≤ bctx.mem.size) : Option P :=
  match bctx.attributes[(bctx.mem.read64! addr).toNat]? with
  | some attr => c.dec attr
  | none => none

@[simp, grind =]
theorem writeProperty_size (p : P) (addr : UInt64) (bctx : Buffed.IRBufContext) (h hattrs) :
    (c.writeProperty p addr bctx h hattrs).mem.size = bctx.mem.size := by
  simp [writeProperty]

/-- The write only appends to the attribute table, so existing entries keep their index. -/
theorem writeProperty_attributes (p : P) (addr : UInt64) (bctx : Buffed.IRBufContext) (h hattrs)
    {i : Nat} {attr : Attribute} (hsome : bctx.attributes[i]? = some attr) :
    (c.writeProperty p addr bctx h hattrs).attributes[i]? = some attr := by
  unfold writeProperty
  grind

/-- `readProperty` decodes the table entry referenced by the stored index. -/
theorem readProperty_at (addr : UInt64) (bctx : Buffed.IRBufContext) (h) {idx : Nat} {attr : Attribute}
    (hread : (bctx.mem.read64! addr).toNat = idx)
    (hattr : bctx.attributes[idx]? = some attr) :
    c.readProperty addr bctx h = c.dec attr := by
  unfold readProperty
  simp only [hread, hattr]

theorem readProperty_writeProperty (p : P) (addr : UInt64) (bctx : Buffed.IRBufContext) (h hattrs h') :
    c.readProperty addr (c.writeProperty p addr bctx h hattrs) h' = some p := by
  have hread : ((c.writeProperty p addr bctx h hattrs).mem.read64! addr).toNat = bctx.attributes.size := by
    unfold writeProperty
    rw [ExArray.read64!_blit64_self]
    exact _root_UInt64.toNat_UInt64_ofNat_of_lt (by simp only [UInt64.size]; omega)
  have hattr : (c.writeProperty p addr bctx h hattrs).attributes[bctx.attributes.size]? = some (c.enc p) := by
    unfold writeProperty
    simp
  rw [c.readProperty_at _ _ _ hread hattr, c.dec_enc]

/-- `readProperty` after `writeProperty`, with the bounds check of the instance's `readPropertyAt` still in place. -/
theorem read_after_write_dite (p : P) (addr : UInt64) (bctx : Buffed.IRBufContext)
    (h : addr.toNat + 8 ≤ bctx.mem.size) (hattrs : bctx.attributes.size < 2^63) :
    (if h' : addr.toNat + 8 ≤ (c.writeProperty p addr bctx h hattrs).mem.size then
       c.readProperty addr (c.writeProperty p addr bctx h hattrs) h'
     else none) = some p := by
  rw [dif_pos (by simpa using h)]
  exact c.readProperty_writeProperty p addr bctx h hattrs _

theorem writeProperty_read_disjoint {w : Nat} (p : P) (addr n len : UInt64) (bctx : Buffed.IRBufContext) (h hattrs)
    (hd : IsDisjoint (n.toNat...(n.toNat + len.toNat)) (addr.toNat...(addr.toNat + 8))) :
    (c.writeProperty p addr bctx h hattrs).mem.read! (w := w) n len = bctx.mem.read! n len := by
  unfold writeProperty
  exact ExArray.read!_blit64_disjoint _ _ _ _ _ (by simpa using hd)

/-- A successful read survives on any buffer agreeing on the index word whose attribute
lookups extend those of `bctx` (only one direction: the table of `bctx'` may be larger,
so a failing read need not stay failing). -/
theorem readProperty_frame {addr : UInt64} {bctx bctx' : Buffed.IRBufContext} (h h') {p : P}
    (hp : c.readProperty addr bctx h = some p)
    (hmem : bctx'.mem.read64! addr = bctx.mem.read64! addr)
    (hattrs : ∀ (i : Nat) (a : Attribute), bctx.attributes[i]? = some a → bctx'.attributes[i]? = some a) :
    c.readProperty addr bctx' h' = some p := by
  unfold readProperty at hp ⊢
  rw [hmem]
  rcases hm : bctx.attributes[(bctx.mem.read64! addr).toNat]? with _ | attr <;> rw [hm] at hp
  · simp at hp
  · rw [hattrs _ _ hm]; exact hp

end AttrCodec

end

end Veir
