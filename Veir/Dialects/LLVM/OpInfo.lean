module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties
public import Veir.Dialects.BuffedProperties

namespace Veir

public section

@[expose, properties_of]
def Llvm.propertiesOf (op : Llvm) : Type :=
match op with
| .mlir__constant => LLVMConstantProperties
| .add => NswNuwProperties
| .sub => NswNuwProperties
| .mul => NswNuwProperties
| .udiv => ExactProperties
| .sdiv => ExactProperties
| .shl => NswNuwProperties
| .lshr => ExactProperties
| .ashr => ExactProperties
| .or => DisjointProperties
| .trunc => NswNuwProperties
| .zext => NnegProperties
| .icmp => IcmpProperties
| .cond_br => CondBrProperties
| .alloca => AllocaProperties
| .load => LoadProperties -- attribute
| .store => StoreProperties -- attribute
| .getelementptr => GetelementptrProperties -- attribute
| .fadd | .fsub | .fmul | .fdiv | .frem => FastMathFlagsProperties
| .func => LLVMFuncProperties
| .module_flags => LLVMModuleFlagsProperties
| _ => Unit

@[expose]
def Llvm.propertySize (op : Llvm) : UInt64 :=
match op with
| .mlir__constant => 8 -- attribute
| .add => 1
| .sub => 1
| .mul => 1
| .udiv => 1
| .sdiv => 1
| .shl => 1
| .lshr => 1
| .ashr => 1
| .or => 1
| .trunc => 1
| .zext => 1
| .icmp => 1
| .cond_br => 8 -- attribute
| .alloca => 8 -- attribute
| .load => 8 -- attribute
| .store => 8 -- attribute
| .getelementptr => 8 -- attribute
| .fadd | .fsub | .fmul | .fdiv | .frem => 1
| .func => 8
| .module_flags => 8
| _ => 0


instance : HasDialectOpInfo Llvm where
  propertiesOf := Llvm.propertiesOf
  propertySize op := Llvm.propertySize op
  propertySize_small {op} := by cases op <;> simp [Llvm.propertySize]

/-! ## `Attribute` codecs for the spilled (8-byte, table-indexed) property types -/

def LLVMConstantProperties.toAttr : LLVMConstantProperties → Attribute
  | ⟨.integer v⟩ => .integerAttr v
  | ⟨.float v⟩ => .floatAttr v

def LLVMConstantProperties.ofAttr? : Attribute → Option LLVMConstantProperties
  | .integerAttr v => some ⟨.integer v⟩
  | .floatAttr v => some ⟨.float v⟩
  | _ => none

theorem LLVMConstantProperties.ofAttr?_toAttr (p : LLVMConstantProperties) : ofAttr? p.toAttr = some p := by
  obtain ⟨v⟩ := p
  cases v <;> simp [toAttr, ofAttr?]

def LLVMConstantProperties.codec : AttrCodec LLVMConstantProperties :=
  ⟨toAttr, ofAttr?, ofAttr?_toAttr⟩

def LLVMModuleFlagsProperties.toAttr (p : LLVMModuleFlagsProperties) : Attribute :=
  .arrayAttr p.flags

def LLVMModuleFlagsProperties.ofAttr? : Attribute → Option LLVMModuleFlagsProperties
  | .arrayAttr f => some ⟨f⟩
  | _ => none

theorem LLVMModuleFlagsProperties.ofAttr?_toAttr (p : LLVMModuleFlagsProperties) : ofAttr? p.toAttr = some p := by
  obtain ⟨f⟩ := p
  simp [toAttr, ofAttr?]

def LLVMModuleFlagsProperties.codec : AttrCodec LLVMModuleFlagsProperties :=
  ⟨toAttr, ofAttr?, ofAttr?_toAttr⟩

def CondBrProperties.toAttr (p : CondBrProperties) : Attribute :=
  .arrayAttr ⟨⟨[.denseArrayAttr p.branch_weights, .denseArrayAttr p.operandSegmentSizes]⟩⟩

def CondBrProperties.ofAttr? : Attribute → Option CondBrProperties
  | .arrayAttr ⟨⟨[.denseArrayAttr w, .denseArrayAttr s]⟩⟩ => some ⟨w, s⟩
  | _ => none

theorem CondBrProperties.ofAttr?_toAttr (p : CondBrProperties) : ofAttr? p.toAttr = some p := by
  obtain ⟨w, s⟩ := p
  simp [toAttr, ofAttr?]

def CondBrProperties.codec : AttrCodec CondBrProperties :=
  ⟨toAttr, ofAttr?, ofAttr?_toAttr⟩

def AllocaProperties.toAttr (p : AllocaProperties) : Attribute :=
  .arrayAttr ⟨⟨[.integerAttr p.alignment, p.elem_type.val, .ofBool p.inalloca]⟩⟩

def AllocaProperties.ofAttr? : Attribute → Option AllocaProperties
  | .arrayAttr ⟨⟨[.integerAttr al, ty, b]⟩⟩ => do
    let elem_type ← ty.toTypeAttr?
    let inalloca ← b.toBool?
    some ⟨al, elem_type, inalloca⟩
  | _ => none

theorem AllocaProperties.ofAttr?_toAttr (p : AllocaProperties) : ofAttr? p.toAttr = some p := by
  obtain ⟨al, ty, b⟩ := p
  simp [toAttr, ofAttr?]

def AllocaProperties.codec : AttrCodec AllocaProperties :=
  ⟨toAttr, ofAttr?, ofAttr?_toAttr⟩

def GetelementptrProperties.toAttr (p : GetelementptrProperties) : Attribute :=
  .arrayAttr ⟨⟨[.denseArrayAttr p.rawConstantIndices, p.elem_type.val, .integerAttr p.noWrapFlags]⟩⟩

def GetelementptrProperties.ofAttr? : Attribute → Option GetelementptrProperties
  | .arrayAttr ⟨⟨[.denseArrayAttr idxs, ty, .integerAttr flags]⟩⟩ => do
    let elem_type ← ty.toTypeAttr?
    some ⟨idxs, elem_type, flags⟩
  | _ => none

theorem GetelementptrProperties.ofAttr?_toAttr (p : GetelementptrProperties) : ofAttr? p.toAttr = some p := by
  obtain ⟨idxs, ty, flags⟩ := p
  simp [toAttr, ofAttr?]

def GetelementptrProperties.codec : AttrCodec GetelementptrProperties :=
  ⟨toAttr, ofAttr?, ofAttr?_toAttr⟩

def LLVMFuncProperties.toAttr (p : LLVMFuncProperties) : Attribute :=
  .arrayAttr ⟨⟨[.ofOptStringAttr p.sym_name, .ofOptTypeAttr p.function_type, .dictionaryAttr p.extra]⟩⟩

def LLVMFuncProperties.ofAttr? : Attribute → Option LLVMFuncProperties
  | .arrayAttr ⟨⟨[sn, ft, .dictionaryAttr extra]⟩⟩ => do
    let sym_name ← sn.toOptStringAttr?
    let function_type ← ft.toOptTypeAttr?
    some ⟨sym_name, function_type, extra⟩
  | _ => none

theorem LLVMFuncProperties.ofAttr?_toAttr (p : LLVMFuncProperties) : ofAttr? p.toAttr = some p := by
  obtain ⟨sn, ft, extra⟩ := p
  simp [toAttr, ofAttr?]

def LLVMFuncProperties.codec : AttrCodec LLVMFuncProperties :=
  ⟨toAttr, ofAttr?, ofAttr?_toAttr⟩

def LoadProperties.toAttr (p : LoadProperties) : Attribute :=
  .arrayAttr ⟨⟨[.integerAttr p.alignment, .ofBool p.volatile_, .ofBool p.nontemporal,
    .ofBool p.invariant, .ofBool p.invariantGroup, .ofOptStringAttr p.syncscope,
    .arrayAttr p.access_groups, .arrayAttr p.alias_scopes, .arrayAttr p.noalias_scopes,
    .arrayAttr p.tbaa]⟩⟩

def LoadProperties.ofAttr? : Attribute → Option LoadProperties
  | .arrayAttr ⟨⟨[.integerAttr al, v, nt, inv, ig, ss,
      .arrayAttr ag, .arrayAttr als, .arrayAttr nas, .arrayAttr tb]⟩⟩ => do
    let volatile_ ← v.toBool?
    let nontemporal ← nt.toBool?
    let invariant ← inv.toBool?
    let invariantGroup ← ig.toBool?
    let syncscope ← ss.toOptStringAttr?
    some ⟨al, volatile_, nontemporal, invariant, invariantGroup, syncscope, ag, als, nas, tb⟩
  | _ => none

theorem LoadProperties.ofAttr?_toAttr (p : LoadProperties) : ofAttr? p.toAttr = some p := by
  obtain ⟨al, v, nt, inv, ig, ss, ag, als, nas, tb⟩ := p
  simp [toAttr, ofAttr?]

def LoadProperties.codec : AttrCodec LoadProperties :=
  ⟨toAttr, ofAttr?, ofAttr?_toAttr⟩

def StoreProperties.toAttr (p : StoreProperties) : Attribute :=
  .arrayAttr ⟨⟨[.integerAttr p.alignment, .ofBool p.volatile_, .ofBool p.nontemporal,
    .ofBool p.invariantGroup, .ofOptStringAttr p.syncscope,
    .arrayAttr p.access_groups, .arrayAttr p.alias_scopes, .arrayAttr p.noalias_scopes,
    .arrayAttr p.tbaa]⟩⟩

def StoreProperties.ofAttr? : Attribute → Option StoreProperties
  | .arrayAttr ⟨⟨[.integerAttr al, v, nt, ig, ss,
      .arrayAttr ag, .arrayAttr als, .arrayAttr nas, .arrayAttr tb]⟩⟩ => do
    let volatile_ ← v.toBool?
    let nontemporal ← nt.toBool?
    let invariantGroup ← ig.toBool?
    let syncscope ← ss.toOptStringAttr?
    some ⟨al, volatile_, nontemporal, invariantGroup, syncscope, ag, als, nas, tb⟩
  | _ => none

theorem StoreProperties.ofAttr?_toAttr (p : StoreProperties) : ofAttr? p.toAttr = some p := by
  obtain ⟨al, v, nt, ig, ss, ag, als, nas, tb⟩ := p
  simp [toAttr, ofAttr?]

def StoreProperties.codec : AttrCodec StoreProperties :=
  ⟨toAttr, ofAttr?, ofAttr?_toAttr⟩

/-! ## The buffed-properties instance -/

instance : HasBuffedProperties Llvm where
  writePropertyAt op p addr bctx h hattrs :=
    match op, p, h with
    | .add, p, h | .sub, p, h | .mul, p, h | .shl, p, h | .trunc, p, h =>
      NswNuwProperties.writeProperty p addr bctx h
    | .udiv, p, h | .sdiv, p, h | .lshr, p, h | .ashr, p, h =>
      ExactProperties.writeProperty p addr bctx h
    | .or, p, h => DisjointProperties.writeProperty p addr bctx h
    | .zext, p, h => NnegProperties.writeProperty p addr bctx h
    | .icmp, p, h => IcmpProperties.writeProperty p addr bctx h
    | .fadd, p, h | .fsub, p, h | .fmul, p, h | .fdiv, p, h | .frem, p, h =>
      FastMathFlagsProperties.writeProperty p addr bctx h
    | .mlir__constant, p, h => LLVMConstantProperties.codec.writeProperty p addr bctx h hattrs
    | .cond_br, p, h => CondBrProperties.codec.writeProperty p addr bctx h hattrs
    | .alloca, p, h => AllocaProperties.codec.writeProperty p addr bctx h hattrs
    | .load, p, h => LoadProperties.codec.writeProperty p addr bctx h hattrs
    | .store, p, h => StoreProperties.codec.writeProperty p addr bctx h hattrs
    | .getelementptr, p, h => GetelementptrProperties.codec.writeProperty p addr bctx h hattrs
    | .func, p, h => LLVMFuncProperties.codec.writeProperty p addr bctx h hattrs
    | .module_flags, p, h => LLVMModuleFlagsProperties.codec.writeProperty p addr bctx h hattrs
    -- the remaining ops have `Unit` properties: nothing to store
    | _, _, _ => bctx
  readPropertyAt op addr bctx :=
    match op with
    | .add | .sub | .mul | .shl | .trunc =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then NswNuwProperties.readProperty addr bctx h else none
    | .udiv | .sdiv | .lshr | .ashr =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then ExactProperties.readProperty addr bctx h else none
    | .or =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then DisjointProperties.readProperty addr bctx h else none
    | .zext =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then NnegProperties.readProperty addr bctx h else none
    | .icmp =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then IcmpProperties.readProperty addr bctx h else none
    | .fadd | .fsub | .fmul | .fdiv | .frem =>
      if h : addr.toNat + 1 ≤ bctx.mem.size then FastMathFlagsProperties.readProperty addr bctx h else none
    | .mlir__constant =>
      if h : addr.toNat + 8 ≤ bctx.mem.size then LLVMConstantProperties.codec.readProperty addr bctx h else none
    | .cond_br =>
      if h : addr.toNat + 8 ≤ bctx.mem.size then CondBrProperties.codec.readProperty addr bctx h else none
    | .alloca =>
      if h : addr.toNat + 8 ≤ bctx.mem.size then AllocaProperties.codec.readProperty addr bctx h else none
    | .load =>
      if h : addr.toNat + 8 ≤ bctx.mem.size then LoadProperties.codec.readProperty addr bctx h else none
    | .store =>
      if h : addr.toNat + 8 ≤ bctx.mem.size then StoreProperties.codec.readProperty addr bctx h else none
    | .getelementptr =>
      if h : addr.toNat + 8 ≤ bctx.mem.size then GetelementptrProperties.codec.readProperty addr bctx h else none
    | .func =>
      if h : addr.toNat + 8 ≤ bctx.mem.size then LLVMFuncProperties.codec.readProperty addr bctx h else none
    | .module_flags =>
      if h : addr.toNat + 8 ≤ bctx.mem.size then LLVMModuleFlagsProperties.codec.readProperty addr bctx h else none
    -- the remaining ops have `Unit` properties: nothing to read
    | .and | .xor | .srem | .urem | .select | .sext | .br | .unreachable | .«return» => some ()
  read_after_write {op addr p bctx h hattrs} := by
    cases op <;>
      first
        | exact NswNuwProperties.read_after_write_dite p addr bctx h
        | exact ExactProperties.read_after_write_dite p addr bctx h
        | exact DisjointProperties.read_after_write_dite p addr bctx h
        | exact NnegProperties.read_after_write_dite p addr bctx h
        | exact IcmpProperties.read_after_write_dite p addr bctx h
        | exact FastMathFlagsProperties.read_after_write_dite p addr bctx h
        | exact AttrCodec.read_after_write_dite _ p addr bctx h hattrs
        | rfl
  only_adds_attributes {a op p addr bctx h hattrs} i hsome := by
    cases op <;>
      first
        | exact AttrCodec.writeProperty_attributes _ p addr bctx h hattrs hsome
        | simpa using hsome
        | exact hsome
  preserves_size {op p addr bctx h hattrs} := by
    cases op <;> first | simp | rfl
  only_modifies_properties {op p addr bctx h hattrs w n len} hd := by
    cases op <;>
      first
        | exact AttrCodec.writeProperty_read_disjoint _ p addr n len bctx h hattrs hd
        | exact NswNuwProperties.writeProperty_read_disjoint p addr n len bctx h hd
        | exact ExactProperties.writeProperty_read_disjoint p addr n len bctx h hd
        | exact DisjointProperties.writeProperty_read_disjoint p addr n len bctx h hd
        | exact NnegProperties.writeProperty_read_disjoint p addr n len bctx h hd
        | exact IcmpProperties.writeProperty_read_disjoint p addr n len bctx h hd
        | exact FastMathFlagsProperties.writeProperty_read_disjoint p addr n len bctx h hd
        | rfl
  readPropertyAt_frame {op addr bctx bctx' p} hp hsz hmem hattrs := by
    cases op <;>
      first
        | exact hp
        | exact Buffed.dite_read_frame hp hsz fun h h' hr =>
            (NswNuwProperties.readProperty_frame h h' (hmem 8 addr 1 (Nat.le_refl _) (Nat.le_refl _))).trans hr
        | exact Buffed.dite_read_frame hp hsz fun h h' hr =>
            (ExactProperties.readProperty_frame h h' (hmem 8 addr 1 (Nat.le_refl _) (Nat.le_refl _))).trans hr
        | exact Buffed.dite_read_frame hp hsz fun h h' hr =>
            (DisjointProperties.readProperty_frame h h' (hmem 8 addr 1 (Nat.le_refl _) (Nat.le_refl _))).trans hr
        | exact Buffed.dite_read_frame hp hsz fun h h' hr =>
            (NnegProperties.readProperty_frame h h' (hmem 8 addr 1 (Nat.le_refl _) (Nat.le_refl _))).trans hr
        | exact Buffed.dite_read_frame hp hsz fun h h' hr =>
            (IcmpProperties.readProperty_frame h h' (hmem 8 addr 1 (Nat.le_refl _) (Nat.le_refl _))).trans hr
        | exact Buffed.dite_read_frame hp hsz fun h h' hr =>
            (FastMathFlagsProperties.readProperty_frame h h' (hmem 8 addr 1 (Nat.le_refl _) (Nat.le_refl _))).trans hr
        | exact Buffed.dite_read_frame hp hsz fun h h' hr =>
            AttrCodec.readProperty_frame _ h h' hr
              (by rw [ExArray.read64!_eq_read!, ExArray.read64!_eq_read!, hmem 64 addr 8 (Nat.le_refl _) (Nat.le_refl _)])
              hattrs

end

end Veir
