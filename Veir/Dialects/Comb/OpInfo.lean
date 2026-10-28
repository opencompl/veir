module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Comb.Properties
public import Veir.Dialects.HW.OpInfo
public import Veir.ConstantMaterialization
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode
import Veir.Data.Comb.Basic

namespace Veir

public section

@[opcodes]
inductive Comb where
| add
| and
| concat
| divs
| divu
| extract
| icmp
| mods
| modu
| mul
| mux
| or
| parity
| replicate
| reverse
| shl
| shrs
| shru
| sub
| xor
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Comb.propertiesOf (op : Comb) : Type :=
match op with
| .extract => CombExtractProperties
| .icmp => CombIcmpProperties
| _ => Unit

def Comb.fromAttrDict
    (op : Comb) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Comb.propertiesOf op) := by
  cases op
  case extract => exact CombExtractProperties.fromAttrDict attrDict
  case icmp => exact CombIcmpProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Comb.toAttrDict
    (op : Comb) (props : Comb.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .extract =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "lowBit".toUTF8 (Attribute.integerAttr props.lowBit)
  | .icmp =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr props.predicate)
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Comb.getEffects
    (_op : Comb) (_props : Comb.propertiesOf _op) : MemoryEffects :=
  .none

def Comb.isConstantLike (_op : Comb) : Bool :=
  false

def Comb.hasSSADominance (_op : Comb) (_index : Nat) : Bool :=
  true

#generate_dialect Comb

instance : IsOpCode Comb where
  fromName := Comb.fromName
  name := Comb.name
  propertiesOf := Comb.propertiesOf
  fromAttrDict := Comb.fromAttrDict
  toAttrDict := Comb.toAttrDict

/-- CIRCT combinational folds use the HW dialect's integer constant. -/
def Comb.materializeConstant {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo HW]
    (_op : Comb) (value : RuntimeValue) (type : TypeAttr) : Option (Materialized OpInfo) :=
  match value, type.val with
  | .int bw (.val value), .integerType intType =>
    if bw = intType.bitwidth then
      some (.of HW.constant (HWConstantProperties.mk (IntegerAttr.ofInt value.toInt intType)))
    else none
  | _, _ => none

/--
Verify the local invariants of a `comb` operation in any operation-info type
containing the `comb` dialect.
-/
def Comb.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Comb] (opType : Comb) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .add | .and | .mul | .or | .xor => do
    if op.getNumOperands ctx.raw opIn < 1 then
      throw "Expected 1 or more operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .concat => do
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .divs | .divu | .icmp | .mods | .modu | .shl | .shrs | .shru | .sub => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .extract | .parity | .replicate | .reverse => do
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()
  | .mux => do
    op.verifyPlainOpCounts ctx opIn 3 1
    pure ()

/-- Every operand as an `LLVM.Int` at one common width, or `none` if they disagree or if any is
not an integer. The shape every width-preserving `comb` operation needs. -/
private def Comb.sameWidthOperands (operands : Array RuntimeValue) :
    Option ((w : Nat) × List (Data.LLVM.Int w)) := do
  let l : List _ := operands.toList
  -- `operands[0]?` rather than `l[0]!`: a variadic `comb` operation with no operands is
  -- malformed, and must be refused rather than panic.
  let some (first : RuntimeValue) := operands[0]? | none
  let .int w _ := first | none
  let some nl := l.mapM (
      fun e => do
        let .int w' val := e | none
        if h : w' ≠ w then none else
        return val.cast (by simpa using h)) | none
  return ⟨w, nl⟩

/-- The bit width of the operation's first result, for the operations whose result width is not
determined by their operands. -/
private def Comb.resultWidth (resultTypes : Array TypeAttr) : Option Nat := do
  let resType ← resultTypes[0]?
  let .integerType bw := resType.val | none
  return bw.bitwidth

/-- Interpret one `comb` operation.

`resultTypes` is needed because `extract` does not determine its result width from its operands;
everything else either preserves the operand width, sums it, or produces an `i1`. -/
def Comb.interpretOp' (opType : Veir.Comb) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .add => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
               return (#[.int w (Veir.Data.Comb.add l)], none)
  | .mul => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
               return (#[.int w (Veir.Data.Comb.mul l)], none)
  | .and => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
               return (#[.int w (Veir.Data.Comb.and l)], none)
  | .or => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
              return (#[.int w (Veir.Data.Comb.or l)], none)
  | .xor => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
               return (#[.int w (Veir.Data.Comb.xor l)], none)
  -- Binary and width preserving.
  | .sub => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
               let [x, y] := l | none
               return (#[.int w (Veir.Data.Comb.sub x y)], none)
  | .shl => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
               let [x, y] := l | none
               return (#[.int w (Veir.Data.Comb.shl x y)], none)
  | .shru => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
                let [x, y] := l | none
                return (#[.int w (Veir.Data.Comb.shru x y)], none)
  | .shrs => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
                let [x, y] := l | none
                return (#[.int w (Veir.Data.Comb.shrs x y)], none)
  -- Comparison, producing an `i1`. The predicate is an integer attribute, and
  -- `IntPred.fromNat` refuses one outside the table rather than defaulting.
  | .icmp => do
    let ⟨w, l⟩ ← Comb.sameWidthOperands operands
    let [x, y] := l | none
    let pred ← Data.LLVM.IntPred.fromNat properties.predicate.value.toNat
    return (#[.int 1 (Veir.Data.Comb.icmp (w := w) pred x y)], none)
  -- `mux` is not folded through `sameWidthOperands`: its condition is an `i1` while its arms are
  -- at the result width, so the operands are deliberately not all one width.
  | .mux => do
    let #[c, t, f] := operands | none
    let .int 1 c := c | none
    let .int w t := t | none
    let .int w' f := f | none
    if h : w' ≠ w then none else
    return (#[.int w (Veir.Data.Comb.mux c t (f.cast (by simpa using h)))], none)
  -- Width changing.
  | .concat => do
    -- Variadic and most significant first, so it folds from the left, growing the width.
    let mut acc : (w : Nat) × Data.LLVM.Int w := ⟨0, .val (BitVec.ofNat 0 0)⟩
    for operand in operands do
      let .int w v := operand | none
      acc := ⟨acc.1 + w, Veir.Data.Comb.concat acc.2 v⟩
    return (#[.int acc.1 acc.2], none)
  | .extract => do
    let n ← Comb.resultWidth resultTypes
    let #[x] := operands | none
    let .int w x := x | none
    return (#[.int n (Veir.Data.Comb.extract (w := w) n properties.lowBit.value.toNat x)], none)
  -- Bit manipulation. `parity` reduces to an `i1`; `replicate` takes its result width from the
  -- type, like `extract`.
  | .parity => do
    let ⟨_, l⟩ ← Comb.sameWidthOperands operands
    let [x] := l | none
    return (#[.int 1 (Veir.Data.Comb.parity x)], none)
  | .replicate => do
    let n ← Comb.resultWidth resultTypes
    let #[x] := operands | none
    let .int w x := x | none
    return (#[.int n (Veir.Data.Comb.replicate (w := w) n x)], none)
  | .reverse => do
    let ⟨w, l⟩ ← Comb.sameWidthOperands operands
    let [x] := l | none
    return (#[.int w (Veir.Data.Comb.reverse x)], none)
  -- Division and remainder. Poison on a zero divisor; see the note in `Veir.Data.Comb`.
  | .divu => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
                let [x, y] := l | none
                return (#[.int w (Veir.Data.Comb.divu x y)], none)
  | .divs => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
                let [x, y] := l | none
                return (#[.int w (Veir.Data.Comb.divs x y)], none)
  | .modu => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
                let [x, y] := l | none
                return (#[.int w (Veir.Data.Comb.modu x y)], none)
  | .mods => do let ⟨w, l⟩ ← Comb.sameWidthOperands operands
                let [x, y] := l | none
                return (#[.int w (Veir.Data.Comb.mods x y)], none)

instance : HasOpInfo Comb where
  verifyLocalInvariants := Comb.verifyLocalInvariants
  getEffects := Comb.getEffects
  isConstantLike := Comb.isConstantLike
  hasSSADominance := Comb.hasSSADominance

end

end Veir
