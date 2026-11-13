module

public import Veir.Interpreter.Lemmas
public import Veir.Verifier
import all Veir.Verifier.Basic
import all Veir.Verifier.Lemmas
import all Veir.Verifier
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Memory
import all Veir.IR.Basic
import all Veir.IR.OpCode
import Veir.ForLean

public section

/-!
# The results of LLVM operations conform to their types

A verified LLVM operation with operands that conform to their types returns, if its interpretation
succeeds, results that conform to its result types (`OpCode.resultsConform`). An operation either
computes its results from its operands, whose types the verifier makes match its result types, or
builds its results from its result types.
-/

namespace Veir

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

/-! ## Conformance -/

/-- Whether a value conforms to a type depends only on the attribute of the type. -/
private theorem conforms_of_val_eq {v : RuntimeValue} {ty ty' : TypeAttr} (h : ty.val = ty'.val)
    (hv : v.Conforms ty) : v.Conforms ty' := by
  obtain ⟨a, _⟩ := ty; obtain ⟨b, _⟩ := ty'; cases h; exact hv

/-- A single result conforms to the result types of an operation with a single result. -/
private theorem results_one {v : RuntimeValue} (hn' : op.getNumResults! ctx.raw = 1)
    (hv : v.Conforms ((op.getResult 0).getType! ctx.raw)) :
    RuntimeValue.ArrayConforms #[v] (op.getResultTypes! ctx.raw) := by
  refine ⟨by simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hn'], fun i hi => ?_⟩
  obtain rfl : i = 0 := by simp at hi; omega
  rw [OperationPtr.getResultTypes!.getElem!_eq (by omega)]
  simpa using hv

/-- No results conform to the result types of an operation without results. -/
private theorem results_zero (hn' : op.getNumResults! ctx.raw = 0) :
    RuntimeValue.ArrayConforms #[] (op.getResultTypes! ctx.raw) :=
  ⟨by simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hn'], by simp⟩

private theorem operand_conforms {operands : Array RuntimeValue}
    (h : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw)) {i : Nat}
    (hi : i < operands.size) :
    operands[i]!.Conforms ((op.getOperand! ctx.raw i).getType! ctx.raw) := by
  have := h.2 i hi
  rwa [OperationPtr.getOperandTypes!.getElem!_eq (by
    rw [← OperationPtr.getOperandTypes!.size_eq_getNumOperands!, ← h.1]; exact hi)] at this

/-- The width alone decides whether an integer conforms. -/
private theorem int_conforms {w : Nat} {x y : Data.LLVM.Int w} {ty : TypeAttr}
    (h : (RuntimeValue.int w x).Conforms ty) : (RuntimeValue.int w y).Conforms ty := by
  obtain ⟨a, _⟩ := ty; cases a <;> exact h

private theorem byte_conforms {w : Nat} {x y : Data.LLVM.Byte w} {ty : TypeAttr}
    (h : (RuntimeValue.byte w x).Conforms ty) : (RuntimeValue.byte w y).Conforms ty := by
  obtain ⟨a, _⟩ := ty; cases a <;> exact h

private theorem addr_conforms {x y : Data.LLVM.Ptr} {ty : TypeAttr}
    (h : (RuntimeValue.addr x).Conforms ty) : (RuntimeValue.addr y).Conforms ty := by
  obtain ⟨a, _⟩ := ty; cases a <;> exact h

private theorem int_conforms_of_val {w : Nat} {x : Data.LLVM.Int w} {ty : TypeAttr}
    {it : IntegerType} (h : ty.val = .integerType it) (hw : it.bitwidth = w) :
    (RuntimeValue.int w x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; exact hw

private theorem byte_conforms_of_val {w : Nat} {x : Data.LLVM.Byte w} {ty : TypeAttr}
    {bt : LLVM.ByteType} (h : ty.val = .byteType bt) (hw : bt.bitwidth = w) :
    (RuntimeValue.byte w x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; exact hw

private theorem addr_conforms_of_val {x : Data.LLVM.Ptr} {ty : TypeAttr}
    (h : ∃ p, ty.val = .llvmPointerType p) : (RuntimeValue.addr x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; obtain ⟨p, h⟩ := h; simp only at h; subst h; trivial

private theorem float_conforms_of_val {ft : FloatType} {x : Data.Float.FloatValue ft.format}
    {ty : TypeAttr} (h : ty.val = .floatType ft) : (RuntimeValue.float ft x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; rfl

/-- A single result conforms to result types that are a single type it conforms to. -/
private theorem results_toList {v : RuntimeValue} {R : Array TypeAttr} {t : TypeAttr}
    (ht : R.toList = [t]) (hv : v.Conforms t) : RuntimeValue.ArrayConforms #[v] R := by
  obtain rfl : R = #[t] := List.eq_toArray_iff.mpr ht
  refine ⟨rfl, fun i hi => ?_⟩
  obtain rfl : i = 0 := by simp at hi; omega
  simpa using hv

private theorem results_getElem? {v : RuntimeValue} {t : TypeAttr}
    (hn : op.getNumResults! ctx.raw = 1) (ht : (op.getResultTypes! ctx.raw)[0]? = some t)
    (hv : v.Conforms t) :
    RuntimeValue.ArrayConforms #[v] (op.getResultTypes! ctx.raw) := by
  have hs : (op.getResultTypes! ctx.raw).size = 1 := by
    simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hn]
  have : (op.getResultTypes! ctx.raw).toList = [t] := by
    rw [Array.getElem?_eq_some_iff] at ht
    obtain ⟨_, ht⟩ := ht
    apply List.ext_getElem <;> simp_all
  exact results_toList this hv

/-! ## Interpretation -/

private theorem Interp.exists_of_bind_eq_ok {α β : Type} {x : Interp α} {f : α → Interp β}
    {b : β} (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp_all

/-- An invariant of every step of a loop holds after the loop. -/
private theorem Interp.forIn_list_inv {α β : Type} (l : List α) (P : β → Prop)
    {f : α → β → Interp (ForInStep β)} (hf : ∀ a b s, P b → f a b = .ok s → P s.value)
    {init r : β} (hi : P init) (h : forIn l init f = .ok r) : P r := by
  induction l generalizing init with
  | nil => simp at h; exact h ▸ hi
  | cons a l ih =>
    simp only [List.forIn_cons] at h
    rcases hfa : f a init with _ | _ | (b | b) <;> rw [hfa] at h
    · simp at h
    · simp at h
    · simp at h; exact h ▸ hf a init _ hi hfa
    · exact ih (hf a init _ hi hfa) h

private theorem Interp.forIn_range_inv {β : Type} (r : Std.Legacy.Range) (P : β → Prop)
    {f : Nat → β → Interp (ForInStep β)} (hf : ∀ a b s, P b → f a b = .ok s → P s.value)
    {init s : β} (hi : P init) (h : forIn r init f = .ok s) : P s := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact Interp.forIn_list_inv _ P hf hi h

/-- A load returns a value of the type it loads. -/
private theorem llvmLoad_conforms {mem : MemoryState} {p : Data.Pointer} {t : TypeAttr}
    {v : RuntimeValue} (h : mem.llvmLoad p t = .ok v) : v.Conforms t := by
  simp only [MemoryState.llvmLoad] at h
  split at h
  · simp at h
  split at h <;>
    (repeat' (first
      | (obtain ⟨_, -, h⟩ := Interp.exists_of_bind_eq_ok h)
      | split at h)) <;>
    (try simp only [Interp.pure_eq, Interp.ok.injEq] at h) <;> (try subst h) <;>
    first
      | (simp at h; done)
      | exact int_conforms_of_val ‹_› rfl
      | exact byte_conforms_of_val ‹_› rfl
      | exact addr_conforms_of_val ⟨_, ‹_›⟩

/-- A bitcast returns a value of the type it casts to. -/
private theorem bitcastValue_conforms {mem : MemoryState} {val r : RuntimeValue}
    {type : Attribute} (hp : type.isType) (h : Llvm.bitcastValue mem val type = .ok r) :
    r.Conforms ⟨type, hp⟩ := by
  simp only [Llvm.bitcastValue] at h
  split at h <;> (try split at h) <;>
    first
      | (simp at h; done)
      | (simp only [Interp.ok.injEq] at h; subst h
         simp_all [RuntimeValue.Conforms])

/-- The properties of an LLVM operation, as an opcode and as an LLVM opcode. -/
private theorem getProperties!_llvm {op : OperationPtr} {ctx : IRContext OpCode} (o : Llvm) :
    HEq (op.getProperties! ctx (OpCode.llvm o)) (op.getProperties! ctx o) := by
  simp only [OperationPtr.getProperties!]
  generalize op.get! ctx = x
  obtain ⟨⟩ := x
  split <;> split
  · rename_i h1 h2
    simp only at h1 h2
    subst h1
    rfl
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · rfl

/-! ## Verifier -/

/-- The first check of a successful sequence of checks succeeds. -/
private theorem bind_ok_left {ε α : Type} {x : Except ε PUnit} {f : PUnit → Except ε α}
    {a : α} (h : (x >>= f) = .ok a) : x = .ok () := by
  cases x with
  | ok u => rfl
  | error e => simp [bind, Except.bind] at h

private theorem llvmVerified {opT : Llvm} (hType : op.getOpType! ctx.raw = .llvm opT)
    (hV : op.Verified ctx opIn) : Llvm.verifyLocalInvariants opT op ctx opIn = .ok () := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, hType] at hV
  exact hV

private theorem verifyNonOperandCounts_ok {r g s : Nat}
    (h : op.verifyNonOperandCounts ctx opIn r g s = .ok ()) : op.getNumResults! ctx.raw = r := by
  rw [OperationPtr.getNumResults!_eq_getNumResults opIn]
  simp only [OperationPtr.verifyNonOperandCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hne; simpa using hne

private theorem verifyOpCounts_ok {o r g s : Nat}
    (h : op.verifyOpCounts ctx opIn o r g s = .ok ()) : op.getNumResults! ctx.raw = r := by
  simp only [OperationPtr.verifyOpCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · exact verifyNonOperandCounts_ok h

private theorem verifyPlainOpCounts_ok {o r : Nat}
    (h : op.verifyPlainOpCounts ctx opIn o r = .ok ()) : op.getNumResults! ctx.raw = r :=
  verifyOpCounts_ok h

private theorem verifyTerminatorCounts_ok {s : Nat}
    (h : op.verifyTerminatorCounts ctx opIn s = .ok ()) : op.getNumResults! ctx.raw = 0 :=
  verifyNonOperandCounts_ok h

private theorem verifyLlvmPointerType_ok {ty : TypeAttr} {msg : String}
    (h : ty.verifyLlvmPointerType msg = .ok ()) : ∃ p, ty.val = .llvmPointerType p := by
  simp only [TypeAttr.verifyLlvmPointerType] at h
  split at h
  · exact ⟨_, by assumption⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem ite_throw_ok {ε : Type} {c : Prop} [Decidable c] {e : ε}
    (h : (if c then throw e else pure () : Except ε PUnit) = .ok ()) : ¬c := by
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · assumption

private theorem verifyResultTypeMatches_ok {ty : TypeAttr} {msg : String}
    (h : op.verifyResultTypeMatches ctx ty msg = .ok ()) :
    ((op.getResult 0).getType! ctx.raw).val = ty.val := by
  simp only [OperationPtr.verifyResultTypeMatches] at h
  exact Classical.byContradiction fun hne => ite_throw_ok h hne

/-!
## The opcodes

Each tactic below peels the interpretation of an opcode down to the results it returns.
-/

private theorem single_of_ok {v : RuntimeValue} {m m' : MemoryState}
    {a a' : Option ControlFlowAction}
    (h : (Interp.ok (#[v], m, a) : Interp _) = .ok (vals, m', a')) : vals = #[v] := by
  simp at h; exact h.1.symm

private theorem empty_of_ok {m m' : MemoryState} {a a' : Option ControlFlowAction}
    (h : (Interp.ok (#[], m, a) : Interp _) = .ok (vals, m', a')) : vals = #[] := by
  simp only [Interp.ok.injEq, Prod.mk.injEq] at h; exact h.1.symm

set_option hygiene false in
local macro "rc_peel" : tactic => `(tactic| (
  simp only [Llvm.interpretOp'] at h
  repeat' (first
    | (obtain ⟨_, -, h⟩ := Interp.exists_of_bind_eq_ok h)
    | split at h)
  all_goals try (simp at h; done)))

set_option hygiene false in
local macro "rc_empty" : tactic => `(tactic| (
  rc_peel
  all_goals (obtain rfl := empty_of_ok h; exact results_zero hR)))

set_option hygiene false in
local macro "rc_binop" lem:term : tactic => `(tactic| (
  have hB := $lem hV hType
  unfold OperationPtr.IsVerifiedIntegerBinop at hB
  obtain ⟨hR, -, -, -, it, hRt, hO0, -⟩ := hB
  simp only [Llvm.interpretOp'] at h
  split at h
  · next bw lhs bw' rhs hOps =>
    obtain rfl : operands = #[.int bw lhs, .int bw' rhs] := List.eq_toArray_iff.mpr hOps
    have h0 := operand_conforms hConf (i := 0) (by simp)
    rw [hO0] at h0
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (obtain rfl := single_of_ok h
         exact results_one hR (by rw [hRt]; exact int_conforms (by simpa using h0)))
  · simp at h))

set_option hygiene false in
local macro "rc_unop" lem:term : tactic => `(tactic| (
  have hB := $lem hV hType
  unfold OperationPtr.IsVerifiedIntegerUnop at hB
  obtain ⟨hR, -, -, -, hRO, -⟩ := hB
  simp only [Llvm.interpretOp'] at h
  split at h
  · next bw x hOps =>
    obtain rfl : operands = #[.int bw x] := List.eq_toArray_iff.mpr hOps
    have h0 := operand_conforms hConf (i := 0) (by simp)
    obtain rfl := single_of_ok h
    exact results_one hR (by rw [hRO]; exact int_conforms (by simpa using h0))
  · simp at h))

set_option hygiene false in
local macro "rc_ternop" lem:term : tactic => `(tactic| (
  have hB := $lem hV hType
  unfold OperationPtr.IsVerifiedIntegerTernop at hB
  obtain ⟨hR, -, -, -, it, hRt, hO0, -⟩ := hB
  simp only [Llvm.interpretOp'] at h
  split at h
  · next bw a bw' b bw'' c hOps =>
    obtain rfl : operands = #[.int bw a, .int bw' b, .int bw'' c] := List.eq_toArray_iff.mpr hOps
    have h0 := operand_conforms hConf (i := 0) (by simp)
    rw [hO0] at h0
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (obtain rfl := single_of_ok h
         exact results_one hR (by rw [hRt]; exact int_conforms (by simpa using h0)))
  · simp at h))

set_option hygiene false in
local macro "rc_shift" lem:term : tactic => `(tactic| (
  have hB := $lem hV hType
  unfold OperationPtr.IsVerifiedLLVMShift at hB
  obtain ⟨hR, -, hRO, -⟩ := hB
  simp only [Llvm.interpretOp'] at h
  split at h
  · next lhs bw' rhs hOps =>
    obtain rfl : operands = #[lhs, .int bw' rhs] := List.eq_toArray_iff.mpr hOps
    have h0 := operand_conforms hConf (i := 0) (by simp)
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_cons_zero, Option.getD_some] at h0
    replace h0 := conforms_of_val_eq hRO.symm h0
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (obtain rfl := single_of_ok h
         first
           | exact results_one hR (int_conforms h0)
           | exact results_one hR (byte_conforms h0))
  · simp at h))

/--
A verified LLVM operation with operands that conform to their types returns, if its
interpretation succeeds, results that conform to its result types.
-/
theorem Llvm.interpretOp'_results_conform (opT : Llvm)
    (hType : op.getOpType! ctx.raw = .llvm opT) (hV : op.Verified ctx opIn)
    (hConf : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : Llvm.interpretOp' opT (op.getProperties! ctx.raw (OpCode.llvm opT))
      (op.getResultTypes! ctx.raw) operands bs mem layout = .ok (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  cases opT
  case add => rc_binop OperationPtr.Verified.llvm_add
  case sub => rc_binop OperationPtr.Verified.llvm_sub
  case mul => rc_binop OperationPtr.Verified.llvm_mul
  case sdiv => rc_binop OperationPtr.Verified.llvm_sdiv
  case udiv => rc_binop OperationPtr.Verified.llvm_udiv
  case srem => rc_binop OperationPtr.Verified.llvm_srem
  case urem => rc_binop OperationPtr.Verified.llvm_urem
  case ashr => rc_binop OperationPtr.Verified.llvm_ashr
  case and => rc_binop OperationPtr.Verified.llvm_and
  case or => rc_binop OperationPtr.Verified.llvm_or
  case xor => rc_binop OperationPtr.Verified.llvm_xor
  case intr__smax => rc_binop OperationPtr.Verified.llvm_intr__smax
  case intr__smin => rc_binop OperationPtr.Verified.llvm_intr__smin
  case intr__umax => rc_binop OperationPtr.Verified.llvm_intr__umax
  case intr__umin => rc_binop OperationPtr.Verified.llvm_intr__umin
  case intr__sadd__sat => rc_binop OperationPtr.Verified.llvm_intr__sadd__sat
  case intr__uadd__sat => rc_binop OperationPtr.Verified.llvm_intr__uadd__sat
  case intr__ssub__sat => rc_binop OperationPtr.Verified.llvm_intr__ssub__sat
  case intr__usub__sat => rc_binop OperationPtr.Verified.llvm_intr__usub__sat
  case intr__sshl__sat => rc_binop OperationPtr.Verified.llvm_intr__sshl__sat
  case intr__ushl__sat => rc_binop OperationPtr.Verified.llvm_intr__ushl__sat
  case intr__ctlz => rc_unop OperationPtr.Verified.llvm_intr__ctlz
  case intr__cttz => rc_unop OperationPtr.Verified.llvm_intr__cttz
  case intr__ctpop => rc_unop OperationPtr.Verified.llvm_intr__ctpop
  case intr__bswap => rc_unop OperationPtr.Verified.llvm_intr__bswap
  case intr__bitreverse => rc_unop OperationPtr.Verified.llvm_intr__bitreverse
  case intr__abs => rc_unop OperationPtr.Verified.llvm_intr__abs
  case intr__fshl => rc_ternop OperationPtr.Verified.llvm_intr__fshl
  case intr__fshr => rc_ternop OperationPtr.Verified.llvm_intr__fshr
  case shl => rc_shift OperationPtr.Verified.llvm_shl
  case lshr => rc_shift OperationPtr.Verified.llvm_lshr
  case icmp =>
    have hB := hV.llvm_icmp hType
    unfold OperationPtr.IsVerifiedIcmp at hB
    obtain ⟨hR, -, -, -, ⟨it, hRt, hbw⟩, -⟩ := hB
    simp only [Llvm.interpretOp'] at h
    split at h
    · split at h
      · simp at h
      · obtain rfl := single_of_ok h
        exact results_one hR (int_conforms_of_val (by simpa using hRt) hbw)
    · simp at h
  case select =>
    have hB := hV.llvm_select hType
    unfold OperationPtr.IsVerifiedSelect at hB
    obtain ⟨hR, -, -, hR1, -⟩ := hB
    simp only [Llvm.interpretOp'] at h
    split at h
    · next cond bw lhs bw' rhs hOps =>
      obtain rfl : operands = #[.int 1 cond, .int bw lhs, .int bw' rhs] :=
        List.eq_toArray_iff.mpr hOps
      have h1 := operand_conforms hConf (i := 1) (by simp)
      split at h
      · simp at h
      · obtain rfl := single_of_ok h
        exact results_one hR (conforms_of_val_eq hR1.symm (int_conforms (by simpa using h1)))
    · simp at h
  case load =>
    simp only [Llvm.interpretOp'] at h
    repeat' split at h
    all_goals try (simp at h; done)
    next hR =>
    obtain ⟨_, -, h⟩ := Interp.exists_of_bind_eq_ok h
    obtain ⟨v, hv, h⟩ := Interp.exists_of_bind_eq_ok h
    obtain rfl := single_of_ok h
    exact results_toList hR (llvmLoad_conforms hv)
  case store | intr__memset | intr__memcpy | intr__memmove =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hR := verifyPlainOpCounts_ok (bind_ok_left (Except.ok_of_bind_ok hV'))
    rc_empty
  case «return» | cond_br =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hR := verifyTerminatorCounts_ok (bind_ok_left (Except.ok_of_bind_ok hV'))
    rc_empty
  case br =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hV'' := Except.ok_of_bind_ok hV'
    simp only [OperationPtr.verifyUnconditionalBranch] at hV''
    have hR := verifyTerminatorCounts_ok (bind_ok_left hV'')
    rc_empty
  case switch =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hR := verifyTerminatorCounts_ok (bind_ok_left (Except.ok_of_bind_ok hV'))
    simp only [Llvm.interpretOp'] at h
    repeat' split at h
    all_goals try (simp at h; done)
    obtain ⟨s, hs, h⟩ := Interp.exists_of_bind_eq_ok h
    have hP := Interp.forIn_range_inv _
      (fun (b : Option (Array RuntimeValue × MemoryState × Option ControlFlowAction) × Nat) =>
        ∀ r, b.1 = some r → r.1 = #[])
      (fun i b s hb hstep => by
        repeat' split at hstep
        all_goals first
          | (simp at hstep; done)
          | (simp only [Interp.pure_eq, Interp.ok.injEq] at hstep; subst hstep; simp; done)
          | (simp only [Interp.pure_eq, Interp.ok.injEq] at hstep; subst hstep; simpa using hb))
      (by simp) hs
    split at h
    · rename_i r hr
      simp only [Interp.pure_eq, Interp.ok.injEq] at h
      subst h
      have h1 := hP _ hr
      simp only at h1
      subst h1; exact results_zero hR
    · obtain rfl := empty_of_ok h; exact results_zero hR
  case unreachable =>
    simp only [Llvm.interpretOp'] at h; simp at h
  case mlir__addressof =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hR := verifyPlainOpCounts_ok (bind_ok_left hV')
    have hP := Except.ok_of_bind_ok hV'
    split at hP
    · next heq =>
      rc_peel
      all_goals
        (obtain rfl := single_of_ok h; exact results_one hR (addr_conforms_of_val ⟨_, heq⟩))
    · simp [throw, throwThe, MonadExceptOf.throw] at hP
  case alloca =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hV1 := Except.ok_of_bind_ok hV'
    have hR := verifyPlainOpCounts_ok (bind_ok_left hV1)
    have hP := verifyLlvmPointerType_ok (bind_ok_left (Except.ok_of_bind_ok hV1))
    rc_peel
    all_goals (obtain rfl := single_of_ok h; exact results_one hR (addr_conforms_of_val hP))
  case getelementptr =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hV1 := Except.ok_of_bind_ok hV'
    split at hV1
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hV1
    split at hV1
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hV1
    rename_i hne
    have hR : op.getNumResults! ctx.raw = 1 := by
      rw [OperationPtr.getNumResults!_eq_getNumResults opIn]
      exact Classical.byContradiction hne
    split at hV1
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hV1
    split at hV1
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hV1
    /- The operand and index checks come before the one on the result. -/
    have hP := verifyLlvmPointerType_ok
      (bind_ok_left (Except.ok_of_bind_ok (Except.ok_of_bind_ok hV1)))
    rc_peel
    all_goals (obtain rfl := single_of_ok h; exact results_one hR (addr_conforms_of_val hP))
  case freeze =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hV1 := Except.ok_of_bind_ok hV'
    have hR := verifyPlainOpCounts_ok (bind_ok_left hV1)
    have hM := verifyResultTypeMatches_ok (bind_ok_left (Except.ok_of_bind_ok hV1))
    simp only [Llvm.interpretOp'] at h
    split at h
    · next val hOps =>
      obtain rfl : operands = #[val] := List.eq_toArray_iff.mpr hOps
      have h0 := conforms_of_val_eq hM.symm (operand_conforms hConf (i := 0) (by simp))
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_cons_zero, Option.getD_some] at h0
      repeat' split at h
      all_goals first
        | (simp at h; done)
        | (obtain rfl := single_of_ok h
           first
             | exact results_one hR (int_conforms h0)
             | exact results_one hR (byte_conforms h0)
             | exact results_one hR (addr_conforms h0))
    · simp at h
  case bitcast =>
    simp only [Llvm.interpretOp'] at h
    repeat' split at h
    all_goals try (simp at h; done)
    next hR =>
    obtain ⟨r, hr, h⟩ := Interp.exists_of_bind_eq_ok h
    obtain rfl := single_of_ok h
    exact results_toList hR (bitcastValue_conforms _ hr)
  case inttoptr | ptrtoint =>
    rc_peel
    all_goals (obtain rfl := single_of_ok h
               first
                 | exact results_toList ‹_› (addr_conforms_of_val ⟨_, ‹_›⟩)
                 | exact results_toList ‹_› (int_conforms_of_val ‹_› ‹_›))
  case sext | zext =>
    have hB : OperationPtr.IsVerifiedIntegerExtop op ctx := by
      first | exact hV.llvm_sext hType | exact hV.llvm_zext hType
    unfold OperationPtr.IsVerifiedIntegerExtop at hB
    obtain ⟨hR, -⟩ := hB
    rc_peel
    all_goals (obtain rfl := single_of_ok h
               exact results_getElem? hR ‹_› (int_conforms_of_val ‹_› rfl))
  case trunc =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hT := bind_ok_left (Except.ok_of_bind_ok hV')
    simp only [OperationPtr.verifyTruncTypes] at hT
    have hR := verifyPlainOpCounts_ok (bind_ok_left hT)
    rc_peel
    all_goals (obtain rfl := single_of_ok h
               first
                 | exact results_getElem? hR ‹_› (int_conforms_of_val ‹_› rfl)
                 | exact results_getElem? hR ‹_› (byte_conforms_of_val ‹_› rfl))
  case mlir__poison | mlir__zero =>
    have hV' := llvmVerified hType hV
    simp only [Llvm.verifyLocalInvariants] at hV'
    have hR := verifyPlainOpCounts_ok (bind_ok_left (Except.ok_of_bind_ok hV'))
    rc_peel
    all_goals (obtain rfl := single_of_ok h
               first
                 | exact results_getElem? hR ‹_› (int_conforms_of_val ‹_› rfl)
                 | exact results_getElem? hR ‹_› (byte_conforms_of_val ‹_› rfl)
                 | exact results_getElem? hR ‹_› (addr_conforms_of_val ⟨_, ‹_›⟩))
  case mlir__constant =>
    obtain ⟨hR, -⟩ := hV.llvm_mlir__constant hType
    rc_peel
    all_goals (obtain rfl := single_of_ok h)
    · exact results_getElem? hR ‹_› (int_conforms_of_val ‹_› rfl)
    · rename_i resType hRes _ fa hProp _ bw hBw
      have hR0 : (op.getResultTypes! ctx.raw)[0]! = resType := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hRes, Option.getD_some]
      rw [OperationPtr.getResultTypes!.getElem!_eq (by omega)] at hR0
      have hProp' : (op.getProperties! ctx.raw Llvm.mlir__constant).value = .float fa := by
        rw [← eq_of_heq (getProperties!_llvm (ctx := ctx.raw) (op := op) .mlir__constant)]
        exact hProp
      have hV' := llvmVerified hType hV
      simp only [Llvm.verifyLocalInvariants] at hV'
      have hV1 := Except.ok_of_bind_ok (Except.ok_of_bind_ok hV')
      simp only [hProp', hR0, hBw] at hV1
      split at hV1
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hV1
      · have hEq : bw = fa.type := Classical.byContradiction (ite_throw_ok hV1)
        exact results_getElem? hR hRes (float_conforms_of_val (hEq ▸ hBw))
  all_goals (simp only [Llvm.interpretOp'] at h; simp at h)

/-- The results of every LLVM opcode conform to their types. -/
theorem OpCode.resultsConform_llvm (opT : Llvm) : OpCode.resultsConform (.llvm opT) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType hV operands vals mem mem' act hConf h => ?_
  have hType! : op.getOpType! ctx.raw = .llvm opT := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  simp only [OperationPtr.interpret] at h
  rw [hType!] at h
  exact Llvm.interpretOp'_results_conform opT hType! hV hConf h

/--
info: 'Veir.OpCode.resultsConform_llvm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OpCode.resultsConform_llvm

instance (op : Llvm) : ResultsConform (.llvm op) :=
  ⟨OpCode.resultsConform_llvm op⟩

end Veir

end
