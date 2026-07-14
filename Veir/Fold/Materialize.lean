import Veir.Fold.Agree

/-!
  # Correctness of constant materialization

  Layer C of the folding soundness proofs (see `Veir.Fold.Semantics`):
  interpreting the operation built by `PatternRewriter.materializeConstant!`
  in any state succeeds, binds its single result to exactly the materialized
  runtime value, threads the memory through unchanged, and produces no control
  flow.

  The proof is layered: a generic core lemma (`interpretOp_createOp_constant`)
  handles any freshly created zero-operand, single-result operation whose
  dialect step is total and constant, and one small semantic lemma per
  constant kind discharges its hypothesis via the attribute round-trips
  (`BitVec.ofInt_toInt` and friends). The core lemma is stated against
  `WfRewriter.createOp` at an arbitrary insertion point so that it can also
  serve a detached-creation materializer (as `LocalRewritePattern`s use).

  The `mod_arith` materialization arm is excluded: the dialect is
  uninterpreted, and any lifting proof about a folded `mod_arith` operation is
  vacuous before materialization correctness is ever needed.
-/

namespace Veir

/--
  Invert a successful `WfRewriter.createOp!` at any insertion point: since
  every failing side condition panics, a `some` result recovers the side
  conditions together with the plain `createOp` equation. Generalizes
  `WfRewriter.createOp!_none_some` to inserted creations.
-/
theorem WfRewriter.createOp!_some_inv {OpInfo : Type} [HasOpInfo OpInfo]
    {wfCtx : WfIRContext OpInfo} {opType : OpInfo}
    {resultTypes operands blockOperands regions} {properties : HasOpInfo.propertiesOf opType}
    {ipOpt : Option InsertPoint} {ctx' : WfIRContext OpInfo} {newOp : OperationPtr}
    (h : WfRewriter.createOp! wfCtx opType resultTypes operands blockOperands regions properties
      ipOpt = some (ctx', newOp)) :
    ∃ (hoper : ∀ oper, oper ∈ operands → oper.InBounds wfCtx.raw)
      (hblock : ∀ oper, oper ∈ blockOperands → oper.InBounds wfCtx.raw)
      (hreg : ∀ reg, reg ∈ regions → reg.InBounds wfCtx.raw)
      (hins : ipOpt.maybe InsertPoint.InBounds wfCtx.raw),
      WfRewriter.createOp wfCtx opType resultTypes operands blockOperands regions properties
        ipOpt hoper hblock hreg hins = some (ctx', newOp) := by
  unfold WfRewriter.createOp! at h
  split at h
  case isTrue hoper =>
    split at h
    case isTrue hblock =>
      split at h
      case isTrue hreg =>
        split at h
        case h_1 =>
          exact ⟨hoper, hblock, hreg, by grind [Option.maybe], h⟩
        case h_2 ip =>
          split at h
          case isTrue hins =>
            cases hc : WfRewriter.createOp wfCtx opType resultTypes operands blockOperands
                regions properties (some ip) hoper hblock hreg with
            | none =>
              rw [hc] at h
              simp [panicWithPosWithDecl, panic, panicCore] at h
            | some result =>
              rw [hc] at h
              simp only at h
              exact ⟨hoper, hblock, hreg, by grind [Option.maybe], by rw [hc, h]⟩
          case isFalse =>
            simp [panicWithPosWithDecl, panic, panicCore] at h
      case isFalse => simp [panicWithPosWithDecl, panic, panicCore] at h
    case isFalse => simp [panicWithPosWithDecl, panic, panicCore] at h
  case isFalse => simp [panicWithPosWithDecl, panic, panicCore] at h

/--
  Interpreting a freshly created zero-operand, single-result operation whose
  dialect step is total and constant (`hSem`): in any state it succeeds, binds
  the result to `rv`, threads memory unchanged, and produces no control flow.
-/
theorem interpretOp_createOp_constant {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType : OpCode} {resType : TypeAttr} {properties : HasOpInfo.propertiesOf opType}
    {ipOpt : Option InsertPoint} {hoper hblock hreg hins} {rv : RuntimeValue}
    (hCreate : WfRewriter.createOp ctx opType #[resType] #[] #[] #[] properties ipOpt
      hoper hblock hreg hins = some (ctx', newOp))
    (hSem : ∀ mem, interpretOp' opType properties #[resType] #[] #[] mem
      = some (.ok (#[rv], mem, none)))
    (hConf : rv.Conforms resType)
    (state : InterpreterState ctx') :
    ∃ (hInB : newOp.InBounds ctx'.raw) (varState' : VariableState ctx'),
      interpretOp newOp state hInB = some (.ok (⟨varState', state.memory⟩, none)) ∧
      varState'.getVar? (newOp.getResult 0) = some rv := by
  have hInB : newOp.InBounds ctx'.raw := WfRewriter.createOp_new_inBounds newOp hCreate
  -- Structural fields of the created operation.
  have hType : newOp.getOpType! ctx'.raw = opType := by
    rw [OperationPtr.getOpType!_WfRewriter_createOp hCreate, if_pos rfl]
  have hOps : newOp.getOperands! ctx'.raw = #[] := by
    rw [OperationPtr.getOperands!_WfRewriter_createOp hCreate, if_pos rfl]
  have hSuccs : newOp.getSuccessors! ctx'.raw = #[] := by
    rw [OperationPtr.getSuccessors!_WfRewriter_createOp hCreate, if_pos rfl]
  have hResTypes : newOp.getResultTypes! ctx'.raw = #[resType] := by
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hCreate, if_pos rfl]
  have hNumRes : newOp.getNumResults! ctx'.raw = 1 := by
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hCreate, if_pos rfl]; rfl
  have hProps : newOp.getProperties! ctx'.raw opType = properties := by
    have := OperationPtr.getProperties!_WfRewriter_createOp hCreate (operation := newOp)
    grind
  have hResType0 : (ValuePtr.opResult (newOp.getResult 0)).getType! ctx'.raw = resType := by
    rw [ValuePtr.getType!_WfRewriter_createOp hCreate]
    simp [OperationPtr.getResult]
  -- The operands (there are none) are always fetched.
  have hOV : state.variables.getOperandValues newOp = some #[] := by
    simp [VariableState.getOperandValues, hOps]
  -- Setting the single result succeeds because `rv` conforms to `resType`.
  have hConf' : rv.Conforms ((ValuePtr.opResult (newOp.getResult 0)).getType! ctx'.raw) := by
    rw [hResType0]; exact hConf
  have hSet : state.variables.setResultValues? newOp #[rv]
      = some (state.variables.setVar (newOp.getResult 0) rv hConf' (by grind)) := by
    simp only [VariableState.setResultValues?, hNumRes]
    rw [dif_pos (by simp)]
    simp only [VariableState.setResultValues?_loop,
      show (#[rv] : Array RuntimeValue)[0] = rv from rfl]
    rw [VariableState.setVar?_eq_some_setVar hConf']
    simp
  refine ⟨hInB, state.variables.setVar (newOp.getResult 0) rv hConf' (by grind), ?_, ?_⟩
  · rw [interpretOp_some_iff]
    refine ⟨#[], #[rv], state.memory, _, hOV, ?_, hSet, rfl⟩
    simp only [OperationPtr.interpret, hResTypes, hSuccs]
    subst hType
    rw [hProps]
    exact hSem state.memory
  · rw [VariableState.getVar?_of_setVar, if_pos rfl]

/-! ## Per-kind semantic lemmas -/

private theorem sem_arith_constant {bw : Nat} {v : BitVec bw} {resType : TypeAttr}
    (hConf : (RuntimeValue.int bw (.val v)).Conforms resType) (mem : MemoryState) :
    interpretOp' (.arith .constant)
      ({ value := IntegerAttr.mk v.toInt (IntegerType.mk bw) } : ArithConstantProperties)
      #[resType] #[] #[] mem
      = some (.ok (#[.int bw (.val v)], mem, none)) := by
  obtain ⟨tyVal, tyProp⟩ := resType
  cases tyVal <;> simp only [RuntimeValue.Conforms] at hConf
  case integerType intTy =>
    subst hConf
    simp [interpretOp', Arith.interpretOp', bind, pure]

private theorem sem_llvm_constant {bw : Nat} {v : BitVec bw} {resType : TypeAttr}
    (hConf : (RuntimeValue.int bw (.val v)).Conforms resType) (mem : MemoryState) :
    interpretOp' (.llvm .mlir__constant)
      ({ value := .integer (IntegerAttr.mk v.toInt (IntegerType.mk bw)) }
        : LLVMConstantProperties)
      #[resType] #[] #[] mem
      = some (.ok (#[.int bw (.val v)], mem, none)) := by
  obtain ⟨tyVal, tyProp⟩ := resType
  cases tyVal <;> simp only [RuntimeValue.Conforms] at hConf
  case integerType intTy =>
    subst hConf
    simp [interpretOp', Llvm.interpretOp', Data.LLVM.Int.constant, pure]

private theorem sem_llvm_poison {bw : Nat} {resType : TypeAttr}
    (hConf : (RuntimeValue.int bw (Data.LLVM.Int.mlir_poison bw)).Conforms resType)
    (mem : MemoryState) :
    interpretOp' (.llvm .mlir__poison) () #[resType] #[] #[] mem
      = some (.ok (#[.int bw (Data.LLVM.Int.mlir_poison bw)], mem, none)) := by
  obtain ⟨tyVal, tyProp⟩ := resType
  cases tyVal <;> simp only [RuntimeValue.Conforms] at hConf
  case integerType intTy =>
    subst hConf
    simp [interpretOp', Llvm.interpretOp', pure]

private theorem sem_riscv_li {r : Data.RISCV.Reg} {resType : TypeAttr} (mem : MemoryState) :
    interpretOp' (.riscv .li)
      ({ value := IntegerAttr.mk r.val.toInt (IntegerType.mk 64) }
        : RISCVImmediateProperties)
      #[resType] #[] #[] mem
      = some (.ok (#[.reg r], mem, none)) := by
  cases r with
  | mk val => simp [interpretOp', Riscv.interpretOp', Data.RISCV.li, pure]

/-! ## The packaged materialization theorem -/

set_option maxHeartbeats 1000000 in
/--
  Detached-materialization analogue of
  `PatternRewriter.materializeConstant!_interpretOp`. This is the form used by
  `foldOperationLocal`: the new operation is present in `ctx'` but is not yet
  linked into a block.
-/
theorem WfRewriter.materializeConstant!_interpretOp
    {ctx ctx' : WfIRContext OpCode} {rv : RuntimeValue} {resType : TypeAttr}
    {forOp : OpCode} {newOp : OperationPtr}
    (hMat : WfRewriter.materializeConstant! ctx rv resType forOp = some (ctx', newOp))
    (hConf : rv.Conforms resType)
    (hNotModArith : ∀ mop, forOp ≠ .mod_arith mop)
    (state : InterpreterState ctx') :
    ∃ (hInB : newOp.InBounds ctx'.raw) (varState' : VariableState ctx'),
      interpretOp newOp state hInB = some (.ok (⟨varState', state.memory⟩, none)) ∧
      varState'.getVar? (newOp.getResult 0) = some rv := by
  unfold WfRewriter.materializeConstant! at hMat
  split at hMat
  case h_1 bw v =>
    split at hMat
    case h_1 =>
      obtain ⟨hoper, hblock, hreg, hins, hCreate⟩ :=
        WfRewriter.createOp!_some_inv hMat
      exact interpretOp_createOp_constant hCreate (sem_llvm_constant hConf) hConf state
    case h_2 mop => exact absurd rfl (hNotModArith mop)
    case h_3 =>
      obtain ⟨hoper, hblock, hreg, hins, hCreate⟩ :=
        WfRewriter.createOp!_some_inv hMat
      exact interpretOp_createOp_constant hCreate (sem_arith_constant hConf) hConf state
  case h_2 bw =>
    obtain ⟨hoper, hblock, hreg, hins, hCreate⟩ :=
      WfRewriter.createOp!_some_inv hMat
    exact interpretOp_createOp_constant hCreate (sem_llvm_poison hConf) hConf state
  case h_3 r =>
    obtain ⟨hoper, hblock, hreg, hins, hCreate⟩ :=
      WfRewriter.createOp!_some_inv hMat
    exact interpretOp_createOp_constant hCreate (fun mem => sem_riscv_li mem) hConf state
  case h_4 => simp at hMat

set_option maxHeartbeats 1000000 in
/--
  Layer C: interpreting the operation built by
  `PatternRewriter.materializeConstant!` succeeds in any state over the
  post-creation context, binds its single result to exactly the materialized
  value `rv`, threads memory through unchanged, and produces no control flow.

  The `mod_arith` arm is excluded (`hNotModArith`): its constants are
  uninterpreted, and a lifting proof about a folded `mod_arith` operation is
  already vacuous at the source-interpretation hypothesis.
-/
theorem PatternRewriter.materializeConstant!_interpretOp
    {rewriter rewriter' : PatternRewriter OpCode} {rv : RuntimeValue} {resType : TypeAttr}
    {forOp : OpCode} {ip : InsertPoint} {newOp : OperationPtr}
    (hMat : rewriter.materializeConstant! rv resType forOp ip = some (rewriter', newOp))
    (hConf : rv.Conforms resType)
    (hNotModArith : ∀ mop, forOp ≠ .mod_arith mop)
    (state : InterpreterState rewriter'.ctx) :
    ∃ (hInB : newOp.InBounds rewriter'.ctx.raw) (varState' : VariableState rewriter'.ctx),
      interpretOp newOp state hInB = some (.ok (⟨varState', state.memory⟩, none)) ∧
      varState'.getVar? (newOp.getResult 0) = some rv := by
  unfold PatternRewriter.materializeConstant! at hMat
  split at hMat
  case h_1 bw v =>
    split at hMat
    case h_1 =>
      -- llvm.mlir.constant
      obtain ⟨⟨newCtx, newOp'⟩, hCreate!, hEq⟩ := Option.bind_eq_some_iff.mp hMat
      obtain ⟨hoper', hblock', hreg', hins', hCreate⟩ := WfRewriter.createOp!_some_inv (by
        simpa [PatternRewriter.createOp!, Option.bind_eq_some_iff] using hCreate!)
      obtain ⟨hCtx, rfl⟩ : rewriter'.ctx = newCtx ∧ newOp = newOp' := by
        split at hEq <;> grind
      subst hCtx
      exact interpretOp_createOp_constant hCreate (sem_llvm_constant hConf) hConf state
    case h_2 mop => exact absurd rfl (hNotModArith mop)
    case h_3 =>
      -- arith.constant
      obtain ⟨⟨newCtx, newOp'⟩, hCreate!, hEq⟩ := Option.bind_eq_some_iff.mp hMat
      obtain ⟨hoper', hblock', hreg', hins', hCreate⟩ := WfRewriter.createOp!_some_inv (by
        simpa [PatternRewriter.createOp!, Option.bind_eq_some_iff] using hCreate!)
      obtain ⟨hCtx, rfl⟩ : rewriter'.ctx = newCtx ∧ newOp = newOp' := by
        split at hEq <;> grind
      subst hCtx
      exact interpretOp_createOp_constant hCreate (sem_arith_constant hConf) hConf state
  case h_2 bw =>
    -- llvm.mlir.poison
    obtain ⟨⟨newCtx, newOp'⟩, hCreate!, hEq⟩ := Option.bind_eq_some_iff.mp hMat
    obtain ⟨hoper', hblock', hreg', hins', hCreate⟩ := WfRewriter.createOp!_some_inv (by
      simpa [PatternRewriter.createOp!, Option.bind_eq_some_iff] using hCreate!)
    obtain ⟨hCtx, rfl⟩ : rewriter'.ctx = newCtx ∧ newOp = newOp' := by
      split at hEq <;> grind
    subst hCtx
    exact interpretOp_createOp_constant hCreate (sem_llvm_poison hConf) hConf state
  case h_3 r =>
    -- riscv.li
    obtain ⟨⟨newCtx, newOp'⟩, hCreate!, hEq⟩ := Option.bind_eq_some_iff.mp hMat
    obtain ⟨hoper', hblock', hreg', hins', hCreate⟩ := WfRewriter.createOp!_some_inv (by
      simpa [PatternRewriter.createOp!, Option.bind_eq_some_iff] using hCreate!)
    obtain ⟨hCtx, rfl⟩ : rewriter'.ctx = newCtx ∧ newOp = newOp' := by
      split at hEq <;> grind
    subst hCtx
    exact interpretOp_createOp_constant hCreate (fun mem => sem_riscv_li mem) hConf state
  case h_4 => simp at hMat

end Veir
