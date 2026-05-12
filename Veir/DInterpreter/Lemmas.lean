import Veir.DInterpreter.Basic
import Veir.Dominance

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpInfo}
variable {state state' : InterpreterState ctx}
variable {op op' : OperationPtr}

@[grind =]
theorem InterpreterState.getVar?_setVar :
    (InterpreterState.setVar' state var' α val hα).getVar'! var β hβ =
    if h : var = var' then
      have hαβ : α = β := by grind
      hαβ ▸ val
    else
      state.getVar'! var β hβ := by
  grind [InterpreterState.setVar', InterpreterState.getVar'!]

@[grind =]
theorem InterpreterState.getVar'!_setVar' :
    (InterpreterState.setVar' state var' α val hα).getVar? var =
    if h : var = var' then
      have hαβ : α = runtimeValueType (var.getType! ctx.raw) := by grind
      hαβ ▸ some val
    else
      state.getVar? var := by
  grind [InterpreterState.setVar', InterpreterState.getVar?]

theorem InterpreterState.getVar!_setVar' :
    (InterpreterState.setVar' state var' α val hα).getVar! var =
    if h : var = var' then
      have hαβ : α = runtimeValueType (var.getType! ctx.raw) := by grind
      hαβ ▸ val
    else
      state.getVar! var := by
  grind [InterpreterState.setVar', InterpreterState.getVar!]

@[simp, grind =]
theorem InterpreterState.getVar₁!_setVar₁_eq heq :
    (InterpreterState.setVar₁ state var ty val heq).getVar₁! var ty = val := by
  grind [InterpreterState.setVar₁, InterpreterState.getVar₁!]

@[grind .]
theorem InterpreterState.getVar₁!_eq (state : InterpreterState ctx) (heq : ty = ty') :
    state.getVar₁! var ty =
    heq ▸ state.getVar₁! var ty' := by
  grind [InterpreterState.setVar₁, InterpreterState.getVar₁!]

@[grind .]
theorem InterpreterState.getVar₁!_eq₂ {state : InterpreterState ctx}
    (h : state.getVar₁! var ty = val) (heq : ty = ty') :
    state.getVar₁! var ty' = heq ▸ val := by
  grind

theorem InterpreterState.getVar'!_of_getVar'! :
    state.getVar'! var α hα = x →
    state.getVar'! var β hβ = (show α = β by rw [hα, hβ]) ▸ x := by
  grind [InterpreterState.getVar'!]

theorem InterpreterState.getVar?_of_getVar'! (hα : α = runtimeValueType (var.getType! ctx.raw)) :
    state.getVar? var = some x →
    state.getVar? var = (show Option (runtimeValueType (var.getType! ctx.raw)) = Option α by rw [hα]) ▸ some (state.getVar'! var α hα) := by
  grind [getVar?, getVar'!, Std.ExtDHashMap.get?_eq_some_get!, Std.ExtDHashMap.mem_iff_isSome_get?]

theorem InterpreterState.getVar'!_eq_getVar! :
    state.getVar! var = state.getVar'! var (runtimeValueType (var.getType! ctx.raw)) (by rfl) := by
  grind [InterpreterState.getVar'!, InterpreterState.getVar!]

end Veir
