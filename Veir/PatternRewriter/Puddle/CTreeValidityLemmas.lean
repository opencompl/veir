module

public import Veir.PatternRewriter.Puddle.CTreeValidity

public section

namespace Veir.Puddle

/-- A concrete sequence of values supplied to the matcher's universal value binders. -/
inductive SemanticAssignment.BindsValues : SemanticAssignment →
    List (Handle OpCode .value) → List RuntimeValue → SemanticAssignment → List TypeAttr → Prop
  | nil (assignment) : BindsValues assignment [] [] assignment []
  | cons {assignment handles values final types} (handle) (value) (type)
      (tail : BindsValues (assignment.bindValue handle value type) handles values final types) :
      BindsValues assignment (handle :: handles) (value :: values) final (type :: types)

/-- Instantiate universal value binders with a concrete sequence of outcomes. -/
theorem SemanticAssignment.ForallValues.of_bindsValues
    {assignment final : SemanticAssignment} {handles : List (Handle OpCode .value)}
    {values : List RuntimeValue} {types : List TypeAttr}
    {k : List RuntimeValue → SemanticAssignment → Prop}
    (h : assignment.ForallValues handles types k)
    (hvalues : assignment.BindsValues handles values final types) : k values final := by
  induction hvalues generalizing k with
  | nil => exact h
  | cons handle value type tail ih => exact ih (h value)

/-- Universally bound values preserve implications between continuations. -/
theorem SemanticAssignment.ForallValues.mono
    {assignment : SemanticAssignment} {handles : List (Handle OpCode .value)}
    {types : List TypeAttr}
    {k l : List RuntimeValue → SemanticAssignment → Prop}
    (h : assignment.ForallValues handles types k)
    (hkl : ∀ values final, k values final → l values final) :
    assignment.ForallValues handles types l := by
  induction handles generalizing assignment types k l with
  | nil => cases types with
    | nil => exact hkl [] assignment h
    | cons => exact False.elim h
  | cons handle handles ih =>
    cases types with
    | nil => exact False.elim h
    | cons type types =>
      intro value
      exact ih (h value) (fun values final => hkl (value :: values) final)

namespace CTree

/-- One set of concrete choices satisfying a match declaration's semantic constraints. -/
inductive MatchDecl.Realizes (root : Handle OpCode .op) :
    MatchDecl OpCode → SemanticAssignment → SemanticAssignment → Prop
  | type {matcher handle assignment} (ty)
      (accepted : matcher ty = true) :
      Realizes root (.type matcher handle) assignment (assignment.bindType handle ty)
  | value {typeHandle handle assignment} (ty value)
      (typeBound : assignment.getType typeHandle = some ty) (conforms : value.Conforms ty) :
      Realizes root (.value typeHandle handle) assignment (assignment.bindValue handle value ty)
  | rootOperation {code operandHandles resultTypeHandles matcher propertyHandle opHandle
      resultHandles count assignment} (operands operandTypes resultTypes property)
      (valuesBound : assignment.getValues operandHandles.toList = some operands)
      (valueTypesBound : assignment.getValueTypes operandHandles.toList = some operandTypes)
      (typesBound : assignment.getTypes resultTypeHandles.toList = some resultTypes)
      (accepted : matcher property = true)
      (verified : IsFromVerifiedOp code operandTypes.toArray resultTypes.toArray property)
      (isRoot : opHandle = root) :
      Realizes root (.operation code operandHandles resultTypeHandles matcher propertyHandle
        opHandle resultHandles count) assignment (assignment.bindProperty propertyHandle property)
  | operation {code operandHandles resultTypeHandles matcher propertyHandle opHandle
      resultHandles count assignment final} (operands operandTypes resultTypes property results)
      (valuesBound : assignment.getValues operandHandles.toList = some operands)
      (valueTypesBound : assignment.getValueTypes operandHandles.toList = some operandTypes)
      (typesBound : assignment.getTypes resultTypeHandles.toList = some resultTypes)
      (accepted : matcher property = true)
      (verified : IsFromVerifiedOp code operandTypes.toArray resultTypes.toArray property)
      (notRoot : opHandle ≠ root)
      (resultsBound : assignment.BindsValues resultHandles.toList results final resultTypes)
      (interprets : CanInterpretTo code property resultTypes.toArray operands.toArray
        (.ok results.toArray)) :
      Realizes root (.operation code operandHandles resultTypeHandles matcher propertyHandle
        opHandle resultHandles count) assignment (final.bindProperty propertyHandle property)
  | inspectOperation {Outputs : Type} [IsMetadataTuple OpCode Outputs]
      {handle inspect outputs assignment} (values : MetadataValues OpCode Outputs) :
      Realizes root (.inspectOperation handle inspect outputs) assignment
        (MetadataTuple.bindSemantic assignment outputs values)
  | applyNative {Inputs : Type} [IsMetadataTuple OpCode Inputs]
      {inputs predicate assignment} (values : MetadataValues OpCode Inputs)
      (resolved : MetadataTuple.resolveSemantic assignment inputs = some values)
      (accepted : predicate values = true) :
      Realizes root (.applyNative inputs predicate) assignment assignment

/-- Instantiate a declaration's semantic obligation with satisfying choices. -/
theorem MatchDecl.Models.of_realizes {root : Handle OpCode .op} {decl : MatchDecl OpCode}
    {assignment final : SemanticAssignment} {k : SemanticAssignment → Prop}
    (h : MatchDecl.Models root decl assignment k)
    (realizes : MatchDecl.Realizes root decl assignment final) : k final := by
  cases realizes with
  | type ty accepted => exact h ty accepted
  | value ty value typeBound conforms =>
    simp only [MatchDecl.Models, typeBound] at h
    exact h value conforms
  | rootOperation operands operandTypes resultTypes property valuesBound valueTypesBound typesBound accepted verified isRoot =>
    simp only [MatchDecl.Models, valuesBound, valueTypesBound, typesBound, isRoot, ↓reduceIte] at h
    exact h property accepted verified
  | operation operands operandTypes resultTypes property results valuesBound valueTypesBound typesBound accepted verified notRoot
      resultsBound interprets =>
    simp only [MatchDecl.Models, valuesBound, valueTypesBound, typesBound, notRoot, ↓reduceIte] at h
    exact SemanticAssignment.ForallValues.of_bindsValues (h property accepted verified) resultsBound interprets
  | inspectOperation values => exact h values
  | applyNative values resolved accepted =>
    simp only [MatchDecl.Models, resolved] at h
    exact h accepted

/-- Concrete semantic choices in the matcher's binding order. -/
inductive MatchProg.RealizesDecls (root : Handle OpCode .op) :
    List (MatchDecl OpCode) → SemanticAssignment → SemanticAssignment → Prop
  | nil (assignment) : RealizesDecls root [] assignment assignment
  | cons {decl decls assignment middle final}
      (head : MatchDecl.Realizes root decl assignment middle)
      (tail : RealizesDecls root decls middle final) :
      RealizesDecls root (decl :: decls) assignment final

/-- Instantiate all semantic declarations with a sequence of satisfying choices. -/
theorem MatchProg.ModelsDecls.of_realizes {root : Handle OpCode .op}
    {decls : List (MatchDecl OpCode)} {assignment final : SemanticAssignment}
    {k : SemanticAssignment → Prop} (h : MatchProg.ModelsDecls root decls assignment k)
    (realizes : MatchProg.RealizesDecls root decls assignment final) : k final := by
  induction realizes with
  | nil => exact h
  | cons head tail ih => exact ih (MatchDecl.Models.of_realizes h head)

/-- An assignment obtained by satisfying the matcher's semantic constraints. -/
def MatchProg.Realizes (prog : MatchProg OpCode α) (assignment : SemanticAssignment) : Prop :=
  MatchProg.RealizesDecls prog.rootHandle prog.bindingDecls SemanticAssignment.empty assignment

/-- Instantiate matcher semantics with a satisfying assignment. -/
theorem MatchProg.Models.of_realizes {prog : MatchProg OpCode α}
    {assignment : SemanticAssignment} {k : SemanticAssignment → Prop}
    (h : MatchProg.Models prog k) (realizes : MatchProg.Realizes prog assignment) :
    k assignment :=
  MatchProg.ModelsDecls.of_realizes h realizes

/-- Semantic validity supplies the local simulation for every realized match. -/
theorem Pattern.Valid.refines_of_realizes {rule : Veir.Puddle.Pattern OpCode}
    (valid : Pattern.Valid rule) {assignment : SemanticAssignment}
    (realizes : MatchProg.Realizes rule.matcher assignment) (memory : MemoryState)
    {source : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)}
    (hsource : MatchProg.rootSemantics rule.matcher assignment memory = some source) :
    _root_.CTree.Sim (fun target source => OperationResult.isRefinedBy source target)
      (CreateProg.semantics rule.creation rule.replacement assignment memory) source := by
  have h := MatchProg.Models.of_realizes valid.refines realizes memory
  simpa only [hsource] using h

/-- A matcher declaration preserves implications between semantic continuations. -/
theorem MatchDecl.Models.mono {root : Handle OpCode .op} {decl : MatchDecl OpCode}
    {assignment : SemanticAssignment} {k l : SemanticAssignment → Prop}
    (h : MatchDecl.Models root decl assignment k)
    (hkl : ∀ final, k final → l final) :
    MatchDecl.Models root decl assignment l := by
  cases decl with
  | type matcher handle => exact fun ty hty => hkl _ (h ty hty)
  | value typeHandle handle =>
    simp only [MatchDecl.Models] at h ⊢
    split at h <;> simp_all
  | operation code operands types matcher propertyHandle opHandle results count =>
    simp only [MatchDecl.Models] at h ⊢
    split at h
    · intro property hproperty verified
      have h := h property hproperty verified
      by_cases heq : opHandle = root
      · simp only [heq, ↓reduceIte] at h ⊢
        exact hkl _ h
      · simp only [heq, ↓reduceIte] at h ⊢
        apply SemanticAssignment.ForallValues.mono h
        intro resultValues final hresult hsem
        exact hkl _ (hresult hsem)
    · simp_all
  | inspectOperation handle inspect outputs => exact fun values => hkl _ (h values)
  | applyNative inputs predicate =>
    simp only [MatchDecl.Models] at h ⊢
    split at h <;> simp_all

/-- A list of matching declarations preserves implications between continuations. -/
theorem MatchProg.ModelsDecls.mono {root : Handle OpCode .op}
    {decls : List (MatchDecl OpCode)} {assignment : SemanticAssignment}
    {k l : SemanticAssignment → Prop}
    (h : MatchProg.ModelsDecls root decls assignment k)
    (hkl : ∀ final, k final → l final) :
    MatchProg.ModelsDecls root decls assignment l := by
  induction decls generalizing assignment with
  | nil => exact hkl assignment h
  | cons decl decls ih =>
    exact MatchDecl.Models.mono h (fun _ htail => ih htail)

/-- Matcher semantics can be used to establish any consequence of its continuation. -/
theorem MatchProg.Models.mono {prog : MatchProg OpCode α}
    {k l : SemanticAssignment → Prop} (h : MatchProg.Models prog k)
    (hkl : ∀ final, k final → l final) : MatchProg.Models prog l :=
  MatchProg.ModelsDecls.mono h hkl

end CTree
end Veir.Puddle
