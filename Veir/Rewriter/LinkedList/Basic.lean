module

public import ExArray.CompilerExtras
import Veir.Prelude
public import Veir.Prelude
public import Veir.IR
public import Veir.IR.Buffed.Basic
public import Lean.Data.Json.Parser
public meta import Veir.IR.Buffed.Meta
import Veir.IR.Buffed.InBounds
import Veir.IR.Buffed.Meta
import Veir.IR.Buffed.Basic


@[expose] public section

namespace Veir

attribute [local grind]
  Sim.ValuePtr.getOpOperandPtrPtr Sim.OpOperandPtr.getOpOperandPtrPtr
  Sim.BlockOperandPtr.getBlockOperandPtrPtr Sim.BlockPtr.getBlockOperandPtrPtr

attribute [local grind]
 Sim.BlockArgumentPtr.toO
 Sim.BlockPtr.toO
 Sim.OperationPtr.toO
 Sim.BlockOperandPtr.toO
 Sim.OpOperandPtr.toO
 Sim.RegionPtr.toO
 Sim.OpResultPtr.toO
 Sim.ValuePtr.toO

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
variable {ctx : Sim.IRContext OpInfo}

/- Use def chain for operands. -/
buffed
def Sim.OpOperandPtr.removeFromCurrentSim (ctx: Sim.IRContext OpInfo) (operandPtr: Sim.OpOperandPtr)
    (operandIn: operandPtr.InBounds ctx := by grind)
    (ctxInBounds: ctx.spec.FieldsInBounds := by grind) : Sim.IRContext OpInfo :=
  let back := operandPtr.getBack ctx (by grind)
  let nextUse := operandPtr.getNextUse ctx (by grind)
  let ctx := back.set ctx nextUse (by grind) (by grind)
  match hNextUse: nextUse.toOption with
  | none => ctx
  | some nextPtr => nextPtr.setBack ctx back (by grind) (by grind)

noncomputable
def Sim.OpOperandPtr.removeFromCurrent! (ctx: Sim.IRContext OpInfo) (operandPtr: Sim.OpOperandPtr) : Sim.IRContext OpInfo :=
  let back := operandPtr.getBack! ctx
  let nextUse := operandPtr.getNextUse! ctx
  let ctx := back.set! ctx nextUse
  match nextUse.toOption with
  | none => ctx
  | some nextPtr => nextPtr.setBack! ctx back

@[grind _=_, eq_bang ←]
theorem Sim.OpOperandPtr.removeFromCurrent!_eq_removeFromCurrent
    {operandPtr : Sim.OpOperandPtr}
    (operandIn : operandPtr.InBounds ctx) (ctxIn : ctx.spec.FieldsInBounds) :
    removeFromCurrent! ctx operandPtr = operandPtr.removeFromCurrent ctx operandIn ctxIn := by
  simp [Sim.OpOperandPtr.removeFromCurrent_def, Sim.OpOperandPtr.removeFromCurrentSim, removeFromCurrent!]
  grind

@[grind .]
theorem Sim.OpOperandPtr.removeFromCurrent_fieldsInBounds :
    (removeFromCurrent ctx operandPtr h₁ h₂).spec.FieldsInBounds := by
  simp [removeFromCurrent, removeFromCurrentSpec, removeFromCurrentSim]
  grind

@[grind =]
theorem Sim.OpOperandPtr.removeFromCurrent_veir_inBounds (ptr : Veir.GenericPtr) :
    ptr.InBounds (removeFromCurrent ctx operand h₁ h₂).spec ↔ ptr.InBounds ctx.spec := by
  simp [removeFromCurrent_def, removeFromCurrentSim]; grind

@[grind =]
theorem Sim.OpOperandPtr.removeFromCurrent_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (removeFromCurrent ctx operand h₁ h₂) ↔ ptr.InBounds ctx := by
  simp [removeFromCurrent_def, removeFromCurrentSim]; grind

buffed
def Sim.OpOperandPtr.insertIntoCurrentSim (ctx: Sim.IRContext OpInfo) (operandPtr: Sim.OpOperandPtr)
    (operandIn: operandPtr.InBounds ctx := by grind) (ctxInBounds: ctx.spec.FieldsInBounds) : IRContext OpInfo :=
  let value : Sim.ValuePtr := operandPtr.getValue ctx (by grind)
  let ctx := operandPtr.setBack ctx value.getOpOperandPtrPtr (by grind) (by grind)
  let newNextUse := value.getFirstUse ctx (by grind)
  let ctx := operandPtr.setNextUse ctx newNextUse (by grind) (by grind)
  let ctx := value.setFirstUse ctx operandPtr.toO (by grind) (by grind)
  match hNextUse: newNextUse.toOption with
  | none => ctx
  | some nextUse => nextUse.setBack ctx operandPtr.getOpOperandPtrPtr (by grind) (by grind)

noncomputable
def Sim.OpOperandPtr.insertIntoCurrent! (ctx : Sim.IRContext OpInfo) (operandPtr : Sim.OpOperandPtr) : Sim.IRContext OpInfo :=
  let value := operandPtr.getValue! ctx
  let ctx := operandPtr.setBack! ctx value.getOpOperandPtrPtr
  let newNextUse := value.getFirstUse! ctx
  let ctx := operandPtr.setNextUse! ctx newNextUse
  let ctx := value.setFirstUse! ctx operandPtr.toO
  match newNextUse.toOption with
  | none => ctx
  | some nextUse => nextUse.setBack! ctx operandPtr.getOpOperandPtrPtr

@[grind _=_, eq_bang ←]
theorem Sim.OpOperandPtr.insertIntoCurrent!_eq_insertIntoCurrent
    {operandPtr : Sim.OpOperandPtr}
    (operandIn : operandPtr.InBounds ctx) (ctxIn : ctx.spec.FieldsInBounds) :
    insertIntoCurrent! ctx operandPtr = operandPtr.insertIntoCurrent ctx operandIn ctxIn := by
  simp [insertIntoCurrent_def, insertIntoCurrentSim, insertIntoCurrent!]
  grind

@[grind .]
theorem Sim.OpOperandPtr.insertIntoCurrent_fieldsInBounds :
    (insertIntoCurrent ctx operandPtr h₁ h₂).spec.FieldsInBounds := by
  simp [insertIntoCurrent_def, insertIntoCurrentSim]
  grind

@[grind =]
theorem Sim.OpOperandPtr.insertIntoCurrent_veir_inBounds (ptr : Veir.GenericPtr) :
    ptr.InBounds (insertIntoCurrent ctx operand h₁ h₂).spec ↔ ptr.InBounds ctx.spec := by
  simp [insertIntoCurrent_def, insertIntoCurrentSim]
  grind

@[grind =]
theorem Sim.OpOperandPtr.insertIntoCurrent_inBounds (ptr : GenericPtr) :
    ptr.InBounds (insertIntoCurrent ctx operand h₁ h₂) ↔ ptr.InBounds ctx := by
  simp [insertIntoCurrent_def, insertIntoCurrentSim]
  grind

/- Use def chain for operands. -/

buffed
def Sim.BlockOperandPtr.removeFromCurrentSim (ctx: Sim.IRContext OpInfo) (operandPtr: Sim.BlockOperandPtr)
    (operandIn: operandPtr.InBounds ctx := by grind)
    (ctxInBounds: ctx.spec.FieldsInBounds := by grind) : Sim.IRContext OpInfo :=
  let back := operandPtr.getBack ctx (by grind)
  let nextUse := operandPtr.getNextUse ctx (by grind)
  let ctx := back.set ctx nextUse (by grind) (by grind)
  match hNextUse: nextUse.toOption with
  | none => ctx
  | some nextPtr => nextPtr.setBack ctx back (by grind) (by grind)

noncomputable
def Sim.BlockOperandPtr.removeFromCurrent! (ctx : Sim.IRContext OpInfo) (operandPtr : Sim.BlockOperandPtr) :
    Sim.IRContext OpInfo :=
  let back := operandPtr.getBack! ctx
  let nextUse := operandPtr.getNextUse! ctx
  let ctx := back.set! ctx nextUse
  match nextUse.toOption with
  | none => ctx
  | some nextPtr => nextPtr.setBack! ctx back

@[grind _=_, eq_bang ←]
theorem Sim.BlockOperandPtr.removeFromCurrent!_eq_removeFromCurrent
    {operandPtr : Sim.BlockOperandPtr}
    (operandIn : operandPtr.InBounds ctx) (ctxIn : ctx.spec.FieldsInBounds) :
    removeFromCurrent! ctx operandPtr = operandPtr.removeFromCurrent ctx operandIn ctxIn := by
  simp [Sim.BlockOperandPtr.removeFromCurrent_def, Sim.BlockOperandPtr.removeFromCurrentSim, removeFromCurrent!]
  grind

@[grind .]
theorem Sim.BlockOperandPtr.removeFromCurrent_fieldsInBounds :
    (removeFromCurrent ctx operandPtr h₁ h₂).spec.FieldsInBounds := by
  simp [removeFromCurrent_def, removeFromCurrentSim]
  grind

@[grind =]
theorem Sim.BlockOperandPtr.removeFromCurrent_veir_inBounds (ptr : Veir.GenericPtr) :
    ptr.InBounds (removeFromCurrent ctx operand h₁ h₂).spec ↔ ptr.InBounds ctx.spec := by
  simp [removeFromCurrent_def, removeFromCurrentSim]
  grind

@[grind =]
theorem Sim.BlockOperandPtr.removeFromCurrent_inBounds (ptr : GenericPtr) :
    ptr.InBounds (removeFromCurrent ctx operand h₁ h₂) ↔ ptr.InBounds ctx := by
  simp [removeFromCurrent_def, removeFromCurrentSim]
  grind

buffed
def Sim.BlockOperandPtr.insertIntoCurrentSim (ctx: Sim.IRContext OpInfo) (operandPtr: Sim.BlockOperandPtr)
    (operandIn: operandPtr.InBounds ctx := by grind) (ctxInBounds: ctx.spec.FieldsInBounds) : Sim.IRContext OpInfo :=
  let block := operandPtr.getValue ctx (by grind)
  let ctx := operandPtr.setBack ctx block.getBlockOperandPtrPtr (by grind) (by grind)
  let newNextUse := block.getFirstUse ctx (by grind)
  let ctx := operandPtr.setNextUse ctx newNextUse (by grind) (by grind)
  let ctx := block.setFirstUse ctx operandPtr.toO (by grind) (by grind)
  match hNextUse: newNextUse.toOption with
  | none => ctx
  | some nextUse => nextUse.setBack ctx operandPtr.getBlockOperandPtrPtr (by grind) (by grind)

noncomputable
def Sim.BlockOperandPtr.insertIntoCurrent! (ctx : Sim.IRContext OpInfo) (operandPtr : Sim.BlockOperandPtr) : Sim.IRContext OpInfo :=
  let block := operandPtr.getValue! ctx
  let ctx := operandPtr.setBack! ctx block.getBlockOperandPtrPtr
  let newNextUse := block.getFirstUse! ctx
  let ctx := operandPtr.setNextUse! ctx newNextUse
  let ctx := block.setFirstUse! ctx operandPtr.toO
  match newNextUse.toOption with
  | none => ctx
  | some nextUse => nextUse.setBack! ctx operandPtr.getBlockOperandPtrPtr

@[grind _=_, eq_bang ←]
theorem Sim.BlockOperandPtr.insertIntoCurrent!_eq_insertIntoCurrent
    {operandPtr : Sim.BlockOperandPtr}
    (operandIn : operandPtr.InBounds ctx) (ctxIn : ctx.spec.FieldsInBounds) :
    insertIntoCurrent! ctx operandPtr = operandPtr.insertIntoCurrent ctx operandIn ctxIn := by
  simp [insertIntoCurrent_def, insertIntoCurrentSim, insertIntoCurrent!]
  grind

@[grind .]
theorem Sim.BlockOperandPtr.insertIntoCurrent_fieldsInBounds :
    (insertIntoCurrent ctx operandPtr h₁ h₂).spec.FieldsInBounds := by
  simp [insertIntoCurrent_def, insertIntoCurrentSim]
  grind

@[grind =]
theorem Sim.BlockOperandPtr.insertIntoCurrent_veir_inBounds (ptr : Veir.GenericPtr) :
    ptr.InBounds (insertIntoCurrent ctx operand h₁ h₂).spec ↔ ptr.InBounds ctx.spec := by
  simp [insertIntoCurrent_def, insertIntoCurrentSim]
  grind

@[grind =]
theorem Sim.BlockOperandPtr.insertIntoCurrent_inBounds (ptr : GenericPtr) :
    ptr.InBounds (insertIntoCurrent ctx operand h₁ h₂) ↔ ptr.InBounds ctx := by
  simp [insertIntoCurrent_def, insertIntoCurrentSim]
  grind

/- Operation linked list. -/

buffed
def Sim.OperationPtr.linkBetweenSim (self: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (prevOp: Sim.OptionOperationPtr) (nextOp: Sim.OptionOperationPtr)
    (selfIn: self.InBounds ctx := by grind)
    (prevIn: prevOp.InBounds ctx := by grind)
    (nextIn: nextOp.InBounds ctx := by grind) : Sim.IRContext OpInfo :=
  let ctx := self.setPrevOp ctx prevOp (by grind) (by grind)
  let ctx := self.setNextOp ctx nextOp (by grind) (by grind)
    match _ : prevOp.toOption with
    | none =>
      match _ : nextOp.toOption with
      | none => ctx
      | some nextOp => nextOp.setPrevOp ctx self.toO (by grind) (by grind)
    | some prevOp =>
      let ctx := prevOp.setNextOp ctx self.toO (by grind) (by grind)
      match _ : nextOp.toOption with
      | none => ctx
      | some nextOp => nextOp.setPrevOp ctx self.toO (by grind) (by grind)

noncomputable def Sim.OperationPtr.linkBetween! (self : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (prevOp : Sim.OptionOperationPtr) (nextOp : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  let ctx := self.setPrevOp! ctx prevOp
  let ctx := self.setNextOp! ctx nextOp
  match prevOp.toOption with
  | none =>
    match nextOp.toOption with
    | none => ctx
    | some nextOp => nextOp.setPrevOp! ctx self.toO
  | some prevOp =>
    let ctx := prevOp.setNextOp! ctx self.toO
    match nextOp.toOption with
    | none => ctx
    | some nextOp => nextOp.setPrevOp! ctx self.toO

@[grind _=_, eq_bang ←]
theorem Sim.OperationPtr.linkBetween!_eq_linkBetween {self : Sim.OperationPtr}
    (selfIn : self.InBounds ctx) (prevIn : prevOp.InBounds ctx) (nextIn : nextOp.InBounds ctx) :
    linkBetween! self ctx prevOp nextOp = self.linkBetween ctx prevOp nextOp selfIn prevIn nextIn := by
  simp [Sim.OperationPtr.linkBetween_def, Sim.OperationPtr.linkBetweenSim, linkBetween!]
  grind

@[grind =]
theorem Sim.OperationPtr.linkBetween_inBounds (ptr : GenericPtr) :
    ptr.InBounds (linkBetween self ctx prevOp nextOp h₁ h₂ h₃) ↔ ptr.InBounds ctx := by
  simp [linkBetween_def, linkBetweenSim]
  grind

@[grind =]
theorem Sim.OperationPtr.linkBetween_veir_inBounds (ptr : Veir.GenericPtr) :
    ptr.InBounds (linkBetween self ctx prevOp nextOp h₁ h₂ h₃).spec ↔ ptr.InBounds ctx.spec := by
  simp [linkBetween_def, linkBetweenSim]
  grind

@[grind .]
theorem Sim.OperationPtr.linkBetween_fieldsInBounds (_hx : ctx.spec.FieldsInBounds) :
    (linkBetween self ctx prevOp nextOp h₁ h₂ h₃).spec.FieldsInBounds := by
  simp [linkBetween_def, linkBetweenSim]
  grind (gen := 20)

/-- Set `self` parent to be `parent`. -/
buffed
def Sim.OperationPtr.setParentWithCheckSim (self: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo) (parent: Sim.BlockPtr)
    (selfIn: self.InBounds ctx := by grind) (parentSim : parent.InBounds ctx := by grind) : Option (Sim.IRContext OpInfo) :=
  match (self.getParent ctx (by grind)).toOption with
  | some _ => none
  | none => self.setParent ctx parent.toO (by grind) (by grind)

noncomputable
def Sim.OperationPtr.setParentWithCheck! (self : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (parent : Sim.BlockPtr) :
    Option (Sim.IRContext OpInfo)  :=
  match (self.getParent! ctx).toOption with
  | some _ => none
  | none => self.setParent! ctx parent.toO


@[grind _=_, eq_bang ←]
theorem Sim.OperationPtr.setParentWithCheck!_eq_setParentWithCheck {self : Sim.OperationPtr} (selfIn : self.InBounds ctx) parentIb :
    setParentWithCheck! self ctx parent = self.setParentWithCheck ctx parent selfIn parentIb := by
  simp [Sim.OperationPtr.setParentWithCheck_def, Sim.OperationPtr.setParentWithCheckSim, setParentWithCheck!]
  grind

@[grind .]
theorem Sim.OperationPtr.setParentWithCheck_fieldsInBounds
    (_h₁ : ctx.spec.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx) :
    (setParentWithCheck self ctx parent h₂).maybe₁ (·.spec.FieldsInBounds) := by
  simp [setParentWithCheck_def, setParentWithCheckSim]
  grind

@[grind =>]
theorem Sim.OperationPtr.setParentWithCheck_fieldsInBounds_some
    (h₁ : self.InBounds ctx) (h₃ : parent.InBounds ctx)
    (_heq : setParentWithCheck self ctx parent h₁ = some newCtx) :
    newCtx.spec.FieldsInBounds := by
  simp [setParentWithCheck_def, setParentWithCheckSim] at _heq ⊢
  grind

@[grind =>]
theorem Sim.OperationPtr.setParentWithCheck_inBounds (ptr : GenericPtr)
    h₁ h₂ (heq : setParentWithCheck self ctx parent h₁ h₂ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  simp [setParentWithCheck_def, setParentWithCheckSim] at heq ⊢
  grind

@[grind =>]
theorem Sim.OperationPtr.setParentWithCheck_veir_inBounds (ptr : Veir.GenericPtr)
    h₁ h₂ (heq : setParentWithCheck self ctx parent h₁ h₂ = some newCtx) :
    ptr.InBounds newCtx.spec ↔ ptr.InBounds ctx.spec := by
  simp [setParentWithCheck_def, setParentWithCheckSim] at heq ⊢
  grind

buffed --(inline := false)
def Sim.OperationPtr.linkBetweenWithParentSim (self: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (prevOp: Sim.OptionOperationPtr) (nextOp: Sim.OptionOperationPtr) (parent: Sim.BlockPtr)
    (selfIn: self.InBounds ctx := by grind)
    (prevIn: prevOp.InBounds ctx := by grind)
    (nextIn: nextOp.InBounds ctx := by grind)
    (parentIn : parent.InBounds ctx := by grind) : Option (IRContext OpInfo) :=
  let ctx := self.linkBetween ctx prevOp nextOp
  rlet ctx ← self.setParentWithCheck ctx parent (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind])
  match _ : prevOp.toOption with
    | none =>
      let ctx := parent.setFirstOp ctx self.toO (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind])
      match _ : nextOp.toOption with
      | none => parent.setLastOp ctx self.toO (by grind) (by grind)
      | some nextOp => ctx
    | some prevOp =>
      match _ : nextOp.toOption with
      | none => parent.setLastOp ctx self.toO (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind])
      | some nextOp => ctx

noncomputable def Sim.OperationPtr.linkBetweenWithParent! (self : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (prevOp : Sim.OptionOperationPtr) (nextOp : Sim.OptionOperationPtr)
    (parent : Sim.BlockPtr) : Option (Sim.IRContext OpInfo) :=
  let ctx := self.linkBetween! ctx prevOp nextOp
  rlet ctx ← self.setParentWithCheck! ctx parent
  match prevOp.toOption with
  | none =>
    let ctx := parent.setFirstOp! ctx self.toO
    match nextOp.toOption with
    | none => parent.setLastOp! ctx self.toO
    | some _ => ctx
  | some _ =>
    match nextOp.toOption with
    | none => parent.setLastOp! ctx self.toO
    | some _ => ctx

@[grind _=_, eq_bang ←]
theorem Sim.OperationPtr.linkBetweenWithParent!_eq_linkBetweenWithParent
    {self : Sim.OperationPtr}
    (selfIn : self.InBounds ctx) (prevIn : prevOp.InBounds ctx) (nextIn : nextOp.InBounds ctx) (parentIn : parent.InBounds ctx) :
    linkBetweenWithParent! self ctx prevOp nextOp parent =
    self.linkBetweenWithParent ctx prevOp nextOp parent selfIn prevIn nextIn parentIn := by
  simp [Sim.OperationPtr.linkBetweenWithParent_def, Sim.OperationPtr.linkBetweenWithParentSim, linkBetweenWithParent!]
  grind

@[grind .]
theorem Sim.OperationPtr.linkBetweenWithParent_inBounds (ptr : GenericPtr)
    (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  simp [linkBetweenWithParent_def, linkBetweenWithParentSim] at heq ⊢
  grind [generic_ptr_grind]

@[grind .]
theorem Sim.OperationPtr.linkBetweenWithParent_veir_inBounds (ptr : Veir.GenericPtr)
    (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx.spec ↔ ptr.InBounds ctx.spec := by
  simp [linkBetweenWithParent_def, linkBetweenWithParentSim] at heq ⊢
  grind [generic_ptr_grind]

@[grind .]
theorem Sim.OperationPtr.linkBetweenWithParent_fieldsInBounds (_hx : ctx.spec.FieldsInBounds)
    (_heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    newCtx.spec.FieldsInBounds := by
  simp [linkBetweenWithParent, linkBetweenWithParentSpec, linkBetweenWithParentSim] at _heq ⊢
  grind

/- Block linked list. -/
buffed
def Sim.BlockPtr.linkBetweenSim (self: BlockPtr) (ctx: IRContext OpInfo)
    (prevBlock: OptionBlockPtr) (nextBlock: OptionBlockPtr)
    (selfIn: self.InBounds ctx := by grind)
    (prevIn: prevBlock.InBounds ctx := by grind)
    (nextIn: nextBlock.InBounds ctx := by grind) : IRContext OpInfo :=
  let ctx := self.setPrevBlock ctx prevBlock (by grind) (by grind)
  let ctx := self.setNextBlock ctx nextBlock (by grind) (by grind)
  match _ : prevBlock.toOption with
  | none =>
    match _ : nextBlock.toOption with
    | none => ctx
    | some nextBlock => nextBlock.setPrevBlock ctx self.toO (by grind) (by grind)
  | some prevBlock =>
    let ctx := prevBlock.setNextBlock ctx self.toO (by grind) (by grind)
    match _ : nextBlock.toOption with
    | none => ctx
    | some nextBlock => nextBlock.setPrevBlock ctx self.toO (by grind) (by grind)

noncomputable
def Sim.BlockPtr.linkBetween! (self : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo)
    (prevBlock : Sim.OptionBlockPtr) (nextBlock : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  let ctx := self.setPrevBlock! ctx prevBlock
  let ctx := self.setNextBlock! ctx nextBlock
  match prevBlock.toOption with
  | none =>
    match nextBlock.toOption with
    | none => ctx
    | some nextBlock => nextBlock.setPrevBlock! ctx self.toO
  | some prevBlock =>
    let ctx := prevBlock.setNextBlock! ctx self.toO
    match nextBlock.toOption with
    | none => ctx
    | some nextBlock => nextBlock.setPrevBlock! ctx self.toO

@[grind _=_, eq_bang ←]
theorem Sim.BlockPtr.linkBetween!_eq_linkBetween {self : Sim.BlockPtr}
    (selfIn : self.InBounds ctx) (prevIn : prevBlock.InBounds ctx) (nextIn : nextBlock.InBounds ctx) :
    linkBetween! self ctx prevBlock nextBlock = self.linkBetween ctx prevBlock nextBlock selfIn prevIn nextIn := by
  simp [Sim.BlockPtr.linkBetween_def, Sim.BlockPtr.linkBetweenSim, linkBetween!]
  grind

@[grind =]
theorem Sim.BlockPtr.linkBetween_inBounds (ptr : GenericPtr) :
    ptr.InBounds (linkBetween self ctx prevBlock nextBlock h₁ h₂ h₃) ↔ ptr.InBounds ctx := by
  simp [linkBetween_def, linkBetweenSim]
  grind

@[grind =]
theorem Sim.BlockPtr.linkBetween_veir_inBounds (ptr : Veir.GenericPtr) :
    ptr.InBounds (linkBetween self ctx prevBlock nextBlock h₁ h₂ h₃).spec ↔ ptr.InBounds ctx.spec := by
  simp [linkBetween_def, linkBetweenSim]
  grind

@[grind .]
theorem Sim.BlockPtr.linkBetween_fieldsInBounds (_hx : ctx.spec.FieldsInBounds) :
    (linkBetween self ctx prevBlock nextBlock h₁ h₂ h₃).spec.FieldsInBounds := by
  simp [linkBetween_def, linkBetweenSim]
  grind (gen := 20)

/-- Set `self` parent to be `parent`. -/
buffed
def Sim.BlockPtr.setParentWithCheckSim (self: Sim.BlockPtr) (ctx: Sim.IRContext OpInfo) (parent: Sim.RegionPtr)
    (selfIn: self.InBounds ctx := by grind) (parentIb : parent.InBounds ctx := by grind) : Option (Sim.IRContext OpInfo) :=
  match (self.getParent ctx (by grind)).toOption with
  | some _ => none
  | none => self.setParent ctx parent.toO (by grind) (by grind [generic_ptr_grind])

noncomputable
def Sim.BlockPtr.setParentWithCheck! (self : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (parent : Sim.RegionPtr) :
    Option (Sim.IRContext OpInfo) :=
  match (self.getParent! ctx).toOption with
  | some _ => none
  | none => self.setParent! ctx parent.toO

@[grind _=_, eq_bang ←]
theorem Sim.BlockPtr.setParentWithCheck!_eq_setParentWithCheck {self : Sim.BlockPtr} (selfIn : self.InBounds ctx) :
    setParentWithCheck! self ctx parent = self.setParentWithCheck ctx parent selfIn parentSim := by
  simp [Sim.BlockPtr.setParentWithCheck_def, Sim.BlockPtr.setParentWithCheckSim, setParentWithCheck!]
  grind

@[grind .]
theorem Sim.BlockPtr.setParentWithCheck_fieldsInBounds
    (_h₁ : ctx.spec.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx) :
    (setParentWithCheck self ctx parent h₂ (by grind)).maybe₁ (·.spec.FieldsInBounds) := by
  simp [setParentWithCheck_def, setParentWithCheckSim]
  grind

@[grind =>]
theorem Sim.BlockPtr.setParentWithCheck_fieldsInBounds_some
    (_h₁ : ctx.spec.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx)
    (_heq : setParentWithCheck self ctx parent h₂ = some newCtx) :
    newCtx.spec.FieldsInBounds := by
  simp [setParentWithCheck_def, setParentWithCheckSim] at _heq ⊢
  grind

@[grind =>]
theorem Sim.BlockPtr.setParentWithCheck_inBounds (ptr : GenericPtr)
    (heq : setParentWithCheck self ctx parent h₁ h₂ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  simp [setParentWithCheck_def, setParentWithCheckSim] at heq ⊢
  grind

@[grind =>]
theorem Sim.BlockPtr.setParentWithCheck_veir_inBounds (ptr : Veir.GenericPtr)
    (heq : setParentWithCheck self ctx parent h₁ h₂ = some newCtx) :
    ptr.InBounds newCtx.spec ↔ ptr.InBounds ctx.spec := by
  simp [setParentWithCheck_def, setParentWithCheckSim] at heq ⊢
  grind

buffed
def Sim.BlockPtr.linkBetweenWithParentSim (self: BlockPtr) (ctx: IRContext OpInfo)
    (prevBlock: OptionBlockPtr) (nextBlock: OptionBlockPtr)
    (parent: RegionPtr) (selfIn: self.InBounds ctx := by grind)
    (prevIn: prevBlock.InBounds ctx := by grind)
    (nextIn: nextBlock.InBounds ctx := by grind)
    (parentIn : parent.InBounds ctx := by grind) : Option (IRContext OpInfo) :=
  let ctx := self.linkBetween ctx prevBlock nextBlock
  rlet ctx ← self.setParentWithCheck ctx parent (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind])
  match _ : prevBlock.toOption with
    | none =>
      let ctx := parent.setFirstBlock ctx self.toO (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind])
      match _ : nextBlock.toOption with
      | none =>
        let ctx := parent.setLastBlock ctx self.toO (by grind) (by grind)
        ctx
      | some nextBlock => ctx
    | some prevBlock =>
      match _ : nextBlock.toOption with
      | none => parent.setLastBlock ctx self.toO (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind])
      | some nextBlock => ctx

noncomputable
def Sim.BlockPtr.linkBetweenWithParent! (self : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo)
    (prevBlock : Sim.OptionBlockPtr) (nextBlock : Sim.OptionBlockPtr)
    (parent : Sim.RegionPtr) : Option (Sim.IRContext OpInfo) :=
  let ctx := self.linkBetween! ctx prevBlock nextBlock
  rlet ctx ← self.setParentWithCheck! ctx parent
  match prevBlock.toOption with
  | none =>
    let ctx := parent.setFirstBlock! ctx self.toO
    match nextBlock.toOption with
    | none => parent.setLastBlock! ctx self.toO
    | some _ => ctx
  | some _ =>
    match nextBlock.toOption with
    | none => parent.setLastBlock! ctx self.toO
    | some _ => ctx

@[grind _=_, eq_bang ←]
theorem Sim.BlockPtr.linkBetweenWithParent!_eq_linkBetweenWithParent
    {self : Sim.BlockPtr} {prevBlock : Sim.OptionBlockPtr} {nextBlock : Sim.OptionBlockPtr} {parent : Sim.RegionPtr}
    (selfIn : self.InBounds ctx)
    (prevIn : prevBlock.InBounds ctx)
    (nextIn : nextBlock.InBounds ctx)
    (parentIn : parent.InBounds ctx) :
    linkBetweenWithParent! self ctx prevBlock nextBlock parent =
    self.linkBetweenWithParent ctx prevBlock nextBlock parent selfIn prevIn nextIn parentIn := by
  simp [Sim.BlockPtr.linkBetweenWithParent_def, Sim.BlockPtr.linkBetweenWithParentSim, linkBetweenWithParent!]
  grind

@[grind .]
theorem Sim.BlockPtr.linkBetweenWithParent_veir_inBounds (ptr : Veir.GenericPtr)
    (heq : linkBetweenWithParent self ctx prevBlock nextBlock parent h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx.spec ↔ ptr.InBounds ctx.spec := by
  simp [linkBetweenWithParent_def, linkBetweenWithParentSim] at heq ⊢
  grind [generic_ptr_grind]

@[grind .]
theorem Sim.BlockPtr.linkBetweenWithParent_inBounds (ptr : GenericPtr)
    (heq : linkBetweenWithParent self ctx prevBlock nextBlock parent h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  simp [linkBetweenWithParent_def, linkBetweenWithParentSim] at heq ⊢
  grind [generic_ptr_grind]

@[grind .]
theorem Sim.BlockPtr.linkBetweenWithParent_fieldsInBounds (_hx : ctx.spec.FieldsInBounds)
    (_heq : linkBetweenWithParent self ctx prevBlock nextBlock parent h₁ h₂ h₃ h₄ = some newCtx) :
    newCtx.spec.FieldsInBounds := by
  simp [linkBetweenWithParent_def, linkBetweenWithParentSim] at _heq ⊢
  grind
