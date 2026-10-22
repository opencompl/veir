import Veir.InstSimplify.MiscSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS5681
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Integer constant cast folding, preserving upstream numeric result despite source flags. -/
def fold_trunc (src dst : TypeAttr) (p : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType w := src.val | none
  let .integerType n := dst.val | none
  let .integer a := p.value | none
  let v := (BitVec.ofInt w.bitwidth a.value).truncate n.bitwidth
  return {value := .integer {type := n, value := v.toInt}}
def trunc : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[src]
    MatchProg.matchNative (src,dst) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => n.bitwidth < w.bitwidth
      | _,_ => false)
    let _ ← MatchProg.root (.llvm .trunc) a.res #[dst]
    return (src,dst,a.properties))
  (fun (src,dst,a) => do
    let p ← CreateProg.applyNative (src,dst,a) (fun (src,dst,a) => fold_trunc src dst a)
    CreateProg.operation (.llvm .mlir__constant) #[] #[dst] p)
  (fun r => r)
theorem trunc_valid : Pattern.Valid trunc := by
  simp only [trunc]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hw
  have hw : n < w := by simpa [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hw
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ _ _ ai
  obtain rfl := (misc_trunc_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ri
  simp only [fold_trunc,TypeAttr.of_val,Attribute.of,ha]
  dsimp only [pure,Pure.pure]
  refine ⟨.int n (.val ((BitVec.ofInt w a.value).truncate n)), ?_, ?_⟩
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp only [LLVM.Int.trunc, Id.run, pure]
    repeat' split
    all_goals simp_all [RuntimeValue.isRefinedBy, isRefinedBy]

/-- Integer constant cast folding, preserving upstream numeric result despite source flags. -/
def fold_zext (src dst : TypeAttr) (p : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType w := src.val | none
  let .integerType n := dst.val | none
  let .integer a := p.value | none
  let v := (BitVec.ofInt w.bitwidth a.value).zeroExtend n.bitwidth
  return {value := .integer {type := n, value := v.toInt}}
def zext : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[src]
    MatchProg.matchNative (src,dst) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => w.bitwidth < n.bitwidth
      | _,_ => false)
    let _ ← MatchProg.root (.llvm .zext) a.res #[dst]
    return (src,dst,a.properties))
  (fun (src,dst,a) => do
    let p ← CreateProg.applyNative (src,dst,a) (fun (src,dst,a) => fold_zext src dst a)
    CreateProg.operation (.llvm .mlir__constant) #[] #[dst] p)
  (fun r => r)
theorem zext_valid : Pattern.Valid zext := by
  simp only [zext]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hw
  have hw : w < n := by simpa [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hw
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ _ _ ai
  obtain rfl := (misc_zext_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ri
  simp only [fold_zext,TypeAttr.of_val,Attribute.of,ha]
  dsimp only [pure,Pure.pure]
  refine ⟨.int n (.val ((BitVec.ofInt w a.value).zeroExtend n)), ?_, ?_⟩
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp only [LLVM.Int.zext, Id.run, pure]
    repeat' split
    all_goals simp_all [RuntimeValue.isRefinedBy, isRefinedBy]

/-- Integer constant cast folding, preserving upstream numeric result despite source flags. -/
def fold_sext (src dst : TypeAttr) (p : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType w := src.val | none
  let .integerType n := dst.val | none
  let .integer a := p.value | none
  let v := (BitVec.ofInt w.bitwidth a.value).signExtend n.bitwidth
  return {value := .integer {type := n, value := v.toInt}}
def sext : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[src]
    MatchProg.matchNative (src,dst) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => w.bitwidth < n.bitwidth
      | _,_ => false)
    let _ ← MatchProg.root (.llvm .sext) a.res #[dst]
    return (src,dst,a.properties))
  (fun (src,dst,a) => do
    let p ← CreateProg.applyNative (src,dst,a) (fun (src,dst,a) => fold_sext src dst a)
    CreateProg.operation (.llvm .mlir__constant) #[] #[dst] p)
  (fun r => r)
theorem sext_valid : Pattern.Valid sext := by
  simp only [sext]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hw
  have hw : w < n := by simpa [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hw
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ _ _ ai
  obtain rfl := (sext_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ri
  simp only [fold_sext,TypeAttr.of_val,Attribute.of,ha]
  dsimp only [pure,Pure.pure]
  refine ⟨.int n (.val ((BitVec.ofInt w a.value).signExtend n)), ?_, ?_⟩
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp only [LLVM.Int.sext, Id.run, pure]
    repeat' split
    all_goals simp_all [RuntimeValue.isRefinedBy, isRefinedBy]

def bitcast : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let _ ← MatchProg.root (.llvm .bitcast) a.res #[ty]
    return a.res[0]!)
  pure (fun x => x)
theorem bitcast_valid : Pattern.Valid bitcast := by
  simp only [bitcast]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai rp rv ri
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ _ _ ai
  obtain rfl := misc_bitcast_int_eq _ _ _ _ ri
  exact RuntimeValue.isRefinedBy_refl _

def ptrtoint_null : Pattern OpCode := Pattern.Builder
  (do
    let pty ← MatchProg.type (Attr := LLVM.PointerType) (fun _ => true)
    let ity ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
    let z ← MatchProg.operation (.llvm .mlir__zero) #[] #[pty]
    let _ ← MatchProg.root (.llvm .ptrtoint) z.res #[ity]
    return ity)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let z ← CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p
    return z.res[0]!) (fun x => x)
theorem ptrtoint_null_valid : Pattern.Valid ptrtoint_null := by
  simp only [ptrtoint_null]
  provePuddleValid
  rintro ⟨⟩ _ ⟨w,s⟩ rfl hw zp zv zi rp rv ri
  have : w = 64 := by simpa using hw
  subst w
  have he := zi.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  change Interp.ok (#[.addr LLVM.Ptr.null], MemoryState.empty, none) = Interp.ok (#[zv], MemoryState.empty, none) at he
  have hz : zv = .addr LLVM.Ptr.null := by simpa using he.symm
  subst zv
  have he := ri.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp [LLVM.Ptr.null, LLVM.Ptr.toInt, Pointer.null] at he
  obtain rfl : rv = .int 64 (.val 0) := he.symm
  refine ⟨.int 64 (.val 0), ?_, ?_⟩
  · exact (zero_iff _ _ _).mpr rfl
  · exact RuntimeValue.isRefinedBy_refl _

def trunc_zero : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__zero) #[] #[src]
    MatchProg.matchNative (src,dst) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => n.bitwidth < w.bitwidth
      | _,_ => false)
    let _ ← MatchProg.root (.llvm .trunc) a.res #[dst]
    return dst)
  (fun dst => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let r ← CreateProg.operation (.llvm .mlir__zero) #[] #[dst] p
    return r.res[0]!) (fun r => r)
theorem trunc_zero_valid : Pattern.Valid trunc_zero := by
  simp only [trunc_zero]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hw
  have hw : n < w := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hw
  obtain rfl := (zero_iff _ _ _).mp ai
  obtain rfl := (misc_trunc_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ri
  refine ⟨.int n (.val 0), ?_, ?_⟩
  · exact (zero_iff _ _ _).mpr rfl
  · simp [LLVM.Int.trunc,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,BitVec.signExtend]

def trunc_poison : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__poison) #[] #[src]
    MatchProg.matchNative (src,dst) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => n.bitwidth < w.bitwidth
      | _,_ => false)
    let _ ← MatchProg.root (.llvm .trunc) a.res #[dst]
    return dst)
  (fun dst => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    let r ← CreateProg.operation (.llvm .mlir__poison) #[] #[dst] p
    return r.res[0]!) (fun r => r)
theorem trunc_poison_valid : Pattern.Valid trunc_poison := by
  simp only [trunc_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hw
  have hw : n < w := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hw
  obtain rfl := (poison_iff _ _ _).mp ai
  obtain rfl := (misc_trunc_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ri
  refine ⟨.int n .poison, ?_, ?_⟩
  · exact (poison_iff _ _ _).mpr rfl
  · simp [LLVM.Int.trunc,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,BitVec.signExtend]

def zext_zero : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__zero) #[] #[src]
    MatchProg.matchNative (src,dst) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => w.bitwidth < n.bitwidth
      | _,_ => false)
    let _ ← MatchProg.root (.llvm .zext) a.res #[dst]
    return dst)
  (fun dst => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let r ← CreateProg.operation (.llvm .mlir__zero) #[] #[dst] p
    return r.res[0]!) (fun r => r)
theorem zext_zero_valid : Pattern.Valid zext_zero := by
  simp only [zext_zero]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hw
  have hw : w < n := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hw
  obtain rfl := (zero_iff _ _ _).mp ai
  obtain rfl := (misc_zext_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ri
  refine ⟨.int n (.val 0), ?_, ?_⟩
  · exact (zero_iff _ _ _).mpr rfl
  · simp [LLVM.Int.zext,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,BitVec.signExtend]

def zext_poison : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__poison) #[] #[src]
    MatchProg.matchNative (src,dst) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => w.bitwidth < n.bitwidth
      | _,_ => false)
    let _ ← MatchProg.root (.llvm .zext) a.res #[dst]
    return dst)
  (fun dst => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    let r ← CreateProg.operation (.llvm .mlir__poison) #[] #[dst] p
    return r.res[0]!) (fun r => r)
theorem zext_poison_valid : Pattern.Valid zext_poison := by
  simp only [zext_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hw
  have hw : w < n := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hw
  obtain rfl := (poison_iff _ _ _).mp ai
  obtain rfl := (misc_zext_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ri
  refine ⟨.int n .poison, ?_, ?_⟩
  · exact (poison_iff _ _ _).mpr rfl
  · simp [LLVM.Int.zext,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,BitVec.signExtend]

def sext_zero : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__zero) #[] #[src]
    MatchProg.matchNative (src,dst) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => w.bitwidth < n.bitwidth
      | _,_ => false)
    let _ ← MatchProg.root (.llvm .sext) a.res #[dst]
    return dst)
  (fun dst => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let r ← CreateProg.operation (.llvm .mlir__zero) #[] #[dst] p
    return r.res[0]!) (fun r => r)
theorem sext_zero_valid : Pattern.Valid sext_zero := by
  simp only [sext_zero]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hw
  have hw : w < n := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hw
  obtain rfl := (zero_iff _ _ _).mp ai
  obtain rfl := (sext_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ri
  refine ⟨.int n (.val 0), ?_, ?_⟩
  · exact (zero_iff _ _ _).mpr rfl
  · simp [LLVM.Int.sext,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,BitVec.signExtend]

def sext_poison : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__poison) #[] #[src]
    MatchProg.matchNative (src,dst) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => w.bitwidth < n.bitwidth
      | _,_ => false)
    let _ ← MatchProg.root (.llvm .sext) a.res #[dst]
    return dst)
  (fun dst => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    let r ← CreateProg.operation (.llvm .mlir__poison) #[] #[dst] p
    return r.res[0]!) (fun r => r)
theorem sext_poison_valid : Pattern.Valid sext_poison := by
  simp only [sext_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hw
  have hw : w < n := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hw
  obtain rfl := (poison_iff _ _ _).mp ai
  obtain rfl := (sext_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ri
  refine ⟨.int n .poison, ?_, ?_⟩
  · exact (poison_iff _ _ _).mpr rfl
  · simp [LLVM.Int.sext,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,BitVec.signExtend]

def bitcast_int_zero : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.operation (.llvm .mlir__zero) #[] #[ty]
    let _ ← MatchProg.root (.llvm .bitcast) x.res #[ty]
    return x.res[0]!) pure (fun x => x)
theorem bitcast_int_zero_valid : Pattern.Valid bitcast_int_zero := by
  simp only [bitcast_int_zero]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai rp rv ri
  obtain rfl := (zero_iff _ _ _).mp ai
  obtain rfl := misc_bitcast_int_eq _ _ _ _ ri
  exact RuntimeValue.isRefinedBy_refl _

def bitcast_int_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .bitcast) x.res #[ty]
    return x.res[0]!) pure (fun x => x)
theorem bitcast_int_poison_valid : Pattern.Valid bitcast_int_poison := by
  simp only [bitcast_int_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai rp rv ri
  obtain rfl := (poison_iff _ _ _).mp ai
  obtain rfl := misc_bitcast_int_eq _ _ _ _ ri
  exact RuntimeValue.isRefinedBy_refl _

def bitcast_ptr_zero : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType) (fun _ => true)
    let x ← MatchProg.operation (.llvm .mlir__zero) #[] #[ty]
    let _ ← MatchProg.root (.llvm .bitcast) x.res #[ty]
    return x.res[0]!) pure (fun x => x)
theorem bitcast_ptr_zero_valid : Pattern.Valid bitcast_ptr_zero := by
  simp only [bitcast_ptr_zero]
  provePuddleValid
  rintro ⟨⟩ ap av ai rp rv ri
  have he := ai.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  change Interp.ok (#[.addr LLVM.Ptr.null], MemoryState.empty, none) = Interp.ok (#[av], MemoryState.empty, none) at he
  have hv : av = .addr LLVM.Ptr.null := by simpa using he.symm
  subst av
  obtain rfl := misc_bitcast_ptr_eq _ _ _ ri
  exact RuntimeValue.isRefinedBy_refl _

def bitcast_ptr_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType) (fun _ => true)
    let x ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .bitcast) x.res #[ty]
    return x.res[0]!) pure (fun x => x)
theorem bitcast_ptr_poison_valid : Pattern.Valid bitcast_ptr_poison := by
  simp only [bitcast_ptr_poison]
  provePuddleValid
  rintro ⟨⟩ ap av ai rp rv ri
  have he := ai.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  change Interp.ok (#[.addr LLVM.Ptr.poison], MemoryState.empty, none) = Interp.ok (#[av], MemoryState.empty, none) at he
  have hv : av = .addr LLVM.Ptr.poison := by simpa using he.symm
  subst av
  obtain rfl := misc_bitcast_ptr_eq _ _ _ ri
  exact RuntimeValue.isRefinedBy_refl _

def inttoptr_poison : Pattern OpCode := Pattern.Builder
  (do
    let ity ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
    let pty ← MatchProg.type (Attr := LLVM.PointerType) (fun _ => true)
    let z ← MatchProg.operation (.llvm .mlir__poison) #[] #[ity]
    let _ ← MatchProg.root (.llvm .inttoptr) z.res #[pty]
    return pty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    let z ← CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p
    return z.res[0]!) (fun x => x)
theorem inttoptr_poison_valid : Pattern.Valid inttoptr_poison := by
  simp only [inttoptr_poison]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hw ⟨⟩ zp zv zi rp rv ri
  have hw : w = 64 := by simpa using hw
  subst w
  obtain rfl := (poison_iff _ _ _).mp zi
  have he := ri.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp [MemoryState.ptrFromInt] at he
  obtain rfl : rv = .addr .poison := by simpa using he.symm
  refine ⟨.addr .poison, ?_, RuntimeValue.isRefinedBy_refl _⟩
  refine ⟨?_, ?_⟩
  · constructor
    · rfl
    · intro i hi
      have hi : i < 1 := hi
      have : i = 0 := by omega
      subst i
      trivial
  · intro memory; rfl

def ptrtoint_poison : Pattern OpCode := Pattern.Builder
  (do
    let pty ← MatchProg.type (Attr := LLVM.PointerType) (fun _ => true)
    let ity ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
    let z ← MatchProg.operation (.llvm .mlir__poison) #[] #[pty]
    let _ ← MatchProg.root (.llvm .ptrtoint) z.res #[ity]
    return ity)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    let z ← CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p
    return z.res[0]!) (fun x => x)
theorem ptrtoint_poison_valid : Pattern.Valid ptrtoint_poison := by
  simp only [ptrtoint_poison]
  provePuddleValid
  rintro ⟨⟩ _ ⟨w,s⟩ rfl hw zp zv zi rp rv ri
  have hw : w = 64 := by simpa using hw
  subst w
  have he := zi.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  change Interp.ok (#[.addr .poison], MemoryState.empty, none) = Interp.ok (#[zv], MemoryState.empty, none) at he
  have hz : zv = .addr .poison := by simpa using he.symm
  subst zv
  have he := ri.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp [LLVM.Ptr.toInt] at he
  obtain rfl : rv = .int 64 .poison := by simpa using he.symm
  refine ⟨.int 64 .poison, ?_, RuntimeValue.isRefinedBy_refl _⟩
  exact (poison_iff _ _ _).mpr rfl

def fold_bitcast_integer (dst : TypeAttr) (p : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType n := dst.val | none
  let .integer a := p.value | none
  return { value := .integer {type := n, value := (BitVec.ofInt n.bitwidth a.value).toInt} }
def bitcast_integer : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    MatchProg.matchNative (src,dst) (fun (a,b) => match a.val,b.val with
      | .integerType a,.integerType b => a.bitwidth == b.bitwidth
      | _,_ => false)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[src]
    let _ ← MatchProg.root (.llvm .bitcast) a.res #[dst]
    return (dst,a.properties))
  (fun (dst,a) => do
    let p ← CreateProg.applyNative (dst,a) (fun (dst,a) => fold_bitcast_integer dst a)
    CreateProg.operation (.llvm .mlir__constant) #[] #[dst] p) (fun r => r)
theorem bitcast_integer_valid : Pattern.Valid bitcast_integer := by
  simp only [bitcast_integer]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hn
  have hn : w = n := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hn
  subst n
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ _ _ ai
  obtain rfl := misc_bitcast_int_eq ⟨w,ns⟩ _ _ _ ri
  simp only [fold_bitcast_integer,TypeAttr.of_val,Attribute.of,ha]
  dsimp only [pure,Pure.pure]
  refine ⟨.int w (.val (BitVec.ofInt w a.value)), ?_, RuntimeValue.isRefinedBy_refl _⟩
  exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])

def bitcast_integer_zero : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    MatchProg.matchNative (src,dst) (fun (a,b) => match a.val,b.val with
      | .integerType a,.integerType b => a.bitwidth == b.bitwidth
      | _,_ => false)
    let a ← MatchProg.operation (.llvm .mlir__zero) #[] #[src]
    let _ ← MatchProg.root (.llvm .bitcast) a.res #[dst]
    return dst)
  (fun dst => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let a ← CreateProg.operation (.llvm .mlir__zero) #[] #[dst] p
    return a.res[0]!) (fun r => r)
theorem bitcast_integer_zero_valid : Pattern.Valid bitcast_integer_zero := by
  simp only [bitcast_integer_zero]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hn
  have hn : w = n := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hn
  subst n
  obtain rfl := (zero_iff _ _ _).mp ai
  obtain rfl := misc_bitcast_int_eq ⟨w,ns⟩ _ _ _ ri
  refine ⟨.int w (.val 0), ?_, RuntimeValue.isRefinedBy_refl _⟩
  exact (zero_iff _ _ _).mpr rfl

def bitcast_integer_poison : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let dst ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    MatchProg.matchNative (src,dst) (fun (a,b) => match a.val,b.val with
      | .integerType a,.integerType b => a.bitwidth == b.bitwidth
      | _,_ => false)
    let a ← MatchProg.operation (.llvm .mlir__poison) #[] #[src]
    let _ ← MatchProg.root (.llvm .bitcast) a.res #[dst]
    return dst)
  (fun dst => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    let a ← CreateProg.operation (.llvm .mlir__poison) #[] #[dst] p
    return a.res[0]!) (fun r => r)
theorem bitcast_integer_poison_valid : Pattern.Valid bitcast_integer_poison := by
  simp only [bitcast_integer_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩ ap av ai rp rv ri hn
  have hn : w = n := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hn
  subst n
  obtain rfl := (poison_iff _ _ _).mp ai
  obtain rfl := misc_bitcast_int_eq ⟨w,ns⟩ _ _ _ ri
  refine ⟨.int w .poison, ?_, RuntimeValue.isRefinedBy_refl _⟩
  exact (poison_iff _ _ _).mpr rfl
end Veir.InstSimplify.IS5681
