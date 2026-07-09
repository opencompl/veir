import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

-- (X << Z) & (Y << Z) → (X & Y) << Z
-- The created `shl` drops `nsw` (`X & Y` can have a sign-changing bit pattern where `Y`
-- does not) but may keep `nuw`, since the bits it shifts out are a subset of `Y`'s.
set_option warn.sorry false in
def AndShlShl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchShl dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchShl dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .shl) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { nsw := false, nuw := p1.nuw } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X << Z) | (Y << Z) → (X | Y) << Z
-- The created `shl` drops `nsw` and `nuw` (the bits `X | Y` shifts out can come from `X`
-- alone), and the created `or` drops `disjoint` (`X` and `Y` may overlap only in bits
-- that both shifts discard).
set_option warn.sorry false in
def OrShlShl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchShl dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchShl dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .shl) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X << Z) ^ (Y << Z) → (X ^ Y) << Z
-- The created `shl` drops `nsw` and `nuw`, as in `OrShlShl`.
set_option warn.sorry false in
def XorShlShl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchShl dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchShl dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .shl) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) & (Y >> Z) → (X & Y) >> Z   (logical)
set_option warn.sorry false in
def AndLshrLshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchLshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchLshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) | (Y >> Z) → (X | Y) >> Z   (logical)
-- The created `lshr` drops `exact` (the low bits `X | Y` discards can be nonzero because
-- of `X` alone), and the created `or` drops `disjoint` (`X` and `Y` may overlap only in
-- the discarded low bits).
set_option warn.sorry false in
def OrLshrLshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchLshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchLshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { exact := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z   (logical)
-- The created `lshr` drops `exact`, as in `OrLshrLshr`.
set_option warn.sorry false in
def XorLshrLshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchLshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchLshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { exact := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) & (Y >> Z) → (X & Y) >> Z   (arithmetic)
set_option warn.sorry false in
def AndAshrAshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchAshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchAshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .ashr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) | (Y >> Z) → (X | Y) >> Z   (arithmetic)
-- The created `ashr` drops `exact` and the created `or` drops `disjoint`, as in
-- `OrLshrLshr`.
set_option warn.sorry false in
def OrAshrAshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchAshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchAshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .ashr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { exact := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z   (arithmetic)
-- The created `ashr` drops `exact`, as in `XorLshrLshr`.
set_option warn.sorry false in
def XorAshrAshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchAshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchAshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .ashr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { exact := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X & Z) & (Y & Z) → (X & Y) & Z
set_option warn.sorry false in
def AndAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _) := matchAnd dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _) := matchAnd dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X & Z) | (Y & Z) → (X | Y) & Z
-- The created `or` drops `disjoint`: `X` and `Y` may overlap only in bits that `Z` masks
-- off, so `(X & Z)` and `(Y & Z)` can be disjoint while `X` and `Y` are not.
set_option warn.sorry false in
def OrAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _) := matchAnd dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _) := matchAnd dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X & Z) ^ (Y & Z) → (X ^ Y) & Z
set_option warn.sorry false in
def XorAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _) := matchAnd dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _) := matchAnd dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry
