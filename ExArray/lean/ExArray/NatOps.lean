module

public import ExArray.Basic

/-!
# Nat-indexed shadow operations

Proof-only twins of `blit64`/`blit32`/`read64!`/`read32!` that take a `Nat` start address, so
that all address arithmetic in specifications lives in the linear fragment (no `UInt64`/`Int64`
additions). NEVER call these from executable code: they exist only to state and prove lemmas.
-/

public section

namespace ExArray

@[local grind =]
theorem toNat_ofNat_of_lt' {n : Nat} (h : n < UInt64.size) : (UInt64.ofNat n).toNat = n := by
  simp
  omega

/-- Proof-only `Nat`-indexed twin of `blit64`. NEVER use in executable code. -/
def blit64' (buf : ExArray) (n : Nat) (x : UInt64) (h : n + 8 ≤ buf.size) : ExArray :=
  buf.blit64 n.toUInt64 x (by grind)

/-- Proof-only `Nat`-indexed twin of `blit32`. NEVER use in executable code. -/
def blit32' (buf : ExArray) (n : Nat) (x : UInt32) (h : n + 4 ≤ buf.size) : ExArray :=
  buf.blit32 n.toUInt64 x (by grind)

/-- Proof-only `Nat`-indexed twin of `read64!`. NEVER use in executable code. -/
def read64' (buf : ExArray) (n : Nat) : UInt64 :=
  buf.read64! n.toUInt64

/-- Proof-only `Nat`-indexed twin of `read32!`. NEVER use in executable code. -/
def read32' (buf : ExArray) (n : Nat) : UInt32 :=
  buf.read32! n.toUInt64

/-! ## Equivalence with the `UInt64`-indexed operations -/

theorem blit64_eq_blit64' (buf : ExArray) (n : UInt64) (x : UInt64) h
    (h' : n.toNat + 8 ≤ buf.size) :
    buf.blit64 n x h = buf.blit64' n.toNat x h' := by
  unfold blit64'
  congr 1
  grind [UInt64.ofNat_toNat]

theorem blit32_eq_blit32' (buf : ExArray) (n : UInt64) (x : UInt32) h
    (h' : n.toNat + 4 ≤ buf.size) :
    buf.blit32 n x h = buf.blit32' n.toNat x h' := by
  unfold blit32'
  congr 1
  grind [UInt64.ofNat_toNat]

theorem read64!_eq_read64' (buf : ExArray) (n : UInt64) :
    buf.read64! n = buf.read64' n.toNat := by
  unfold read64'
  congr 1
  grind [UInt64.ofNat_toNat]

theorem read32!_eq_read32' (buf : ExArray) (n : UInt64) :
    buf.read32! n = buf.read32' n.toNat := by
  unfold read32'
  congr 1
  grind [UInt64.ofNat_toNat]

/-! ## Size preservation -/

@[simp]
theorem blit64'_size (buf : ExArray) (n : Nat) (x : UInt64) h :
    (buf.blit64' n x h).size = buf.size := by
  unfold blit64'
  simp

@[simp]
theorem blit32'_size (buf : ExArray) (n : Nat) (x : UInt32) h :
    (buf.blit32' n x h).size = buf.size := by
  unfold blit32'
  simp

/-! ## Read-after-write lemmas, in the linear fragment -/

theorem read64'_blit64'_self (buf : ExArray) (n : Nat) (x : UInt64) h :
    (buf.blit64' n x h).read64' n = x := by
  unfold blit64' read64'
  grind

theorem read32'_blit32'_self (buf : ExArray) (n : Nat) (x : UInt32) h :
    (buf.blit32' n x h).read32' n = x := by
  unfold blit32' read32'
  grind

theorem read64'_blit64'_disjoint (buf : ExArray) (n m : Nat) (x : UInt64) h
    (hn : n + 8 ≤ buf.size) (hd : n + 8 ≤ m ∨ m + 8 ≤ n) :
    (buf.blit64' m x h).read64' n = buf.read64' n := by
  unfold blit64' read64'
  apply read64!_blit64_disjoint
  grind

theorem read64'_blit32'_disjoint (buf : ExArray) (n m : Nat) (x : UInt32) h
    (hn : n + 8 ≤ buf.size) (hd : n + 8 ≤ m ∨ m + 4 ≤ n) :
    (buf.blit32' m x h).read64' n = buf.read64' n := by
  unfold blit32' read64'
  apply read64!_blit32_disjoint
  grind

theorem read32'_blit64'_disjoint (buf : ExArray) (n m : Nat) (x : UInt64) h
    (hn : n + 4 ≤ buf.size) (hd : n + 4 ≤ m ∨ m + 8 ≤ n) :
    (buf.blit64' m x h).read32' n = buf.read32' n := by
  unfold blit64' read32'
  apply read32!_blit64_disjoint
  grind

theorem read32'_blit32'_disjoint (buf : ExArray) (n m : Nat) (x : UInt32) h
    (hn : n + 4 ≤ buf.size) (hd : n + 4 ≤ m ∨ m + 4 ≤ n) :
    (buf.blit32' m x h).read32' n = buf.read32' n := by
  unfold blit32' read32'
  apply read32!_blit32_disjoint
  grind

end ExArray
