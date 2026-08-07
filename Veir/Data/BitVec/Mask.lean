module
/-! # Masks as bitvector variables constrained by `m &&& (m + 1) = 0`. -/

public section

namespace Veir.Data.BitVec

/-- `maskOfWidth o w : BitVec o` has its low `w` bits set and all higher bits clear. -/
def maskOfWidth (o w : Nat) : BitVec o := BitVec.ofNat o (2 ^ w - 1)

/-- `m.IsMask` holds when `m = 2^k - 1` for some `k`; the only fact the bitblaster gets about a
width. -/
def IsMask {o : Nat} (m : BitVec o) : Prop := m &&& (m + 1#o) = 0#o
