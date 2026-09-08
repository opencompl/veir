import Veir.Meta.Deriving

namespace DerivingTest

mutual
inductive Tree (α : Type) where
  | leaf (value : α)
  | branch (children : Forest α)

structure Forest (α : Type) where
  trees : Array (Tree α)
end

structure Label (α : Type) where
  value : α

/-! Positive test cases. -/

derive_mutual_repr for Forest, Tree
derive_mutual_hashable for Forest, Tree

example : Repr (Tree Nat) := inferInstance
example : Repr (Forest Nat) := inferInstance
example : Hashable (Tree Nat) := inferInstance
example : Hashable (Forest Nat) := inferInstance

#guard reprStr (Tree.branch ⟨#[.leaf 7]⟩ : Tree Nat) ==
  "DerivingTest.Tree.branch { trees := #[DerivingTest.Tree.leaf 7] }"

/-! Types outside the mutual group are rejected. -/

/-- error: DerivingTest.Label is not in the mutual group of DerivingTest.Forest -/
#guard_msgs in
derive_mutual_repr for Forest, Label, Tree

/-- error: DerivingTest.Forest is not in the mutual group of DerivingTest.Label -/
#guard_msgs in
derive_mutual_repr for Label, Forest, Tree

/-- error: DerivingTest.Label is not in the mutual group of DerivingTest.Forest -/
#guard_msgs in
derive_mutual_hashable for Forest, Label, Tree

/-- error: DerivingTest.Forest is not in the mutual group of DerivingTest.Label -/
#guard_msgs in
derive_mutual_hashable for Label, Forest, Tree
