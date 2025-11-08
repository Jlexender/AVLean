import avltree.TreeBase

open TreeBase_n

namespace TreeBalance_n

/--
Compute the balance factor of a binary tree.
-/
@[simp]
def balanceFactor : BinaryTree → Int
  | BinaryTree.nil => 0
  | BinaryTree.node left right => Int.ofNat (height left) - Int.ofNat (height right)


/--
AVL balance condition.
-/
@[simp]
def isAVL : BinaryTree → Bool
  | BinaryTree.nil => true
  | BinaryTree.node left right =>
    let bf := balanceFactor (BinaryTree.node left right)
    bf ≥ -1 ∧ bf ≤ 1 ∧ isAVL left ∧ isAVL right


/--
For any binary tree T, max(size T) = 2^(height T) - 1.
-/
theorem max_size_eq : ∀ tree : BinaryTree, size tree < 2 ^ (height tree + 1) := by
  sorry


/--
We state that h(AvlTree) = O(log(size(AvlTree))).
I.e., ∃ C, ∀ t : AvlTree, height t ≤ C * log(size t).
I.e., size t ≥ C ^ (height t).
-/
theorem height_size_pow_bound :
  ∃ C : Nat, ∀ t : BinaryTree, isAVL t → Nat.pow C (height t) ≤ size t := by
  sorry












end TreeBalance_n
