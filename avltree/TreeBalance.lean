import avltree.TreeBase

open TreeBase_n

namespace TreeBalance_n

/--
Compute the balance factor of a binary tree.
-/
def balanceFactor : BinaryTree → Int
  | BinaryTree.nil => 0
  | BinaryTree.node left right => Int.ofNat (height left) - Int.ofNat (height right)


/--
AVL balance condition.
-/
def isAVL : BinaryTree → Bool
  | BinaryTree.nil => true
  | BinaryTree.node left right =>
    let bf := balanceFactor (BinaryTree.node left right)
    bf ≥ -1 ∧ bf ≤ 1 ∧ isAVL left ∧ isAVL right















end TreeBalance_n
