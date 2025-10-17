
/--
  A binary tree is a tree data structure in which each node has at most two children,
  which are referred to as the left child and the right child.
-/
inductive BinaryTree (α : Type) where
  | leaf : BinaryTree α
  | node (left : BinaryTree α) (right : BinaryTree α)

/--
  By definition, the depth of a binary tree is the number
  of edges on the longest path from the root to a leaf.
-/
def depth (tree : BinaryTree α) : Nat :=
  match tree with
  | .leaf => 0
  | .node l r => 1 + max (depth l) (depth r)


/--
  By definition, a binary tree is balancedif the height of
  the left and right subtrees of any node differ by at most 1.
-/
def isBalanced (tree : BinaryTree α) : Bool :=
  match tree with
  | .leaf => true
  | .node l r => Int.natAbs (depth l - depth r) <= 1
