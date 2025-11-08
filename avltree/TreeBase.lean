namespace TreeBase_n

/-- Binary Tree Definition

  V
 / \
L   R

--/
inductive BinaryTree where
  | nil : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree
deriving Repr

/-- Compute the depth of a binary tree. -/
def height : BinaryTree → Nat
  | BinaryTree.nil => 0
  | BinaryTree.node left right => 1 + max (height left) (height right)

/-- Compute the size of a binary tree. -/
def size : BinaryTree → Nat
  | BinaryTree.nil => 1
  | BinaryTree.node left right => 1 + size left + size right


@[simp] theorem height_leaf : height BinaryTree.nil = 0 := rfl

@[simp] theorem size_leaf : size BinaryTree.nil = 1 := rfl

/--
Retrieve the left child of a binary tree.
-/
def leftChild : BinaryTree → BinaryTree
  | BinaryTree.nil => BinaryTree.nil
  | BinaryTree.node left _ => left

/--
Retrieve the right child of a binary tree.
-/
def rightChild : BinaryTree → BinaryTree
  | BinaryTree.nil => BinaryTree.nil
  | BinaryTree.node _ right => right

/--
Check if a binary tree is a leaf.
-/
@[simp] def isLeaf : BinaryTree → Bool
  | BinaryTree.nil => true
  | BinaryTree.node _ _ => false

theorem size_node_leaf : ∀ node, isLeaf node → size node = 1 := by
  intro node
  cases node
  · intro h
    exact size_leaf
  · intro h
    contradiction

theorem size_node_non_leaf : ∀ node, ¬ isLeaf node → size node = 1 + size (leftChild node) + size (rightChild node) := by
  intro node
  cases node
  · intro h
    contradiction
  · intro h
    rfl


end TreeBase_n
