
namespace BinaryTree_n

/-- Binary Tree Definition

  V
 / \
L   R

--/
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → Nat → BinaryTree → BinaryTree


/-- Compute the depth of a binary tree. -/
def depth : BinaryTree → Nat
  | BinaryTree.leaf => 0
  | BinaryTree.node left _ right => 1 + max (depth left) (depth right)

/-- Compute the size of a binary tree. -/
def size : BinaryTree → Nat
  | BinaryTree.leaf => 1
  | BinaryTree.node left _ right => 1 + size left + size right

@[simp]
theorem depth_leaf : depth BinaryTree.leaf = 0 := rfl

@[simp]
theorem size_leaf : size BinaryTree.leaf = 1 := rfl

/--
Retrieve the left child of a binary tree.
-/
def leftChild : BinaryTree → BinaryTree
  | BinaryTree.leaf => BinaryTree.leaf
  | BinaryTree.node left _ _ => left

/--
Retrieve the right child of a binary tree.
-/
def rightChild : BinaryTree → BinaryTree
  | BinaryTree.leaf => BinaryTree.leaf
  | BinaryTree.node _ _ right => right

/--
Check if a binary tree is a leaf.
-/
def isLeaf : BinaryTree → Bool
  | BinaryTree.leaf => true
  | BinaryTree.node _ _ _ => false

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
    exact rfl

end BinaryTree_n
