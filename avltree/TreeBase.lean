namespace TreeBase_n

/-- Binary Tree Definition

  V
 / \
L   R

--/
inductive BinaryTree where
  | nil : BinaryTree
  | node : BinaryTree → Nat → BinaryTree → BinaryTree
deriving Repr

/-- Compute the depth of a binary tree. -/
@[simp]
def height : BinaryTree → Nat
  | BinaryTree.nil => 0
  | BinaryTree.node left _ right => 1 + max (height left) (height right)

/-- Compute the size of a binary tree. -/
@[simp]
def size : BinaryTree → Nat
  | BinaryTree.nil => 1
  | BinaryTree.node left _ right => 1 + size left + size right


@[simp]
theorem height_leaf : height BinaryTree.nil = 0 := rfl

@[simp]
theorem size_leaf : size BinaryTree.nil = 1 := rfl

/--
Retrieve the left child of a binary tree.
-/
def leftChild : BinaryTree → BinaryTree
  | BinaryTree.nil => BinaryTree.nil
  | BinaryTree.node left _ _ => left

/--
Retrieve the right child of a binary tree.
-/
def rightChild : BinaryTree → BinaryTree
  | BinaryTree.nil => BinaryTree.nil
  | BinaryTree.node _ _ right => right

/--
Check if a binary tree is a leaf.
-/
@[simp]
def isLeaf : BinaryTree → Bool
  | BinaryTree.nil => true
  | BinaryTree.node _ _ _ => false

@[simp]
theorem size_node_leaf : ∀ node, isLeaf node → size node = 1 := by
  intro node
  cases node
  · intro h
    exact size_leaf
  · intro h
    contradiction

@[simp]
theorem size_node_non_leaf : ∀ node, ¬ isLeaf node → size node = 1 + size (leftChild node) + size (rightChild node) := by
  intro node
  cases node
  · intro h
    contradiction
  · intro h
    exact rfl


/--
Compute the balance factor of a binary tree.
-/
@[simp]
def balanceFactor : BinaryTree → Int
  | BinaryTree.nil => 0
  | BinaryTree.node left _ right => Int.ofNat (height left) - Int.ofNat (height right)

/--
Check if a binary tree is balanced.
-/
@[simp]
def isBalanced : BinaryTree → Bool
  | BinaryTree.nil => true
  | BinaryTree.node left _ right =>
    let bf := balanceFactor (BinaryTree.node left 0 right)
    bf ≥ -1 ∧ bf ≤ 1 ∧ isBalanced left ∧ isBalanced right


end TreeBase_n
