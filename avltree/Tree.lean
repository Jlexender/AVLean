
namespace BinaryTree_n

/-- Binary Tree Definition

  X
 / \
X   X

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


/-- Example binary tree.

  2
 / \
1   3

-/
def exampleTree : BinaryTree :=
  BinaryTree.node
    (BinaryTree.node BinaryTree.leaf 1 BinaryTree.leaf)
    2
    (BinaryTree.node BinaryTree.leaf 3 BinaryTree.leaf)

#eval depth exampleTree
#eval size exampleTree


@[simp]
theorem depth_leaf : depth BinaryTree.leaf = 0 := rfl

@[simp]
theorem size_leaf : size BinaryTree.leaf = 1 := rfl


end BinaryTree_n
