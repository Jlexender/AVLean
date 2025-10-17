

inductive BinaryTree (α : Type)
  | leaf : BinaryTree α
  | node (left : BinaryTree α) (right : BinaryTree α)


def depth (tree : BinaryTree α) : Nat :=
  match tree with
  | .leaf => 0
  | .node l r => 1 + max (depth l) (depth r)

def isBalanced (tree : BinaryTree α) : Bool :=
  match tree with
  | .leaf => true
  | .node l r => Int.natAbs (depth l - depth r) <= 1
