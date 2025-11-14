import avltree.BinSearchTree
import avltree.BinTree

open BinTree
open BinSearchTree

namespace AvlTree

@[simp]
def is_avl (tree : BinTree) : Prop :=
  is_bst tree ∧
  match tree with
  | .empty                    => True
  | .node _ left right        =>
      is_avl left ∧
      is_avl right ∧
      Int.natAbs (balance_factor tree) ≤ 1

inductive AvlTree : Type
  | mk : (tree : BinTree) → is_avl tree → AvlTree

end AvlTree
