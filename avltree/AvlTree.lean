import avltree.BinSearchTree
import avltree.BinTree

open BinTree
open BinSearchTree

namespace AvlTree

@[simp]
def is_avl (t : BinTree) : Prop :=
  is_bst t ∧
  match t with
  | .empty       => True
  | .node _ l r  =>
      is_avl l ∧
      is_avl r ∧
      Int.natAbs (balance_factor t) ≤ 1

inductive AvlTree : Type
  | mk : (t : BinTree) → is_avl t → AvlTree

end AvlTree
