import avltree.TreeBase

open TreeBase_n

namespace AvlBase_n

/--
An AVL Tree is a balanced binary tree where each
node maintains a balance factor.

-/
inductive AvlTree where
  | nil : AvlTree
  | node : AvlTree → Int → AvlTree → AvlTree
deriving Repr
-- node(left_subtree, balance_factor, right_subtree)


end AvlBase_n
