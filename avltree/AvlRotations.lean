import avltree.AvlStructure

namespace AVL

namespace Rotations

/-
  AVL Tree Rotations.
  If rotation is not possible, leave the tree unchanged.
-/

/--
  Left-left rotation. If not possible, leaves the tree unchanged.

  Transforms:

      z                   y
     / \                 / \
    y   T4    ==>       x   z
   / \                 / \ / \
  x   T3             T1 T2 T3 T4
-/
def ll_rotate {α : Type} : AvlStructure α → AvlStructure α
| AvlStructure.node (AvlStructure.node T1 x T2) z T4 =>
    AvlStructure.node T1 x (AvlStructure.node T2 z T4)
| t => t  -- No rotation possible


/--
  Right-right rotation. If not possible, leaves the tree unchanged.

  Transforms:

      z                    y
     / \                 /  \
    T1   y    ==>       z    x
        / \           / \   / \
      T2   x         T1 T2 T3 T4
-/
def rr_rotate {α : Type} : AvlStructure α → AvlStructure α
| AvlStructure.node T1 z (AvlStructure.node T2 y T3) =>
    AvlStructure.node (AvlStructure.node T1 z T2) y T3
| t => t  -- No rotation possible


/--
  Left-right rotation. If not possible, leaves the tree unchanged.

  Transforms:

      z                 z                    x
     / \               / \                 /  \
    y   T4    ==>     x   T4    ==>       y    z
   / \               / \                 / \  / \
 T1   x             y   T3              T1 T2 T3 T4
     / \           / \
   T2   T3       T1   T2
-/
def lr_rotate {α : Type} : AvlStructure α → AvlStructure α
| AvlStructure.node (AvlStructure.node T1 y (AvlStructure.node T2 x T3)) z T4 =>
    AvlStructure.node (AvlStructure.node T1 y T2) x (AvlStructure.node T3 z T4)
| t => t  -- No rotation possible

/--
  Right-left rotation. If not possible, leaves the tree unchanged.

  Transforms:

      z                  z                   x
     / \               /   \               /   \
    T1   y    ==>     T1    x    ==>     z      y
        / \          / \                / \    / \
      x   T4        T2   y             T1 T2  T3 T4
     / \               /  \
   T2   T3            T3  T4
-/
def rl_rotate {α : Type} : AvlStructure α → AvlStructure α
| AvlStructure.node T1 z (AvlStructure.node (AvlStructure.node T2 x T3) y T4) =>
    AvlStructure.node (AvlStructure.node T1 z T2) x (AvlStructure.node T3 y T4)
| t => t  -- No rotation possible

end Rotations

end AVL
