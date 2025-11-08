import avltree.AvlBase
import avltree.TreeBalance

open AvlBase_n
open TreeBalance_n

namespace AvlOps_n

/--
Right-right rotation for AVL tree balancing.
Used when the right subtree is heavier and its right subtree is the heaviest.
Transforms:
    A            B
     \          / \
      B   ->   A   C
       \
        C
-/
def rotateRightRight : AvlTree → AvlTree
  | AvlTree.nil => AvlTree.nil
  | AvlTree.node left bf (AvlTree.node rightLeft rightBf rightRight) =>
    AvlTree.node (AvlTree.node left bf rightLeft) (bf + 1 - min rightBf 0) rightRight
  | AvlTree.node _ _ _ => AvlTree.nil  -- Invalid case, return empty tree

/--
Left-left rotation for AVL tree balancing.
Used when the left subtree is heavier and its left subtree is the heaviest.
Transforms:
      C        B
     /        / \
    B   ->   A   C
   /
  A
-/
def rotateLeftLeft : AvlTree → AvlTree
  | AvlTree.nil => AvlTree.nil
  | AvlTree.node (AvlTree.node leftLeft leftBf leftRight) bf right =>
    AvlTree.node leftLeft (bf - 1 - max leftBf 0) (AvlTree.node leftRight bf right)
  | AvlTree.node _ _ _ => AvlTree.nil  -- Invalid case, return empty tree

/--
Left-right double rotation for AVL tree balancing.
Used when the left subtree is heavier but its right subtree is the heaviest.
First does a right rotation on left child, then left rotation on root.
Transforms:
      C          C        B
     /          /        / \
    A    ->    B   ->   A   C
     \        /
      B      A
-/
def rotateLeftRight : AvlTree → AvlTree
  | AvlTree.nil => AvlTree.nil
  | AvlTree.node left bf (AvlTree.node rightLeft rightBf rightRight) =>
    let newLeft := AvlTree.node left bf rightLeft
    let newTree := AvlTree.node newLeft (bf + 1 - min rightBf 0) rightRight
    rotateLeftLeft newTree
  | AvlTree.node _ _ _ => AvlTree.nil  -- Invalid case, return empty tree

/--
Right-left double rotation for AVL tree balancing.
Used when the right subtree is heavier but its left subtree is the heaviest.
First does a left rotation on right child, then right rotation on root.
Transforms:
    A        A            B
     \        \          / \
      C  ->    B   ->   A   C
     /          \
    B            C
-/
def rotateRightLeft : AvlTree → AvlTree
  | AvlTree.nil => AvlTree.nil
  | AvlTree.node (AvlTree.node leftLeft leftBf leftRight) bf right =>
    let newRight := AvlTree.node leftRight bf right
    let newTree := AvlTree.node leftLeft (bf - 1 - max leftBf 0) newRight
    rotateRightRight newTree
  | AvlTree.node _ _ _ => AvlTree.nil  -- Invalid case, return empty tree

end AvlOps_n
