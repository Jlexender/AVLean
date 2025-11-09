
namespace AVL

/--
AVL Tree structure. No duplicates allowed in this implementation.
-/
inductive AvlStructure (α : Type) : Type
| nil : AvlStructure α
| node : AvlStructure α → α → AvlStructure α → AvlStructure α


/--
  Compute the height of an AVL tree.
  Height is the number of edges on the longest path from the root to a leaf.
-/
def height {α : Type} : AvlStructure α → Nat
| AvlStructure.nil => 0
| AvlStructure.node left _ right =>
    1 + Nat.max (height left) (height right)


/--
  Compute the balance factor of an AVL tree.
  Balance Factor = height(left subtree) - height(right subtree)
-/
def balanceFactor {α : Type} : AvlStructure α → Int
| AvlStructure.nil => 0
| AvlStructure.node left _ right =>
    Int.ofNat (height left) - Int.ofNat (height right)


namespace Auxiliary

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
| t => t


/--
  Right-right rotation. If not possible, leaves the tree unchanged.

  Transforms:

       z                y
      / \             /   \
    T1   y    ==>    z     x
        / \         / \   / \
      T2   x       T1 T2 T3 T4
-/
def rr_rotate {α : Type} : AvlStructure α → AvlStructure α
| AvlStructure.node T1 z (AvlStructure.node T2 y T3) =>
    AvlStructure.node (AvlStructure.node T1 z T2) y T3
| t => t


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
| t => t

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
| t => t

end Auxiliary

namespace Operations

/--
  Balancing operation to restore AVL property.
-/
def balance {α : Type} (t : AvlStructure α) : AvlStructure α :=
  let bf := balanceFactor t
  if bf > 1 then
    -- Left heavy
    match t with
    | AvlStructure.node left _ _ =>
        if balanceFactor left >= 0 then
          Auxiliary.ll_rotate t
        else
          Auxiliary.lr_rotate t
    | _ => t
  else if bf < -1 then
    -- Right heavy
    match t with
    | AvlStructure.node _ _ right =>
        if balanceFactor right <= 0 then
          Auxiliary.rr_rotate t
        else
          Auxiliary.rl_rotate t
    | _ => t
  else
    t


/--
  Search for a value in the AVL tree.
-/
def search {α : Type} [Ord α] (v : α) (t : AvlStructure α) : Bool :=
  match t with
  | AvlStructure.nil => false
  | AvlStructure.node left x right =>
      match compare v x with
      | Ordering.eq => true
      | Ordering.lt => search v left
      | Ordering.gt => search v right


/--
  Insert a value into the AVL tree and balance it.
-/
def insert {α : Type} [Ord α] (v : α) (t : AvlStructure α) : AvlStructure α :=
  match t with
  | AvlStructure.nil => AvlStructure.node AvlStructure.nil v AvlStructure.nil
  | AvlStructure.node left x right =>
      match compare v x with
      | Ordering.eq => t
      | Ordering.lt =>
          let newLeft := insert v left
          balance (AvlStructure.node newLeft x right)
      | Ordering.gt =>
          let newRight := insert v right
          balance (AvlStructure.node left x newRight)

/--
  Find the minimum value in the AVL tree.
-/
def findMin {α : Type} (t : AvlStructure α) : Option α :=
  match t with
  | AvlStructure.nil => none
  | AvlStructure.node AvlStructure.nil x _ => some x
  | AvlStructure.node left _ _ => findMin left

/--
  Delete a value from the AVL tree and balance it.
-/
def delete {α : Type} [Ord α] (v : α) (t : AvlStructure α) : AvlStructure α :=
  match t with
  | AvlStructure.nil => AvlStructure.nil
  | AvlStructure.node left x right =>
      match compare v x with
      | Ordering.lt =>
          let newLeft := delete v left
          balance (AvlStructure.node newLeft x right)
      | Ordering.gt =>
          let newRight := delete v right
          balance (AvlStructure.node left x newRight)
      | Ordering.eq =>
          match right with
          | AvlStructure.nil => left
          | _ =>
              match findMin right with
              | none => left
              | some minRight =>
                  let newRight := delete minRight right
                  balance (AvlStructure.node left minRight newRight)



end Operations

/--
  AVL Tree Invariant: For every node, the balance factor is -1, 0, or 1.
-/
def AvlInvariant {α : Type} (t : AvlStructure α) : Prop :=
  match t with
  | AvlStructure.nil => True
  | AvlStructure.node left _ right =>
      let bf := balanceFactor t
      bf ≥ -1 ∧ bf ≤ 1 ∧ AvlInvariant left ∧ AvlInvariant right

end AVL
