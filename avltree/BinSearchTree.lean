import avltree.BinTree

open BinTree

namespace BinSearchTree

@[simp]
def is_bst : BinTree → Prop
  | .empty                    => True
  | .node value left right    =>
      (∀ v ∈ collect_values left, v < value) ∧
      (∀ v ∈ collect_values right, v > value) ∧
      is_bst left ∧
      is_bst right

inductive BinSearchTree : Type
  | mk : (tree : BinTree) → is_bst tree → BinSearchTree

def find (searchValue : Nat) : BinSearchTree → Bool
  | .mk tree _ =>
      let rec find_aux (currentTree : BinTree) : Bool :=
        match currentTree with
        | .empty                     => false
        | .node value left right     =>
            if searchValue == value then
              true
            else if searchValue < value then
              find_aux left
            else
              find_aux right
      find_aux tree

def insert (newValue : Nat) : BinSearchTree → BinSearchTree
  | .mk tree proof =>
      let rec insert_aux (currentTree : BinTree) : BinTree :=
        match currentTree with
        | .empty                     => .node newValue .empty .empty
        | .node value left right     =>
            if newValue == value then
              currentTree
            else if newValue < value then
              .node value (insert_aux left) right
            else
              .node value left (insert_aux right)
      let updatedTree := insert_aux tree
      .mk updatedTree (by sorry)

def remove (targetValue : Nat) : BinSearchTree → BinSearchTree
  | .mk tree proof =>
      let rec remove_aux (currentTree : BinTree) : BinTree :=
        match currentTree with
        | .empty                     => .empty
        | .node value left right     =>
            if targetValue == value then
              match left, right with
              | .empty, _       => right
              | _, .empty       => left
              | _, _            =>
                  let rec find_min (subtree : BinTree) : Nat :=
                    match subtree with
                    | .empty                      => panic! "unreachable"
                    | .node minValue .empty _     => minValue
                    | .node _ leftChild _         => find_min leftChild
                  let minRightValue := find_min right
                  .node minRightValue left (remove_aux right)
            else if targetValue < value then
              .node value (remove_aux left) right
            else
              .node value left (remove_aux right)
      let updatedTree := remove_aux tree
      .mk updatedTree (by sorry)

def rotate_left (bst : BinSearchTree) : BinSearchTree :=
  match bst with
  | .mk tree proof =>
      match tree with
      | .empty => bst
      | .node value left right =>
          match right with
          | .empty => bst
          | .node rightValue rightLeft rightRight =>
              let rotatedTree := .node rightValue (.node value left rightLeft) rightRight
              .mk rotatedTree (by sorry)

def rotate_right (bst : BinSearchTree) : BinSearchTree :=
  match bst with
  | .mk tree proof =>
      match tree with
      | .empty => bst
      | .node value left right =>
          match left with
          | .empty => bst
          | .node leftValue leftLeft leftRight =>
              let rotatedTree := .node leftValue leftLeft (.node value leftRight right)
              .mk rotatedTree (by sorry)

@[simp]
def balance_factor (tree : BinTree) : Int :=
  match tree with
  | .empty                    => 0
  | .node _ left right        => Int.ofNat (height left) - Int.ofNat (height right)

@[simp]
theorem empty_is_bst : is_bst .empty :=
  by simp [is_bst]

@[simp]
theorem collect_values_empty : collect_values (.empty : BinTree) = [] :=
  rfl

@[simp]
theorem collect_values_node (value : Nat) (left right : BinTree) :
    collect_values (.node value left right) =
    collect_values left ++ [value] ++ collect_values right :=
  rfl

@[simp]
theorem height_empty : height (.empty : BinTree) = 0 :=
  rfl

@[simp]
theorem balance_factor_empty : balance_factor .empty = 0 :=
  rfl

@[simp]
theorem balance_factor_node (value : Nat) (left right : BinTree) :
    balance_factor (.node value left right) = Int.ofNat (height left) - Int.ofNat (height right) :=
  rfl

@[simp]
theorem is_bst_true_for_empty : is_bst .empty = True :=
  rfl

@[simp]
theorem not_mem_collect_values_empty (v : Nat) : v ∉ collect_values (.empty : BinTree) := by
  simp

theorem bst_node_property {value : Nat} {left right : BinTree}
    (h : is_bst (.node value left right)) :
    (∀ v ∈ collect_values left, v < value) ∧
    (∀ v ∈ collect_values right, v > value) ∧
    is_bst left ∧
    is_bst right :=
  by simp [is_bst] at h; exact h

@[simp]
theorem bst_implies_left_smaller {value : Nat} {left right : BinTree}
    (h : is_bst (.node value left right)) (v : Nat) (hv : v ∈ collect_values left) :
    v < value :=
  by
    rcases bst_node_property h with ⟨h_left, _, _, _⟩
    exact h_left v hv

@[simp]
theorem bst_implies_right_greater {value : Nat} {left right : BinTree}
    (h : is_bst (.node value left right)) (v : Nat) (hv : v ∈ collect_values right) :
    v > value :=
  by
    rcases bst_node_property h with ⟨_, h_right, _, _⟩
    exact h_right v hv

@[simp]
theorem balance_factor_nonempty_node {value : Nat} {left right : BinTree} :
    balance_factor (.node value left right) = Int.ofNat (height left) - Int.ofNat (height right) :=
  rfl

@[simp]
theorem find_empty (searchValue : Nat) :
    find searchValue (.mk .empty empty_is_bst) = false :=
  rfl

@[simp]
theorem rotate_left_empty : rotate_left (.mk .empty empty_is_bst) = (.mk .empty empty_is_bst) :=
  rfl

@[simp]
theorem rotate_right_empty : rotate_right (.mk .empty empty_is_bst) = (.mk .empty empty_is_bst) :=
  rfl

end BinSearchTree
