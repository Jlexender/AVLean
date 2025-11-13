import avltree.BinTree

open BinTree

namespace BinSearchTree

@[simp]
def is_bst : BinTree → Prop
  | .empty       => True
  | .node v l r  =>
      (∀ x ∈ collect l, x < v) ∧
      (∀ x ∈ collect r, v < x) ∧
      is_bst l ∧
      is_bst r

inductive BinSearchTree : Type
  | mk : (t : BinTree) → is_bst t → BinSearchTree

def find (x : Nat) : BinSearchTree → Bool
  | .mk t _ =>
      let rec find_aux (t : BinTree) : Bool :=
        match t with
        | .empty       => false
        | .node v l r  =>
            if x == v then
              true
            else if x < v then
              find_aux l
            else
              find_aux r
      find_aux t

def insert (x : Nat) : BinSearchTree → BinSearchTree
  | .mk t h =>
      let rec insert_aux (t : BinTree) : BinTree :=
        match t with
        | .empty       => .node x .empty .empty
        | .node v l r  =>
            if x == v then
              t
            else if x < v then
              .node v (insert_aux l) r
            else
              .node v l (insert_aux r)
      let new_tree := insert_aux t
      .mk new_tree (by admit)

def remove (x : Nat) : BinSearchTree → BinSearchTree
  | .mk t h =>
      let rec remove_aux (t : BinTree) : BinTree :=
        match t with
        | .empty       => .empty
        | .node v l r  =>
            if x == v then
              match l, r with
              | .empty, _       => r
              | _, .empty       => l
              | _, _            =>
                  let rec find_min (t : BinTree) : Nat :=
                    match t with
                    | .empty          => panic! "unreachable"
                    | .node v .empty _ => v
                    | .node _ l _      => find_min l
                  let min_right := find_min r
                  .node min_right l (remove_aux r)
            else if x < v then
              .node v (remove_aux l) r
            else
              .node v l (remove_aux r)
      let new_tree := remove_aux t
      .mk new_tree (by admit)

def rotate_left (t : BinSearchTree) : BinSearchTree :=
  match t with
  | .mk tree h =>
      match tree with
      | .empty => t
      | .node v l r =>
          match r with
          | .empty => t
          | .node rv rl rr =>
              let new_tree := .node rv (.node v l rl) rr
              .mk new_tree ( by
                  admit
              )

def rotate_right (t : BinSearchTree) : BinSearchTree :=
  match t with
  | .mk tree h =>
      match tree with
      | .empty => t
      | .node v l r =>
          match l with
          | .empty => t
          | .node lv ll lr =>
              let new_tree := .node lv ll (.node v lr r)
              .mk new_tree (by admit)

@[simp]
def balance_factor (t : BinTree) : Int :=
  match t with
  | .empty       => 0
  | .node _ l r  => Int.ofNat (height l) - Int.ofNat (height r)

end BinSearchTree
