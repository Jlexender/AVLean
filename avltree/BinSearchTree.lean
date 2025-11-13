import avltree.BinTree

open BinTree

namespace BinSearchTree

def is_bst {α : Type u} [LT α]  : BinTree α → Prop
  | .empty       => True
  | .node v l r  =>
      (∀ x ∈ collect l, x < v) ∧
      (∀ x ∈ collect r, v < x) ∧
      is_bst l ∧
      is_bst r


inductive BinSearchTree (α : Type u) [LT α] : Type u
  | mk : (t : BinTree α) → is_bst t → BinSearchTree α


def find {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] [DecidableEq α]
                      (x : α) : BinSearchTree α → Bool
  | .mk t _ =>
      let rec find_aux (t : BinTree α) : Bool :=
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


def insert {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] [DecidableEq α]
                        (x : α) : BinSearchTree α → BinSearchTree α
  | .mk t h =>
      let rec insert_aux (t : BinTree α) : BinTree α :=
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
      .mk new_tree ( by
          admit
      )




def remove {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] [DecidableEq α] [Inhabited α]
                        (x : α) : BinSearchTree α → BinSearchTree α
  | .mk t h =>
      let rec remove_aux (t : BinTree α) : BinTree α :=
        match t with
        | .empty       => .empty
        | .node v l r  =>
            if x == v then
              match l, r with
              | .empty, _       => r
              | _, .empty       => l
              | _, _            =>
                  let rec find_min (t : BinTree α) : α :=
                    match t with
                    | .empty       => panic! "unreachable"
                    | .node v .empty _  => v
                    | .node _ l _      => find_min l
                  let min_right := find_min r
                  .node min_right l (remove_aux r)
            else if x < v then
              .node v (remove_aux l) r
            else
              .node v l (remove_aux r)
      let new_tree := remove_aux t
      .mk new_tree ( by
          admit
      )

def rotate_left {α : Type u} [LT α] (t : BinSearchTree α) : BinSearchTree α :=
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

def rotate_right {α : Type u} [LT α] (t : BinSearchTree α) : BinSearchTree α :=
  match t with
  | .mk tree h =>
      match tree with
      | .empty => t
      | .node v l r =>
          match l with
          | .empty => t
          | .node lv ll lr =>
              let new_tree := .node lv ll (.node v lr r)
              .mk new_tree ( by
                  admit
              )

end BinSearchTree
