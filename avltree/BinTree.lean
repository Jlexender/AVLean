namespace BinTree

inductive BinTree (α : Type u) : Type u
  | empty : BinTree α
  | node  : α → BinTree α → BinTree α → BinTree α


def size {α : Type u} : BinTree α → Nat
  | BinTree.empty       => 0
  | BinTree.node _ l r  => 1 + size l + size r

def height {α : Type u} : BinTree α → Nat
  | .empty       => 0
  | .node _ l r  => 1 + max (height l) (height r)

def insert_left {α : Type u} (x : α) (t : BinTree α) : BinTree α :=
  match t with
  | .empty       => .node x .empty .empty
  | .node v l r  => .node x (.node v l r) .empty

def insert_right {α : Type u} (x : α) (t : BinTree α) : BinTree α :=
  match t with
  | .empty       => .node x .empty .empty
  | .node v l r  => .node x .empty (.node v l r)

def collect {α : Type u} : BinTree α → List α
  | .empty       => []
  | .node v l r  => collect l ++ [v] ++ collect r

end BinTree
