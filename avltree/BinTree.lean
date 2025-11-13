namespace BinTree

inductive BinTree : Type
  | empty : BinTree
  | node  : Nat → BinTree → BinTree → BinTree

def size : BinTree → Nat
  | .empty       => 0
  | .node _ l r  => 1 + size l + size r

def height : BinTree → Nat
  | .empty       => 0
  | .node _ l r  => 1 + max (height l) (height r)

def insert_left (x : Nat) (t : BinTree) : BinTree :=
  match t with
  | .empty       => .node x .empty .empty
  | .node v l r  => .node x (.node v l r) .empty

def insert_right (x : Nat) (t : BinTree) : BinTree :=
  match t with
  | .empty       => .node x .empty .empty
  | .node v l r  => .node x .empty (.node v l r)

def collect : BinTree → List Nat
  | .empty       => []
  | .node v l r  => collect l ++ [v] ++ collect r

end BinTree
