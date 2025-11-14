namespace BinTree

inductive BinTree : Type
  | empty : BinTree
  | node  : Nat → BinTree → BinTree → BinTree

@[simp]
def size : BinTree → Nat
  | .empty              => 0
  | .node _ left right  => 1 + size left + size right

@[simp]
def height : BinTree → Nat
  | .empty              => 0
  | .node _ left right  => 1 + max (height left) (height right)

@[simp]
def insert_left (value : Nat) (tree : BinTree) : BinTree :=
  match tree with
  | .empty                     => .node value .empty .empty
  | .node nodeValue left right => .node value (.node nodeValue left right) .empty

@[simp]
def insert_right (value : Nat) (tree : BinTree) : BinTree :=
  match tree with
  | .empty                     => .node value .empty .empty
  | .node nodeValue left right => .node value .empty (.node nodeValue left right)

@[simp]
def collect_values : BinTree → List Nat
  | .empty              => []
  | .node value left right  =>
      collect_values left ++ [value] ++ collect_values right

end BinTree
