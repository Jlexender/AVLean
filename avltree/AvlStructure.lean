
namespace AVL

/--
AVL Tree structure.
-/
inductive AvlStructure (α : Type) : Type
| nil : AvlStructure α
| node : AvlStructure α → α → AvlStructure α → AvlStructure α






end AVL
