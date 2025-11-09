import avltree.AvlTree

namespace AVL

/-
  Verification of AVL Invariant preservation.
-/

theorem insert_preserves_invariant {α : Type} [Ord α] (v : α) (t : AvlStructure α) :
  AvlInvariant t → AvlInvariant (Operations.insert v t) := by sorry

theorem delete_preserves_invariant {α : Type} [Ord α] (v : α) (t : AvlStructure α) :
  AvlInvariant t → AvlInvariant (Operations.delete v t) := by sorry

end AVL
