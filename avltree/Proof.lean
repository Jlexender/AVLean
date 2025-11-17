inductive BinTree where
  | leaf : BinTree
  | node : BinTree → Nat → BinTree → BinTree
deriving Repr, Inhabited


@[simp]
def height : BinTree → Nat
  | .leaf => 0
  | .node l _ r => 1 + max (height l) (height r)


@[simp]
def size : BinTree → Nat
  | .leaf => 0
  | .node l _ r => 1 + size l + size r


@[simp]
def mirror : BinTree → BinTree
  | .leaf => .leaf
  | .node l v r => .node (mirror r) v (mirror l)


@[simp]
theorem mirror_involutive (t : BinTree) : mirror (mirror t) = t := by
  induction t with
  | leaf => rfl
  | node l v r ih_l ih_r =>
    simp [mirror, ih_l, ih_r]


@[simp]
theorem height_mirror (t : BinTree) : height (mirror t) = height t := by
  induction t with
  | leaf => rfl
  | node l v r ih_l ih_r =>
    simp [mirror, height, ih_l, ih_r]
    rw [Nat.max_comm]


@[simp]
theorem size_mirror (t : BinTree) : size (mirror t) = size t := by
  induction t with
  | leaf => rfl
  | node l v r ih_l ih_r =>
    simp [mirror, size, ih_l, ih_r]
    grind


def is_bst : BinTree → Option Nat → Option Nat → Prop
  | .leaf, _, _ => True
  | .node l v r, min_opt, max_opt =>
    (match min_opt with
     | none => True
     | some min_val => v > min_val) ∧
    (match max_opt with
     | none => True
     | some max_val => v < max_val) ∧
    is_bst l min_opt (some v) ∧
    is_bst r (some v) max_opt

inductive BinSearchTree where
  | mk : (t : BinTree) → is_bst t none none → BinSearchTree
deriving Repr


theorem height_leaf : height BinTree.leaf = 0 := rfl
theorem size_leaf : size BinTree.leaf = 0 := rfl
theorem mirror_leaf : mirror BinTree.leaf = BinTree.leaf := rfl


theorem size_node (l : BinTree) (v : Nat) (r : BinTree) :
    size (BinTree.node l v r) = 1 + size l + size r := rfl
theorem height_node (l : BinTree) (v : Nat) (r : BinTree) :
    height (BinTree.node l v r) = 1 + max (height l) (height r) := rfl
theorem mirror_node (l : BinTree) (v : Nat) (r : BinTree) :
    mirror (BinTree.node l v r) = BinTree.node (mirror r) v (mirror l) := rfl


theorem size_pos (l : BinTree) (v : Nat) (r : BinTree) :
    0 < size (BinTree.node l v r) := by
  simp [size]
  omega

theorem height_nonneg (t : BinTree) : 0 ≤ height t := Nat.zero_le _
theorem size_nonneg (t : BinTree) : 0 ≤ size t := Nat.zero_le _


def avl_invariant : BinTree → Prop
  | .leaf => True
  | .node l _ r =>
    (Int.natAbs (height l - height r) ≤ 1) ∧
    avl_invariant l ∧
    avl_invariant r


def is_avl : BinSearchTree → Prop
  | .mk t _ => avl_invariant t


def insert_aux : Nat → BinTree → BinTree
  | v, .leaf => .node .leaf v .leaf
  | v, .node l val r =>
    if v < val then
      .node (insert_aux v l) val r
    else if v > val then
      .node l val (insert_aux v r)
    else
      .node l val r

def in_bounds (v : Nat) (minopt maxopt : Option Nat) : Prop :=
  (match minopt with | none => True | some m => v > m) ∧
  (match maxopt with | none => True | some M => v < M)


theorem insert_aux_preserves_bst (v : Nat) (t : BinTree) :
  ∀ minopt maxopt,
    in_bounds v minopt maxopt →
    is_bst t minopt maxopt →
    is_bst (insert_aux v t) minopt maxopt := by
  intro minopt maxopt
  induction t generalizing minopt maxopt with
  | leaf =>
    intro h_in h_bst
    -- inserting into a leaf yields node .leaf v .leaf, and h_in provides the two bounds
    simp [insert_aux, is_bst]
    trivial

    -- cases h_in with
    -- | intro h_lo h_hi =>
    --   constructor
    --   · exact h_lo
    --   constructor
    --   · exact h_hi
    --   constructor
    --   · assumption
    --   · assumption

  | node l val r ih_l ih_r =>
    intro h_in h_bst
    -- break apart is_bst hypothesis for this node
    rcases h_bst with ⟨h_lo, h_rest⟩
    rcases h_rest with ⟨h_hi, ⟨h_bl, h_br⟩⟩
    -- and break apart the in_bounds hypothesis
    rcases h_in with ⟨h_v_lo, h_v_hi⟩
    simp [insert_aux]
    by_cases hv_lt : v < val
    · -- inserted into left subtree
      simp [hv_lt]
      constructor
      · exact h_lo
      constructor
      · exact h_hi
      constructor
      · -- need: v in bounds for left subtree: lower bound = minopt, upper bound = some val
        apply ih_l (minopt := minopt) (maxopt := some val)
        constructor
        · exact h_v_lo
        · -- new upper bound is `some val`, need v < val which is hv_lt
          exact hv_lt
        -- use h_bl which is is_bst l minopt (some val)
        exact h_bl
      · exact h_br

    by_cases hv_gt : v > val
    · -- inserted into right subtree
      simp [hv_lt, hv_gt]
      constructor
      · exact h_lo
      constructor
      · exact h_hi
      constructor
      · exact h_bl
      · -- need: v in bounds for right subtree: lower bound = some val, upper bound = maxopt
        apply ih_r (minopt := some val) (maxopt := maxopt)
        constructor
        · -- new lower bound is `some val`, need v > val which is hv_gt
          exact hv_gt
        · exact h_v_hi
        exact h_br

    · -- neither < nor >: insertion returns same node, so original bst components suffice
      simp [hv_lt, hv_gt]
      constructor; · exact h_lo
      constructor; · exact h_hi
      constructor; · exact h_bl
      · exact h_br


def insert_bst (v : Nat) : BinSearchTree → BinSearchTree
  | .mk t h =>
    .mk (insert_aux v t) (
      by
        apply insert_aux_preserves_bst v t none none
        constructor
        · trivial
        · trivial
        exact h
    )


def find_aux : Nat → BinTree → Bool
  | _, .leaf => false
  | v, .node l val r =>
    if v < val then
      find_aux v l
    else if v > val then
      find_aux v r
    else
      true


def find_bst (v : Nat) : BinSearchTree → Bool
  | .mk t _ => find_aux v t


def rot_right : BinTree → BinTree
  | .node (.node l1 v1 r1) v2 r2 =>
    .node l1 v1 (.node r1 v2 r2)
  | t => t  -- no rotation possible

def rot_left : BinTree → BinTree
  | .node l1 v1 (.node l2 v2 r2) =>
    .node (.node l1 v1 l2) v2 r2
  | t => t  -- no rotation possible

theorem rot_right_preserves_bst (t : BinTree) :
  ∀ minopt maxopt,
    is_bst t minopt maxopt →
    is_bst (rot_right t) minopt maxopt := by
  intro minopt maxopt h_bst
  cases t with
  | leaf => trivial
  | node l2 v2 r2 =>
    cases l2 with
    | leaf =>
      -- rotation on node with leaf left child yields same tree, so bst property holds trivially
      simp [rot_right]
      exact h_bst
    | node l1 v1 r1 =>
      -- now we have t = node (node l1 v1 r1) v2 r2
      -- need to show is_bst (node l1 v1 (node r1 v2 r2)) minopt maxopt
      simp [rot_right]
      -- break apart h_bst for t
      rcases h_bst with ⟨h_lo, h_rest⟩
      rcases h_rest with ⟨h_hi, ⟨h_bl, h_br⟩⟩
      -- break apart h_bl for left subtree
      rcases h_bl with ⟨h_l1_lo, h_l1_rest⟩
      rcases h_l1_rest with ⟨h_l1_hi, ⟨h_bl1, h_br1⟩⟩
      constructor
      · exact h_l1_lo
      constructor
      · -- need to show v1 < maxopt
        cases maxopt with
        | none => trivial
        | some M =>
          -- from h_hi: v2 < M, and from h_l1_hi: v1 < v2, so v1 < M
          have h_v2_lt_M : v2 < M := h_hi
          have h_v1_lt_v2 : v1 < v2 := h_l1_hi
          omega
      constructor
      · -- need is_bst l1 minopt (some v1)
        exact h_bl1
      · -- need is_bst (node r1 v2 r2) (some v1) maxopt
        constructor
        · -- need v2 > v1
          exact h_l1_hi
        · trivial


theorem rot_left_preserves_bst (t : BinTree) :
  ∀ minopt maxopt,
    is_bst t minopt maxopt →
    is_bst (rot_left t) minopt maxopt := by
  intro minopt maxopt h_bst
  cases t with
  | leaf => trivial
  | node l1 v1 r1 =>
    cases r1 with
    | leaf =>
      -- rotation on node with leaf right child yields same tree, so bst property holds trivially
      simp [rot_left]
      exact h_bst
    | node l2 v2 r2 =>
      -- now we have t = node l1 v1 (node l2 v2 r2)
      -- need to show is_bst (node (node l1 v1 l2) v2 r2) minopt maxopt
      simp [rot_left]
      -- break apart h_bst for t
      rcases h_bst with ⟨h_lo, h_rest⟩
      rcases h_rest with ⟨h_hi, ⟨h_bl, h_br⟩⟩
      -- break apart h_br for right subtree
      rcases h_br with ⟨h_l2_lo, h_l2_rest⟩
      rcases h_l2_rest with ⟨h_l2_hi, ⟨h_bl2, h_br2⟩⟩
      constructor
      · grind
      · trivial



def rot_right_bst : BinSearchTree → BinSearchTree
  | .mk t h => .mk (rot_right t) (
    by
      apply rot_right_preserves_bst t none none
      exact h
  )

def rot_left_bst : BinSearchTree → BinSearchTree
  | .mk t h => .mk (rot_left t) (
    by
      apply rot_left_preserves_bst t none none
      exact h
  )
