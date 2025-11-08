namespace InductionDemo_n

def Nat.geom_sum_powers_two : Nat → Nat
  | 0 => 1
  | n + 1 => Nat.geom_sum_powers_two n + Nat.pow 2 (n + 1)

-- 1 + 2 + 4 + ... + 2^n = 2^(n+1) - 1
theorem sum_geom_series : ∀ n : Nat , Nat.geom_sum_powers_two n = Nat.pow 2 (n + 1) - 1 := by
  intro n
  induction n with
  | zero =>
    simp [Nat.geom_sum_powers_two]
  | succ n ih =>
    simp [Nat.geom_sum_powers_two, ih]
    grind

def Nat.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * Nat.factorial n

-- for all n, n! ≥ 1
theorem factorial_ge_1 : ∀ n : Nat, Nat.factorial n ≥ 1 := by
  intro n
  induction n with
  | zero =>
    simp [Nat.factorial]
  | succ n ih =>
    rw [Nat.factorial]

    have h1 : Nat.factorial n ≥ 1 := ih
    have h2 : (n + 1) ≥ 1 := by
      apply Nat.succ_le_succ
      exact Nat.zero_le n
    exact Nat.mul_le_mul h2 h1

end InductionDemo_n
