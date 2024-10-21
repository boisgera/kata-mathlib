import Mathlib

open Nat

/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

lemma ex_lb_succ (n : ℕ) : ∀ (k : ℕ), n < k → ∃ j, k = succ j := by
  intro k
  cases k with
  | zero => intro ; contradiction
  | succ m => intro ; use m

lemma lemma₀ (n : ℕ) : ∀ (k : ℕ), (n < k) -> choose n k = 0 := by
  induction n with
  | zero =>
    intro k n_lt_k
    let ⟨_, h⟩ := ex_lb_succ 0 k n_lt_k
    rw [h, choose]
  | succ n ih =>
    intro k succ_n_lt_k
    have ⟨m, hm⟩ := ex_lb_succ (n+1) k succ_n_lt_k
    rw [hm, choose]
    have le_1 : n < m := by
      subst hm
      simp only [succ_eq_add_one, add_lt_add_iff_right] at succ_n_lt_k
      assumption
    have le_2: n < m + 1 := by
      subst hm
      exact lt_trans le_1 (lt_add_one m)
    rw [ih m le_1, ih (m+1) le_2]

theorem theorem₁ (n : ℕ) : choose n 0 = 1 ∧ choose n n = 1 := by
  constructor
  . rw[choose]
  . induction n with
    | zero =>
      rw[choose]
    | succ n ih =>
      rw [choose, ih]
      have : n < n + 1 := lt_add_one n
      rw [lemma₀ n (n+1) this]

theorem theorem₂ (n : ℕ) : ∀ (k : ℕ), (k ≤ n) -> choose n k = choose n (n - k) := by
  induction n with
  | zero =>
    intro k k_le_n
    simp only [nonpos_iff_eq_zero] at k_le_n
    simp only [_root_.zero_le, Nat.sub_eq_zero_of_le, choose_self, k_le_n]
  | succ n ih =>
    intro k k_le_succ_n
    cases k with
    | zero =>
      rw [choose]
      simp only [tsub_zero, (theorem₁ (n+1)).2]
    | succ j =>
      simp only [add_le_add_iff_right] at k_le_succ_n
      rw [choose]
      simp only [reduceSubDiff]
      rw [ih j k_le_succ_n]
      cases le_or_gt (j+1) n with
      | inl succ_j_le_n =>
        rw [ih (j+1) succ_j_le_n]
        have : n - j = (n - (j+1)) + 1 := by
          rw [<- Nat.sub_sub]
          have h : n - j ≠ 0 := by
            intro n_eq_j
            have n_le_j := Nat.le_of_sub_eq_zero n_eq_j
            have j_lt_n := Nat.lt_of_succ_le succ_j_le_n
            have := not_le_of_lt j_lt_n
            contradiction
          rw [Nat.add_one, Nat.sub_one, Nat.succ_pred h]
        rw [this, choose, add_comm]
      | inr succ_j_gt_n =>
        have n_sub_j_eq_0 : n - j = 0 := by
          rw [gt_iff_lt, Nat.lt_succ_iff] at succ_j_gt_n
          rw [Nat.sub_eq_zero_of_le]
          assumption
        rw [n_sub_j_eq_0]
        rw [choose, choose, lemma₀ n (j+1) succ_j_gt_n]
