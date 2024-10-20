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
  intro k k_le_n
  induction n with
  | zero =>
    simp only [nonpos_iff_eq_zero] at k_le_n
    simp only [_root_.zero_le, Nat.sub_eq_zero_of_le, choose_self, k_le_n]
  | succ n ih =>
    sorry
