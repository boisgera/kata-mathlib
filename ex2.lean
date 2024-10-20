import Mathlib

open Nat

/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

section

variables (k n : ℕ)

lemma lemma₀ : (n < k) -> choose n k = 0 := by
  induction n with
  | zero =>
    intro zero_lt_k
    have ⟨j, k_is_succ_j⟩ : ∃ j : ℕ, k = j + 1 := by
      cases k with
      | zero =>
        have h := Nat.lt_irrefl 0
        contradiction
      | succ j =>
        use j
    rw [k_is_succ_j]
    rw [choose]
  | succ j ih =>
    -- 🤯 Brainz goes brrrrrrrrrr!
    -- need to tame the pattern matching used in the definition of choose
    sorry

lemma lemma₁ : choose n 0 = 1 ∧ choose n n = 1 := by
  constructor
  . rw[choose]
  . induction n with
    | zero =>
      rw[choose]
    | succ n ih =>
      rw [choose, ih]
      have : n < n + 1 := by
        sorry
      rw [lemma₀ (n+1) n this]

lemma lemma₂ :  (k ≤ n) -> choose n k = choose n (n - k) := by
  intro k_le_n
  induction n with
  | zero =>
    simp only [nonpos_iff_eq_zero] at k_le_n
    simp only [_root_.zero_le, Nat.sub_eq_zero_of_le, choose_self, k_le_n]
  | succ n ih =>
    sorry

end
