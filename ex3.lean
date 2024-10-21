import Mathlib

open Nat

/-
We define a function recursively for all positive integers $n$
by $f(1)=1$, $f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$.
Show that $f(n)= 2^{n}+(-1)^{n}$,
using the second principle of mathematical induction.
-/

def f : ℕ -> ℤ
| 0 => 2 -- 2 ^ 0 + (-1) ^ 0, so that the closed-form also works for n = 0.
| 1 => 1
| 2 => 5
| n + 2 => f (n + 1) + 2 * f n

#check Nat.strong_induction_on

theorem f_closed_form : ∀ n : ℕ, f n = 2^n + (-1)^n := by
  intro
  apply Nat.strong_induction_on (p := fun (n : ℕ) => f n = 2^n + (-1)^n)
  intro n
  match n with
  | 0 => intro ; rw [f]; rfl
  | 1 => intro ; rw [f]; rfl
  | 2 => intro ; rw [f]; rfl
  | n + 2 =>
    intro p
    have p_n : f n = 2^n + (-1)^n := by
      have : n < n + 2 := by
        simp [Int.reduceNeg, zero_lt_one, ofNat_pos, lt_add_iff_pos_right]
      exact p n this
    have p_succ_n : f (n + 1) = 2^(n + 1) + (-1)^(n + 1) := by
      have : n + 1 < n + 2 := by
        simp [Int.reduceNeg, zero_lt_one, ofNat_pos, lt_add_iff_pos_right]
      exact p (n+1) this
    by_cases h : n > 0
    . calc f (n + 2)
      _ = f (n + 1) + 2 * f n := by
        rw [f] ; intro n_eq_zero ; rw [n_eq_zero] at h ; contradiction
      _ = 2 ^ (n + 1) + (-1) ^ (n + 1) + 2 * (2 ^ n + (-1) ^ n) := by rw [p_n, p_succ_n]
      _ = 2 ^ (n + 2) + (-1) ^ (n + 2) := by ring
    . simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h
      subst h
      simp only [zero_add, Int.reducePow, Int.reduceNeg, even_two, Even.neg_pow, one_pow,
        Int.reduceAdd]
      rw [f]
