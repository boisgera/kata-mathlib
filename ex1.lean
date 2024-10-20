import Mathlib

open Finset

/-
If $a$ and $r$ are real numbers and $r \neq 1$, then
(1.1)
$$
\sum_{j=0}^{n} a r^{j}=a+a r+a r^{2}+\cdots+a r^{n}=\frac{a r^{n+1}-a}{r-1} .
$$
-/

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) :
  ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by

  have r_sub_one_new_zero : r - 1 ≠ 0 := by
    intro k
    have := congrArg (· + 1) k
    simp at this
    contradiction

  induction n with
  | zero =>
    rw [zero_add, range_one, sum_singleton]
    rw [pow_zero, mul_one, pow_one]
    rw [<- mul_sub_one]
    rw [<- mul_div]
    rw [div_self r_sub_one_new_zero]
    rw [mul_one]
  | succ n ih =>
    rw [sum_range_succ (β := ℝ)]
    rw [ih]
    nth_rw 2 [<- mul_one (a * r ^ (n + 1))]
    nth_rw 2 [<- div_self r_sub_one_new_zero]
    rw [mul_div, <- add_div]
    rw [mul_sub]
    simp only [mul_one, sub_add_sub_cancel']
    rw [mul_assoc, <- pow_succ]
