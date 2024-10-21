import Mathlib

open Nat

/-
We define a function recursively for all positive integers $n$
by $f(1)=1$, $f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$.
Show that $f(n)= 2^{n}+(-1)^{n}$,
using the second principle of mathematical induction.
-/

def f : ℕ -> ℤ
| 0 => 2 -- 2^0 + (-1)^0
| 1 => 1
| 2 => 5
| n + 2 => (f n) + 2 * (f (n+1))

#check Nat.strong_induction_on
-- theorem Nat.strong_induction_on
-- {p : ℕ → Prop} (n : ℕ) (h : ∀ (n : ℕ), (∀ (m : ℕ), m < n → p m) → p n) :
-- p n

theorem f_closed_form (n : ℕ) : f n = 2^n + (-1)^n := by
  sorry
