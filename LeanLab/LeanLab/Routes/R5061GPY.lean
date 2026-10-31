import Mathlib

/-!
# R-5061, GPY and Maynard weights on the pair `{n, N - n}`

Lab proof, unit U-5557, CLOUD 20261019T1321Z-cloud25. AI wrote the Lean code. Known mathematics,
Goldston-Pintz-Yıldırım 2009 and Maynard 2015 for the method. Binary Goldbach is OPEN; this is a
T3 route, never progress on Goldbach.

The GPY step for the two linear forms `n` and `N - n`: with weights `w ≥ 0`, if
`∑ w(n)(1_P(n) + 1_P(N - n)) > ∑ w(n)` then some `n` has both `n` and `N - n` prime.
Maynard's method makes the left side `(θ/2) M₂` times the right side at level `θ`, so the step
needs `M₂ > 2/θ`; numerically `M₂ = 1.385933 < 2 log 2 < 2`, see numerics/r5061_gpy.py.

* `both_prime_of_weight`: the pigeonhole step, PROVED.
* `both_prime_of_weight_example`: vacuity test at `N = 10`, `S = {3}`.
-/

namespace LeanLab.Routes.R5061

open Finset

/-- `1_P(n)` as a real number. -/
noncomputable def ind (n : ℕ) : ℝ := if n.Prime then 1 else 0

/-- The GPY pigeonhole step for the pair `{n, N - n}`. -/
theorem both_prime_of_weight (N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n)
    (h : ∑ n ∈ S, w n < ∑ n ∈ S, w n * (ind n + ind (N - n))) :
    ∃ n ∈ S, n.Prime ∧ (N - n).Prime := by
  by_contra hne
  push Not at hne
  have hle : ∀ n ∈ S, w n * (ind n + ind (N - n)) ≤ w n := by
    intro n hn
    have h1 : ind n + ind (N - n) ≤ 1 := by
      unfold ind
      by_cases hp : n.Prime
      · rw [if_pos hp, if_neg (hne n hn hp)]; norm_num
      · rw [if_neg hp]; split_ifs <;> norm_num
    nlinarith [hw n hn]
  exact absurd (sum_le_sum hle) (not_le.2 h)

/-- Vacuity test: `N = 10`, `S = {3}`, `w = 1`, and `3 + 7 = 10`. -/
theorem both_prime_of_weight_example : ∃ n ∈ ({3} : Finset ℕ), n.Prime ∧ (10 - n).Prime := by
  apply both_prime_of_weight 10 {3} (fun _ => 1) (fun _ _ => zero_le_one)
  simp only [sum_singleton, ind, one_mul]
  norm_num

end LeanLab.Routes.R5061
