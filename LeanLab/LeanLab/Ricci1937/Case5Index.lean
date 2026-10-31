import Mathlib

/-!
# P0092 Ricci 1937, case 5°: with the d that page 88 requires, a = 2 is not reached at ω = 5,21

Unit U-1079, PC run 20261019T1603Z-20267. AI wrote the Lean code. Binary Goldbach is OPEN.

Page 88, Theorem III: `ω = (θ₁ + ... + θ_{d-1} + λ θ_d)/f`, `d ≥ 1`, `0 ≤ λ < 1`, and
`τ̄ = Σ_{i<d} exp(-(θ₁+...+θᵢ)/f) + exp(-ω/2) Σ_{i≥d} exp(-(θ₁+...+θᵢ)/2)`, the tail convention
of cases 2° to 4°, which reproduces their printed bounds 2,8, 2,43, 1,98, 1,49. In Section 9,
`f = 1`. Case 5° prints `θ₁+θ₂+θ₃+6θ < ω < θ₁+θ₂+θ₃+7θ`, that is `S₉ = 4,98 < ω = 5,21 < S₁₀`,
which forces `d = 10`, but prints `d = 9` and uses `d = 9` in its τ̄ display.

`tauBar10` is τ̄ with `d = 10` at `ω = 5,21`: the head `Σ_{i=1}^{9} e^{-Sᵢ}`, `Sᵢ = 0,90, 1,46,
1,98, 2,48, ..., 4,98`, and the geometric tail `e^{-ω/2} e^{-S₁₀/2}/(1 - e^{-θ/2})` in closed form,
`(ω + S₁₀)/2 = 5,345`.

* `tauBar10_gt_one`: `τ̄ > 1`, value 1.000685, so `[1 + 2τ̄] = 3` and a = 2 fails at ω = 5,21.
  PROVED.
* Numerics, not in Lean: the least ω with τ̄ < 1 is ω* = 5.27452, where `e^ω (1 + 2τ̄) → 585.89`,
  so the method gives at best the pair (2, 585); on the d = 9 range [4,48, 4,98) τ̄ ≥ 1.0033.
-/

namespace LeanLab.Ricci1937

open Real Finset

noncomputable section

/-- τ̄ of Theorem III at ω = 5,21 with the index d = 10 that page 88 requires. -/
def tauBar10 : ℝ :=
  exp (-0.9) + exp (-1.46) + exp (-1.98) + exp (-2.48) + exp (-2.98) + exp (-3.48)
    + exp (-3.98) + exp (-4.48) + exp (-4.98) + exp (-5.345) / (1 - exp (-0.25))

/-- `(ω + S₁₀)/2` with `ω = 5,21`, `S₁₀ = θ₁+θ₂+θ₃+7θ`, and `θ/2` are the tail exponents. -/
lemma tail_exponents : ((5.21 : ℝ) + (0.90 + 0.56 + 0.52 + 7 * 0.50)) / 2 = 5.345 ∧
    (0.50 : ℝ) / 2 = 0.25 := by
  constructor <;> norm_num

lemma exp_ub {x r : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1)
    (h : ∑ i ∈ range 10, x ^ i / (i.factorial : ℝ) + x ^ 10 * ((Nat.succ 10 : ℝ) / ((Nat.factorial 10 : ℝ) * 10)) ≤ r) :
    exp x ≤ r := by
  have hb := Real.exp_bound (x := x) (by rw [abs_le]; constructor <;> linarith) (n := 10) (by norm_num)
  rw [abs_of_nonneg h0] at hb
  have := (abs_le.mp hb).2
  linarith

lemma e05 : exp 0.5 ≤ 1.648721272 := exp_ub (by norm_num) (by norm_num)
  (by norm_num [Finset.sum_range_succ, Nat.factorial])
lemma e04 : exp 0.4 ≤ 1.491824699 := exp_ub (by norm_num) (by norm_num)
  (by norm_num [Finset.sum_range_succ, Nat.factorial])
lemma e046 : exp 0.46 ≤ 1.584073986 := exp_ub (by norm_num) (by norm_num)
  (by norm_num [Finset.sum_range_succ, Nat.factorial])
lemma e048 : exp 0.48 ≤ 1.616074404 := exp_ub (by norm_num) (by norm_num)
  (by norm_num [Finset.sum_range_succ, Nat.factorial])
lemma e0345 : exp 0.345 ≤ 1.411989921 := exp_ub (by norm_num) (by norm_num)
  (by norm_num [Finset.sum_range_succ, Nat.factorial])
lemma e025 : exp 0.25 ≤ 1.284025418 := exp_ub (by norm_num) (by norm_num)
  (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `exp (m/2 + r) ≤ B^m R` from `exp (1/2) ≤ B` and `exp r ≤ R`. -/
lemma exp_split {m : ℕ} {r R : ℝ} (hR : exp r ≤ R) :
    exp ((m : ℝ) * 0.5 + r) ≤ 1.648721272 ^ m * R := by
  rw [exp_add, show exp ((m : ℝ) * 0.5) = exp 0.5 ^ m by rw [← exp_nat_mul]]
  exact mul_le_mul (pow_le_pow_left₀ (exp_pos _).le e05 m) hR (exp_pos _).le (by positivity)

/-- `exp (-y) ≥ 1/U` from `exp y ≤ U`. -/
lemma exp_neg_ge {y U : ℝ} (h : exp y ≤ U) : 1 / U ≤ exp (-y) := by
  rw [exp_neg, one_div]
  exact inv_anti₀ (exp_pos y) h

lemma tauBar10_gt_one : 1 < tauBar10 := by
  have h1 : 1 / (1.648721272 ^ 1 * 1.491824699) ≤ exp (-0.9) :=
    exp_neg_ge (by have := exp_split (m := 1) e04; norm_num at this ⊢; linarith)
  have h2 : 1 / (1.648721272 ^ 2 * 1.584073986) ≤ exp (-1.46) :=
    exp_neg_ge (by have := exp_split (m := 2) e046; norm_num at this ⊢; linarith)
  have h3 : 1 / (1.648721272 ^ 3 * 1.616074404) ≤ exp (-1.98) :=
    exp_neg_ge (by have := exp_split (m := 3) e048; norm_num at this ⊢; linarith)
  have h4 : 1 / (1.648721272 ^ 4 * 1.616074404) ≤ exp (-2.48) :=
    exp_neg_ge (by have := exp_split (m := 4) e048; norm_num at this ⊢; linarith)
  have h5 : 1 / (1.648721272 ^ 5 * 1.616074404) ≤ exp (-2.98) :=
    exp_neg_ge (by have := exp_split (m := 5) e048; norm_num at this ⊢; linarith)
  have h6 : 1 / (1.648721272 ^ 6 * 1.616074404) ≤ exp (-3.48) :=
    exp_neg_ge (by have := exp_split (m := 6) e048; norm_num at this ⊢; linarith)
  have h7 : 1 / (1.648721272 ^ 7 * 1.616074404) ≤ exp (-3.98) :=
    exp_neg_ge (by have := exp_split (m := 7) e048; norm_num at this ⊢; linarith)
  have h8 : 1 / (1.648721272 ^ 8 * 1.616074404) ≤ exp (-4.48) :=
    exp_neg_ge (by have := exp_split (m := 8) e048; norm_num at this ⊢; linarith)
  have h9 : 1 / (1.648721272 ^ 9 * 1.616074404) ≤ exp (-4.98) :=
    exp_neg_ge (by have := exp_split (m := 9) e048; norm_num at this ⊢; linarith)
  have h10 : 1 / (1.648721272 ^ 10 * 1.411989921) ≤ exp (-5.345) :=
    exp_neg_ge (by have := exp_split (m := 10) e0345; norm_num at this ⊢; linarith)
  have h11 : 1 / 1.284025418 ≤ exp (-0.25) := exp_neg_ge e025
  have hden : 0 < 1 - exp (-0.25) := by
    have : exp (-0.25) < 1 := exp_lt_one_iff.mpr (by norm_num); linarith
  have htail : 1 / (1.648721272 ^ 10 * 1.411989921) / (1 - 1 / 1.284025418) ≤
      exp (-5.345) / (1 - exp (-0.25)) := by
    apply div_le_div₀ (exp_pos _).le h10 hden (by linarith)
  unfold tauBar10
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 htail ⊢
  linarith

end
end LeanLab.Ricci1937
