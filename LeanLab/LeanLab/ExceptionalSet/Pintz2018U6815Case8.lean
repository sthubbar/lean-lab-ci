/-
P0016 Pintz 2018, arXiv 1804.09084v2, unit U-6815, CLOUD 20261021T0316Z-cloud57, T2.
Binding map of Section 9: Case 8 is far from binding.

`Pintz2018Slack2.case8_closes_gen` closes Case 8 for every weight `A ≥ 7/2`. Here the same
argument, with the same quoted inputs (9.31) and (9.32), is pushed down to every `A ≥ 17/5`,
that is to the level `ϑ = 5/17` and the exponent `1 - 5/17 = 12/17 = 0.70588...`. The numerics
of numerics/map_U6815.py put the true floor of this Case 8 argument at `A ≈ 3.3077`, exponent
`0.6977`. So Case 8 is not what holds Pintz's exponent at `0.72`; Cases 1 to 6 are, see
`Pintz2018Slack2` and PROGRESS.md U-6815.

The new idea against `case8_closes_gen` is to use both cut conditions `Λ* ≥ 3.96` and
`Λ* ≥ (12/11 - ε) log(1/λ₁)`, split at `λ₁ = 0.02`: above it the first gives
`e^{-(A-2)Λ*} ≤ e^{-5.544}`, below it the second gives `e^{-(A-2)Λ*} ≤ λ₁^{3/2} ≤ e^{-1.95} λ₁`,
which beats the linear gain `1 - e^{-2Aλ₁} ≈ 2Aλ₁`.

HONESTY. This is a statement about one case of Pintz's own argument with his own quoted inputs,
CONDITIONAL ON those inputs; it is not an improvement of the exponent `0.72`, since Cases 1 to 6
still bind at `η < 0.0029948`. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ExceptionalSet.Pintz2018Slack2

namespace LeanLab.ExceptionalSet.Pintz2018U6815Case8
open Real Finset
open LeanLab.ExceptionalSet.Pintz2018Slack

attribute [local instance] Classical.propDecidable

/-! ### Numerical facts, each from the 15-term Taylor bounds of `Pintz2018.ExpBounds` -/

theorem m_e5544 : exp (-5.544 : ℝ) ≤ 0.00392 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 5.544 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

theorem m_e2904 : exp (-2.904 : ℝ) ≤ 0.0549 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 2.904 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

theorem m_e0136 : exp (-0.136 : ℝ) ≤ 0.8729 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 0.136 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

theorem m_e195 : exp (-1.95 : ℝ) ≤ 0.143 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 1.95 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

theorem m_e39 : (0.02 : ℝ) ≤ exp (-3.9) := by
  have h1 := LeanLab.Pintz2018.expneg_lower 3.9 (by norm_num) (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

/-- `log l ≤ -3.9` for `0 < l ≤ 0.02`. -/
theorem log_le_of_small {l : ℝ} (h0 : 0 < l) (h1 : l ≤ 0.02) : log l ≤ -3.9 := by
  have : l ≤ exp (-3.9) := h1.trans m_e39
  have := log_le_log h0 this
  rwa [log_exp] at this

/-- `e^{-x} ≤ 1 - x + (3/4) x²` for `0 ≤ x ≤ 1`, from `Real.exp_bound` with `n = 2`. -/
theorem expneg_quad {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : exp (-x) ≤ 1 - x + 3 / 4 * x ^ 2 := by
  have h := Real.exp_bound (x := -x) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 2)
    (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  rw [abs_neg, abs_of_nonneg h0] at h
  norm_num at h
  have := (abs_le.mp h).2
  nlinarith

/-- The two bounds for `e^{-(A-2)Λ*}` in Case 8 at weight `A ≥ 17/5`. PROVED, no input.
Plain math: if `Λ* ≥ 3.96` and `Λ* ≥ (12/11 - ε) log(1/λ₁)`, `ε ≤ 1/100`, `0 < λ₁ ≤ 1`, then
`e^{-(A-2)Λ*} ≤ 0.00392`, and `e^{-(A-2)Λ*} ≤ 0.143 λ₁` when `λ₁ ≤ 0.02`. -/
theorem case8_u_bounds {A l Ls ε : ℝ} (hA : 17 / 5 ≤ A) (hl0 : 0 < l) (hl1 : l ≤ 1)
    (hε : ε ≤ 1 / 100) (hLs1 : 3.96 ≤ Ls) (hLs2 : (12 / 11 - ε) * log (1 / l) ≤ Ls) :
    exp (-((A - 2) * Ls)) ≤ 0.00392 ∧ (l ≤ 0.02 → exp (-((A - 2) * Ls)) ≤ 0.143 * l) := by
  have hlog : 0 ≤ log (1 / l) := log_nonneg (by rw [le_div_iff₀ hl0]; linarith)
  refine ⟨?_, fun hl2 => ?_⟩
  · have : exp (-((A - 2) * Ls)) ≤ exp (-5.544) := exp_le_exp.mpr (by nlinarith)
    linarith [m_e5544]
  · have hlg : log (1 / l) = -log l := by rw [one_div, log_inv]
    have hsm := log_le_of_small hl0 hl2
    have hg : 3 / 2 * log (1 / l) ≤ (A - 2) * Ls := by
      have h1 : (3 / 2 : ℝ) ≤ (A - 2) * (12 / 11 - ε) := by nlinarith
      have h2 : 0 ≤ A - 2 := by linarith
      calc 3 / 2 * log (1 / l) ≤ (A - 2) * (12 / 11 - ε) * log (1 / l) :=
            mul_le_mul_of_nonneg_right h1 hlog
        _ = (A - 2) * ((12 / 11 - ε) * log (1 / l)) := by ring
        _ ≤ (A - 2) * Ls := mul_le_mul_of_nonneg_left hLs2 h2
    have hstep : -((A - 2) * Ls) ≤ log l + (-1.95) := by rw [hlg] at hg; linarith
    calc exp (-((A - 2) * Ls)) ≤ exp (log l + (-1.95)) := exp_le_exp.mpr hstep
      _ = l * exp (-1.95) := by rw [exp_add, exp_log hl0]
      _ ≤ l * 0.143 := mul_le_mul_of_nonneg_left m_e195 hl0.le
      _ = 0.143 * l := by ring

/-- The final scalar inequality of Case 8 at `A ≥ 17/5`. PROVED, no input.
Plain math: if `0 < λ₁ ≤ 0.04`, `u ≤ 0.00392`, and `u ≤ 0.143 λ₁` when `λ₁ ≤ 0.02`, then
`e^{-2Aλ₁} + 26.78 u < 1`. -/
theorem case8_scalar {A l u : ℝ} (hA : 17 / 5 ≤ A) (hl0 : 0 < l) (hl1 : l ≤ 0.04)
    (hu1 : u ≤ 0.00392) (hu2 : l ≤ 0.02 → u ≤ 0.143 * l) :
    exp (-(2 * A) * l) + 26.78 * u < 1 := by
  have he : exp (-(2 * A) * l) ≤ exp (-(6.8 * l)) := exp_le_exp.mpr (by nlinarith)
  rcases le_or_gt l 0.02 with hl | hl
  · have hq := expneg_quad (x := 6.8 * l) (by positivity) (by linarith)
    have := hu2 hl
    have hll : l * l ≤ 0.02 * l := mul_le_mul_of_nonneg_right hl hl0.le
    nlinarith
  · have : exp (-(6.8 * l)) ≤ exp (-0.136) := exp_le_exp.mpr (by linarith)
    linarith [m_e0136]

section Cases
variable {ι κ : Type*}

/-- **Case 8 at every weight `A ≥ 17/5`.** CONDITIONAL ON the same quoted inputs as
`Pintz2018Slack.case8_closes` and `Pintz2018Slack2.case8_closes_gen`: Theorem G and Table 5
of [9] as (9.31), one zero `λ₁ ∈ (0, 0.04]` and all others at `λ ≥ Λ*`, `Λ* ≥ 3.96`,
`Λ* ≥ (12/11 - ε) log(1/λ₁)`; Corollary 1 as (9.32) with the term of `ϱ₁` added.

Plain math: then for every `A ≥ 17/5`, at weight `A` and cut `Λ*`, `S₀ = Σ_i (a_i + b_i)² < 1`.
At `A = 17/5` the level is `ϑ = 5/17` and the exponent `12/17 = 0.70588...`. -/
theorem case8_closes_low {A : ℝ} (hA : 17 / 5 ≤ A) {I : Finset κ} {Z : κ → Finset ι}
    {lam : ι → ℝ} {H Ls ε : ℝ} {i1 : κ} {j1 : ι} (hLH : Ls ≤ H)
    (hZH : ∀ i ∈ I, ∀ j ∈ Z i, lam j ≤ H) (hi1 : i1 ∈ I) (hj1 : j1 ∈ Z i1)
    (hsingle : ∀ i ∈ I, ∀ j ∈ Z i, lam j < Ls → i = i1 ∧ j = j1)
    (hl0 : 0 < lam j1) (hl1 : lam j1 ≤ 0.04) (hε : ε ≤ 1 / 100)
    (hLs1 : 3.96 ≤ Ls) (hLs2 : (12 / 11 - ε) * log (1 / lam j1) ≤ Ls)
    (h932a : ∑ i ∈ I, KS (8 / 3) Ls (Z i) lam ≤ 10.4 + exp (-(8 / 3 * Ls)))
    (h932b : ∀ i ∈ I, KS 2 Ls (Z i) lam ≤ 10.4 + exp (-(2 * Ls))) :
    ∑ i ∈ I, (aS A Ls (Z i) lam + bS A Ls H (Z i) lam) ^ 2 < 1 := by
  set l := lam j1
  have hA0 : 0 ≤ A := by linarith
  have hasum : ∑ i ∈ I, aS A Ls (Z i) lam ≤ exp (-(A * l)) := by
    rw [aS_single hi1 hj1 hsingle, min_eq_left (by linarith : l ≤ Ls)]
    linarith [exp_pos (-(A * Ls))]
  obtain ⟨hu1, hu2⟩ := case8_u_bounds hA hl0 (by linarith) hε hLs1 hLs2
  set u := exp (-((A - 2) * Ls)) with hud
  have hu0 : 0 ≤ u := (exp_pos _).le
  have hm2 : exp (-(2 * Ls)) ≤ 0.01 := by
    have h1 := LeanLab.Pintz2018.expneg_upper 7.92 (by norm_num)
    simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
    norm_num at h1
    have : exp (-(2 * Ls)) ≤ exp (-7.92) := exp_le_exp.mpr (by linarith)
    linarith
  have hbi : ∀ i ∈ I, bS A Ls H (Z i) lam ≤ 10.41 * u := by
    intro i hi
    have h1 := bS_tail (A := A) (B := 2) (Λ := Ls) (H := H) (by linarith) (Z i) lam
    have h2 := h932b i hi
    calc bS A Ls H (Z i) lam ≤ u * KS 2 Ls (Z i) lam := h1
      _ ≤ u * 10.41 := mul_le_mul_of_nonneg_left (by linarith) hu0
      _ = _ := by ring
  have hm83 : exp (-(8 / 3 * Ls)) ≤ 0.01 := by
    have : exp (-(8 / 3 * Ls)) ≤ exp (-(2 * Ls)) := exp_le_exp.mpr (by linarith)
    linarith
  have hbsum : ∑ i ∈ I, bS A Ls H (Z i) lam ≤ 0.572 := by
    have he : exp (-((A - 8 / 3) * Ls)) ≤ 0.0549 := by
      have : exp (-((A - 8 / 3) * Ls)) ≤ exp (-2.904) := exp_le_exp.mpr (by nlinarith)
      linarith [m_e2904]
    calc ∑ i ∈ I, bS A Ls H (Z i) lam
        ≤ ∑ i ∈ I, exp (-((A - 8 / 3) * Ls)) * KS (8 / 3) Ls (Z i) lam :=
          sum_le_sum fun i _ => bS_tail (by linarith) _ _
      _ = exp (-((A - 8 / 3) * Ls)) * ∑ i ∈ I, KS (8 / 3) Ls (Z i) lam := by rw [mul_sum]
      _ ≤ 0.0549 * 10.41 := mul_le_mul he (by linarith)
          (sum_nonneg fun i _ => KS_nonneg _ _ _ _) (by norm_num)
      _ ≤ 0.572 := by norm_num
  have hb := LeanLab.Pintz2018.basic_ineq I (fun i => aS A Ls (Z i) lam)
    (fun i => bS A Ls H (Z i) lam) (10.41 * u) (exp (-(A * l))) 0.572
    (by positivity) (fun i _ => aS_nonneg hA0 _ _) (fun i hi => bS_nonneg hA0 (hZH i hi) hLH)
    hbi hasum hbsum
  refine lt_of_le_of_lt hb ?_
  have he1 : exp (-(A * l)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hsq : exp (-(A * l)) ^ 2 = exp (-(2 * A) * l) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hsc := case8_scalar hA hl0 hl1 hu1 hu2
  have : 10.41 * u * (2 * exp (-(A * l)) + 0.572) ≤ 26.78 * u := by
    nlinarith [(exp_pos (-(A * l))).le]
  rw [hsq]
  linarith

/-- Vacuity instance for `case8_closes_low` at `A = 17/5`: one zero at `λ₁ = e^{-4} ≤ 0.04`,
`Λ* = H = 5`, `ε = 0`, so `(12/11) log(1/λ₁) = 48/11 ≤ 5`. -/
theorem case8_closes_low_vacuity :
    ∑ _i ∈ ({0} : Finset ℕ), (aS (17 / 5) 5 ({0} : Finset ℕ) (fun _ => exp (-4)) +
      bS (17 / 5) 5 5 ({0} : Finset ℕ) (fun _ => exp (-4))) ^ 2 < 1 := by
  have hl : exp (-4 : ℝ) ≤ 0.04 := by
    have h1 := LeanLab.Pintz2018.expneg_upper 4 (by norm_num)
    simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
    norm_num at h1
    linarith
  have hlog : log (1 / exp (-4 : ℝ)) = 4 := by rw [one_div, ← exp_neg, log_exp]; norm_num
  have h4 : exp (-4 : ℝ) < 5 := by linarith
  have := case8_closes_low (ι := ℕ) (κ := ℕ) (A := 17 / 5) le_rfl (I := {0}) (Z := fun _ => {0})
    (lam := fun _ => exp (-4)) (H := 5) (Ls := 5) (ε := 0) (i1 := 0) (j1 := 0) le_rfl
    (by intro _ _ _ _; linarith) (by simp) (by simp) (by intro i hi j hj _; simp_all)
    (exp_pos _) hl (by norm_num) (by norm_num) (by rw [hlog]; norm_num)
    (by
      simp only [KS, sum_singleton]
      rw [max_eq_right h4.le]
      linarith [exp_pos (-(8 / 3 * (5 : ℝ)))])
    (by
      intro i _
      simp only [KS, sum_singleton]
      rw [max_eq_right h4.le]
      linarith [exp_pos (-(2 * (5 : ℝ)))])
  simpa using this

end Cases

/-- The level and exponent at `A = 17/5`: `ϑ = 5/17`, `1 - ϑ = 12/17 < 0.706 < 0.72`. -/
theorem exponent_17_5 : 1 / (17 / 5 : ℝ) = 5 / 17 ∧ 1 - 1 / (17 / 5 : ℝ) = 12 / 17 ∧
    (12 / 17 : ℝ) < 0.706 ∧ (0.706 : ℝ) < 0.72 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The binding map of Section 9 as the order of the three weight floors, from the numerics:
Case 8 needs `A ≥ 17/5` here, proved; Case 7 at the `Λ₁` reconstruction needs about
`A > 3.4837`; Cases 1 to 6 with the printed inputs need about `A > 3.5684`. Only the first is
a theorem; this lemma records that `17/5` lies below both other floors, so Case 8 never binds. -/
theorem case8_floor_below : (17 / 5 : ℝ) < 3.4837 ∧ (3.4837 : ℝ) < 3.5684 ∧
    (3.5684 : ℝ) < 25 / 7 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end LeanLab.ExceptionalSet.Pintz2018U6815Case8

#print axioms LeanLab.ExceptionalSet.Pintz2018U6815Case8.case8_u_bounds
#print axioms LeanLab.ExceptionalSet.Pintz2018U6815Case8.case8_scalar
#print axioms LeanLab.ExceptionalSet.Pintz2018U6815Case8.case8_closes_low
#print axioms LeanLab.ExceptionalSet.Pintz2018U6815Case8.case8_closes_low_vacuity
#print axioms LeanLab.ExceptionalSet.Pintz2018U6815Case8.exponent_17_5
#print axioms LeanLab.ExceptionalSet.Pintz2018U6815Case8.case8_floor_below
#print axioms LeanLab.ExceptionalSet.Pintz2018U6815Case8.expneg_quad
#print axioms LeanLab.ExceptionalSet.Pintz2018U6815Case8.log_le_of_small
