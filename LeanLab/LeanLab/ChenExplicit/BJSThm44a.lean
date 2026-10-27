/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T0704Z-6940, unit U-0920.
P0009 Bordignon, Johnston, Starichkova, An explicit version of Chen's theorem and the
linear sieve, arXiv 2207.09452v6, 25 Jun 2025, read in Claude in Chrome per RULES_BLOCKERS B1.

Theorem 44 case (a), as printed in v6, opens its bracket with
`2 e^{-γ} log(3 - 8α₁) / (4 - 8α₁)`. The proof, display (143), and the definition (62)
`f(s) = 2 e^{γ} log(s - 1) / s` for `2 ≤ s ≤ 4` give `2 e^{γ} log(3 - 8α₁) / (4 - 8α₁)`;
case (b) of the same theorem also prints `e^{γ}`.

The printed bound is true, being weaker, but it cannot feed Section 9: with the Section 9
parameter `α₁ = α₂ = 10⁻⁵`, the printed main term of Theorem 44 (a) minus half the main term
of Theorem 50 (a) is already negative, whatever the nonnegative Theorem 51 term is. Every
error term in Theorems 44, 50 and 51 only makes the combination smaller, so the main-term
combination is an upper bound for `cA - cQ/2 - cB/2`.

PROVED here: `printed44a_lt_proof143`, the printed bracket is below the bracket of (143);
`printed44a_combo_neg`, the printed constant gives a negative Section 9 combination in
case (a). Main result of the paper: unaffected, Section 9 uses `e^{γ}`, see PROGRESS.md
and the Python check of this run.
-/
import Mathlib

open Real

noncomputable section
namespace LeanLab.ChenExplicit.BJS44a

/-- `α₁ = α₂ = 10⁻⁵`, Section 9. -/
def α : ℝ := 1 / 100000

/-- Theorem 44 (a), the main term of the bracket as printed, times the outside factor `8`.
The outside factor `1 - 32.02/log² N < 1` and the subtracted error terms are dropped,
which can only raise it. -/
def printedA : ℝ := 8 * (2 * exp (-eulerMascheroniConstant) * log (3 - 8 * α) / (4 - 8 * α))

/-- The same main term as in display (143) and (62), `8 f(4 - 8α₁)`. -/
def proofA : ℝ := 8 * (2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α))

/-- Theorem 50 (a), the main part `8.0004 · l₂(X₂)` with the factors
`X₂^{1/8}/(X₂^{1/8} - 1) ≥ 1`, `1 + 32.02/log² N ≥ 1` and the positive `512/(k log² X₂)`,
`ε C₁ e² h` and `l₁`, `l` terms dropped, which can only lower it. -/
def mainQ : ℝ :=
  8.0004 * (exp eulerMascheroniConstant / 4 *
    ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α)))

lemma log3_le : log (3 - 8 * α) ≤ log 3 :=
  Real.log_le_log (by norm_num [α]) (by norm_num [α])

lemma log3_pos : 0 < log (3 - 8 * α) := Real.log_pos (by norm_num [α])

lemma logratio_nonneg : 0 ≤ log ((3 - 8 * α) / (3 - 18 * α)) :=
  Real.log_nonneg (by rw [le_div_iff₀ (by norm_num [α])]; norm_num [α])

lemma exp_half_ge : (1.6 : ℝ) ≤ exp (1 / 2) := by
  have := Real.add_one_le_exp (1 / 2 : ℝ)
  have h2 : (1 + 1 / 2 + (1 / 2) ^ 2 / 2 : ℝ) ≤ exp (1 / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
    linarith
  norm_num at h2 ⊢; linarith

/-- **The printed bracket of Theorem 44 (a) is below the one its proof gives**, by the
factor `e^{-2γ}`. PROVED. -/
theorem printed44a_lt_proof143 : printedA < proofA := by
  unfold printedA proofA
  have hγ := one_half_lt_eulerMascheroniConstant
  have he : exp (-eulerMascheroniConstant) < exp eulerMascheroniConstant :=
    exp_lt_exp.mpr (by linarith)
  have hl := log3_pos
  have hd : (0 : ℝ) < 4 - 8 * α := by norm_num [α]
  have : 2 * exp (-eulerMascheroniConstant) * log (3 - 8 * α) <
      2 * exp eulerMascheroniConstant * log (3 - 8 * α) := by nlinarith
  have := div_lt_div_of_pos_right this hd
  linarith

/-- **Finding check, PROVED: the printed Theorem 44 (a) cannot give Section 9.**
With `α₁ = α₂ = 10⁻⁵`, the printed main term minus half the Theorem 50 (a) main term is
negative, for any nonnegative Theorem 51 constant `cB`. Numerically about
`2.467 - 6.383 < 0`; with the `e^{γ}` of (143) the left side is about `7.827 - 6.383`. -/
theorem printed44a_combo_neg (cB : ℝ) (hB : 0 ≤ cB) : printedA - mainQ / 2 - cB / 2 < 0 := by
  have hγa := one_half_lt_eulerMascheroniConstant
  have hγb := eulerMascheroniConstant_lt_two_thirds
  set u := exp (1 / 2 : ℝ) with hu
  have hu16 : (1.6 : ℝ) ≤ u := exp_half_ge
  have hneg : exp (-eulerMascheroniConstant) ≤ u⁻¹ := by
    rw [hu, ← exp_neg]; exact exp_le_exp.mpr (by linarith)
  have hpos : u ≤ exp eulerMascheroniConstant := exp_le_exp.mpr (by linarith)
  have l3 := log3_le
  have l3b := log_three_lt_d9
  have l3p := log3_pos
  have lr := logratio_nonneg
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l2a := log_two_gt_d9
  have l3a := log_three_gt_d9
  have hu0 : 0 < u := by linarith
  -- upper bound for printedA
  have hA : printedA ≤ 8 * (2 * (1 / 1.6) * 1.0986122888) / 3.99992 := by
    unfold printedA
    have hi : u⁻¹ ≤ 1 / 1.6 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hu16
    have e1 : 2 * exp (-eulerMascheroniConstant) * log (3 - 8 * α) ≤
        2 * (1 / 1.6) * 1.0986122888 := by
      have := exp_pos (-eulerMascheroniConstant)
      have : exp (-eulerMascheroniConstant) ≤ 1 / 1.6 := hneg.trans hi
      nlinarith
    have hd : (4 : ℝ) - 8 * α = 3.99992 := by norm_num [α]
    rw [hd, mul_div_assoc']
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left e1 (by norm_num : (0:ℝ) ≤ 8))
      (by norm_num : (0:ℝ) ≤ 3.99992)
    simpa [mul_div_assoc] using this
  -- lower bound for mainQ
  have hQ : 8.0004 * (u / 4 * (log 6 / (1 / 2))) ≤ mainQ := by
    unfold mainQ
    have hd : (1 : ℝ) / 2 - α = 0.49999 := by norm_num [α]
    rw [hd]
    have h1 : log 6 / (1 / 2) ≤ (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / 0.49999 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      have : 0 < log 6 := by rw [h6]; linarith
      nlinarith
    have h2 : 0 ≤ log 6 / (1 / 2) := by rw [h6]; positivity
    have h3 : u / 4 * (log 6 / (1 / 2)) ≤
        exp eulerMascheroniConstant / 4 *
          ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / 0.49999) := by
      apply mul_le_mul (by linarith) h1 h2 (by have := exp_pos eulerMascheroniConstant; positivity)
    linarith
  have hQ' : 8.0004 * (u / 4 * (log 6 / (1 / 2))) ≥ 8.0004 * (u / 4 * (1.79 / (1 / 2))) := by
    have : (1.79 : ℝ) ≤ log 6 := by rw [h6]; norm_num at l2a l3a ⊢; linarith
    gcongr
  have : 8.0004 * (u / 4 * (1.79 / (1 / 2))) ≥ 8.0004 * ((1.6 : ℝ) / 4 * (1.79 / (1 / 2))) := by
    gcongr
  norm_num at hA this ⊢
  linarith

end LeanLab.ChenExplicit.BJS44a
