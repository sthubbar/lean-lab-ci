import LeanLab.GoldbachAverage.VarianceTails124

/-!
P0051 page 11 eq. 56, with explicit constants and convergent series.
AI wrote this Lean code. Goldbach is open.
-/

set_option maxHeartbeats 800000

noncomputable section
namespace LeanLab.GoldbachAverage.VarianceComparison124
open MeasureTheory Set Filter
open FloorVariance82 VarianceTails124 I2Bound124

/-- The first moment of the half geometric prefix weights is two N.
Source context: the absorbed N term in P0051 page 11 eq. 56.
Mathlib hasSum_coe_mul_geometric_of_norm_lt_one supplies the moment. -/
theorem linear_prefix_sum (N : ℝ) :
    HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * (((j : ℝ) + 1) * N)) (2 * N) := by
  have hs := (hasSum_nat_add_iff' 1).mpr
    (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num))
  have hs' : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * ((j : ℝ) + 1)) 2 := by
    norm_num only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero,
      show (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 = 2 by norm_num] at hs
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hs
  simpa only [mul_assoc] using hs'.mul_right N

/-- A prefix comparison with additive error two T passes to the convergent geometric series.
Source: P0051 page 10 eqs. 51 and 52 and page 11 eq. 56. -/
theorem prefix_series_comparison {F G : ℝ → ℝ} {N : ℝ}
    (hN : 0 < N)
    (hF : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * F (((j : ℝ) + 1) * N)))
    (hG : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * G (((j : ℝ) + 1) * N)))
    (hb : ∀ T : ℝ, 0 ≤ T → F T ≤ 2 * G T + 2 * T) :
    (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * F (((j : ℝ) + 1) * N)) ≤
      2 * (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * G (((j : ℝ) + 1) * N)) + 4 * N := by
  have hs := (hG.hasSum.mul_left (2 : ℝ)).add ((linear_prefix_sum N).mul_left (2 : ℝ))
  have hp (j : ℕ) : (1 / 2 : ℝ) ^ (j + 1) * F (((j : ℝ) + 1) * N) ≤
      2 * ((1 / 2 : ℝ) ^ (j + 1) * G (((j : ℝ) + 1) * N)) +
      2 * ((1 / 2 : ℝ) ^ (j + 1) * (((j : ℝ) + 1) * N)) := by
    have hm := mul_le_mul_of_nonneg_left (hb (((j : ℝ) + 1) * N) (by positivity))
      (show 0 ≤ (1 / 2 : ℝ) ^ (j + 1) by positivity)
    nlinarith only [hm]
  have hc := hasSum_le hp hF.hasSum hs
  convert hc using 1 <;> ring

/-- LEAF. The exponential R square mass is bounded by H tails and the floor error.
Source: P0051 page 11 eq. 56, using page 10 eq. 51. -/
theorem rMass_H_bound (N : ℕ) (hN : 1 ≤ N) :
    rMass N ≤ 4 * (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
      InghamTheta.H (((j : ℝ) + 1) * N)) + 8 * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := rMass_prefix_bound N hN
  have hc := prefix_series_comparison
    (F := fun T => ∫ t in (0 : ℝ)..T, psiFloorError t ^ 2)
    (G := InghamTheta.H) hN0 hp.1 (H_series_summable hN0)
    (fun T hT => floor_prefix_bound hT)
  linarith only [hp.2, hc]

/-- LEAF. The exponential R increment square mass is bounded by J tails and the floor error.
Source: P0051 page 11 eq. 56, using page 10 eq. 52. -/
theorem deltaMass_J_bound (N : ℕ) (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h) :
    deltaMass N h ≤ 4 * (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
      GSInputs.J (((j : ℝ) + 1) * N) h) + 8 * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := deltaMass_prefix_bound N hN hh
  have hc := prefix_series_comparison
    (F := fun T => ∫ t in (0 : ℝ)..T, (psiFloorError (t + h) - psiFloorError t) ^ 2)
    (G := fun T => GSInputs.J T h) hN0 hp.1 (J_series_summable hN0 hh)
    (fun T hT => floor_increment_bound hT hh)
  linarith only [hp.2, hc]

/-- LEAF. P0051 page 11 eq. 56 with explicit absolute constants.
Both series converge by VarianceTails124. No cited analytic input or RH is used. -/
theorem I2_HJ_bound (N : ℕ) (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h) (hhN : h ≤ N) :
    I2 N h ≤
      12 * (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * GSInputs.J (((j : ℝ) + 1) * N) h) +
      12 * (Real.exp 2 + 1) * (h / N) ^ 2 *
        (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * InghamTheta.H (((j : ℝ) + 1) * N)) +
      (24 * Real.exp 2 + 48) * N := by
  have hi := (I2_weighted_bound N hN hh hhN).2
  have hd := deltaMass_J_bound N hN hh
  have hr := mul_le_mul_of_nonneg_left (rMass_H_bound N hN)
    (show 0 ≤ 3 * (Real.exp 2 + 1) * (h / N) ^ 2 by positivity)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio : 0 ≤ h / N ∧ h / N ≤ 1 :=
    ⟨div_nonneg hh hN0.le, (div_le_one hN0).mpr hhN⟩
  have hs : (h / N) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (h / N)]
  have he := Real.exp_pos (2 : ℝ)
  have hcost := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 24 * (Real.exp 2 + 1) * (N : ℝ) by positivity)
  nlinarith only [hi, hd, hr, hcost]

end LeanLab.GoldbachAverage.VarianceComparison124
