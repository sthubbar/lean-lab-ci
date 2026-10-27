import LeanLab.GoldbachAverage.WeightedPrefixBound82

/-!
The weighted increment in P0051 page 10 eq. 55.
This continues the unfinished Gallagher variance proof without asserting that analytic input.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.WeightedIncrement124
open MeasureTheory Filter
open FloorVariance82 WeightedPrefix82 WeightedPrefixBound82

/-- The weighted short interval coefficient sum in P0051 page 10 eq. 55. -/
def weightedIncrement (N : ℕ) (x h : ℝ) : ℝ :=
  weightedPrefix N (x + h) - weightedPrefix N x

/-- Weighted R is integrable on every compact nonnegative interval.
Source: the integral on the first line of P0051 page 10 eq. 55. -/
theorem weighted_R_integrable (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => psiFloorError t * Real.exp (-t / N)) volume a b := by
  have hb : 0 ≤ b := ha.trans hab
  have hR : IntervalIntegrable psiFloorError volume 0 b := by
    refine ⟨memLp_one_iff_integrable.mp (R_memLp hb 1), ?_⟩
    rw [Set.Ioc_eq_empty_of_le hb]
    exact integrableOn_empty
  have hRab : IntervalIntegrable psiFloorError volume a b := by
    apply hR.mono_set
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hb]
    intro t ht
    exact ⟨ha.trans ht.1, ht.2⟩
  apply hRab.mul_continuousOn
  fun_prop

/-- LEAF. P0051 page 10 eq. 55, first line, the exact weighted increment Abel identity. -/
theorem weighted_increment_abel (N : ℕ) (hN : 1 ≤ N) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h) :
    weightedIncrement N x h =
      psiFloorError (x + h) * Real.exp (-(x + h) / N) -
      psiFloorError x * Real.exp (-x / N) +
      1 / (N : ℝ) * ∫ u in x..(x + h), psiFloorError u * Real.exp (-u / N) := by
  have hxh : x ≤ x + h := by linarith
  have hxhp : 0 ≤ x + h := by linarith
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (weighted_R_integrable N (le_refl (0 : ℝ)) hx)
    (weighted_R_integrable N hx hxh)
  rw [weightedIncrement, weighted_prefix_abel N hN hxhp, weighted_prefix_abel N hN hx]
  rw [← hi]
  ring

/-- The exponential endpoint error has the factor h over N in P0051 page 10 eq. 55. -/
theorem endpoint_weight_error (N : ℕ) (hN : 1 ≤ N) (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |psiFloorError (x + h) * (Real.exp (-(x + h) / N) - Real.exp (-x / N))| ≤
      h / N * |psiFloorError (x + h)| * Real.exp (-x / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hhN : 0 ≤ h / N := div_nonneg hh hN0.le
  have he : Real.exp (-h / N) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa only [neg_div] using neg_nonpos.mpr hhN
  have heq : Real.exp (-(x + h) / N) = Real.exp (-x / N) * Real.exp (-h / N) := by
    rw [show -(x + h) / (N : ℝ) = -x / N + -h / N by ring, Real.exp_add]
  have hdiff : Real.exp (-(x + h) / N) - Real.exp (-x / N) =
      -(Real.exp (-x / N) * (1 - Real.exp (-h / N))) := by rw [heq]; ring
  have hsmall : 1 - Real.exp (-h / N) ≤ h / N := by
    have := Real.add_one_le_exp (-h / (N : ℝ))
    simp only [neg_div] at this ⊢
    linarith
  rw [hdiff, abs_mul, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (sub_nonneg.mpr he)]
  calc |psiFloorError (x + h)| * (Real.exp (-x / N) * (1 - Real.exp (-h / N)))
      ≤ |psiFloorError (x + h)| * (Real.exp (-x / N) * (h / N)) := by gcongr
    _ = _ := by ring

/-- LEAF. P0051 page 10 eq. 55 with both implicit error constants equal to one. -/
theorem weighted_increment_error (N : ℕ) (hN : 1 ≤ N) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h) :
    |weightedIncrement N x h -
      (psiFloorError (x + h) - psiFloorError x) * Real.exp (-x / N)| ≤
      h / N * |psiFloorError (x + h)| * Real.exp (-x / N) +
      1 / (N : ℝ) * ∫ u in x..(x + h), |psiFloorError u| * Real.exp (-u / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hi : IntervalIntegrable (fun u => |psiFloorError u| * Real.exp (-u / N))
      volume x (x + h) := by
    simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using
      (weighted_R_integrable N hx (by linarith : x ≤ x + h)).abs
  have hn : |∫ u in x..(x + h), psiFloorError u * Real.exp (-u / N)| ≤
      ∫ u in x..(x + h), |psiFloorError u| * Real.exp (-u / N) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      intervalIntegral.norm_integral_le_integral_norm
        (f := fun u => psiFloorError u * Real.exp (-u / N))
        (show x ≤ x + h by linarith)
  have heq : weightedIncrement N x h -
      (psiFloorError (x + h) - psiFloorError x) * Real.exp (-x / N) =
      psiFloorError (x + h) * (Real.exp (-(x + h) / N) - Real.exp (-x / N)) +
      1 / (N : ℝ) * ∫ u in x..(x + h), psiFloorError u * Real.exp (-u / N) := by
    rw [weighted_increment_abel N hN hx hh]
    ring
  rw [heq]
  calc |psiFloorError (x + h) * (Real.exp (-(x + h) / N) - Real.exp (-x / N)) +
        1 / (N : ℝ) * ∫ u in x..(x + h), psiFloorError u * Real.exp (-u / N)|
      ≤ |psiFloorError (x + h) * (Real.exp (-(x + h) / N) - Real.exp (-x / N))| +
        |1 / (N : ℝ) * ∫ u in x..(x + h), psiFloorError u * Real.exp (-u / N)| := abs_add_le _ _
    _ ≤ h / N * |psiFloorError (x + h)| * Real.exp (-x / N) +
        1 / (N : ℝ) * ∫ u in x..(x + h), |psiFloorError u| * Real.exp (-u / N) := by
      apply add_le_add (endpoint_weight_error N hN x hh)
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hN0)]
      exact mul_le_mul_of_nonneg_left hn (by positivity)

/-- The prefix difference is exactly the finite short interval coefficient sum.
Source: P0051 page 10 eq. 55 left side, with the positive index normalization. -/
theorem weighted_increment_eq_sum (N : ℕ) {x h : ℝ} (hh : 0 ≤ h) :
    weightedIncrement N x h = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊,
      Real.exp (-(n : ℝ) / N) * cfr n := by
  let f : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / N) * cfr n
  have hlo : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_mono (by linarith : x ≤ x + h)
  have hs := Finset.sum_Ico_eq_sub f (Nat.succ_le_succ hlo)
  have hsets : Finset.Ico (⌊x⌋₊ + 1) (⌊x + h⌋₊ + 1) =
      Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊ := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [hsets] at hs
  simpa only [weightedIncrement, weightedPrefix, ← Nat.range_succ_eq_Icc_zero, f] using hs.symm

end LeanLab.GoldbachAverage.WeightedIncrement124
