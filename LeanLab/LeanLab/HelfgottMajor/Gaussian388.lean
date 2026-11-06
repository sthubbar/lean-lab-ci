import LeanLab.HelfgottMajor.DecompJ1153

/-!
Endpoint and sign checks for the middle zero ranges on P0014 pages 39 and 40.
These checks do not supply a discrete sampling estimate from Plancherel.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Gaussian388
open Real DecompJ1153

/-- The inverse height sum is nonnegative, as used in the page 40 Cauchy-Schwarz step. -/
theorem inv_im_sum_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    0 ≤ invImSum χ T := by
  unfold invImSum
  apply tsum_nonneg
  intro ρ
  simp only [Set.indicator_apply]
  split_ifs <;> positivity

/-- The discrete Gaussian moment is nonnegative.
Source P0014 page 39, the nonnegative middle range under consideration.
-/
theorem gaussian_moment_sum_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : 0 ≤ gaussianMomentSum χ δ T := by
  unfold gaussianMomentSum
  apply tsum_nonneg
  intro ρ
  simp only [Set.indicator_apply]
  split_ifs <;> positivity

/-- There is no middle inverse height contribution below height 1.
Source P0014 page 39, the split at absolute imaginary part 1.
-/
theorem inv_im_sum_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : T ≤ 1) : invImSum χ T = 0 := by
  unfold invImSum
  calc
    _ = ∑' _ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, (0 : ℝ) := by
      apply tsum_congr
      intro ρ
      have hi : |ρ.val.im| ≤ 1 := ρ.property.2.2.2.trans hT
      simp [hi]
    _ = 0 := tsum_zero

/-- There is no middle Gaussian moment contribution below height 1.
Source P0014 page 39, the split at absolute imaginary part 1.
-/
theorem gaussian_moment_sum_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : T ≤ 1) : gaussianMomentSum χ δ T = 0 := by
  unfold gaussianMomentSum
  calc
    _ = ∑' _ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, (0 : ℝ) := by
      apply tsum_congr
      intro ρ
      have hi : |ρ.val.im| ≤ 1 := ρ.property.2.2.2.trans hT
      simp [hi]
    _ = 0 := tsum_zero

/-- The sealed Gaussian moment inequality holds at its lower endpoint T equal to 1.
This proves only the empty middle range, not the general leaf.
Source P0014 page 39, the strict lower bound on the middle range.
-/
theorem gaussian_moment_sum_bound_at_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ : ℝ) :
    sqrt (gaussianMomentSum χ δ 1) ≤ sqrt Sec45.nTwo * sqrt 1 + sqrt Sec45.nLog * sqrt 1 := by
  rw [gaussian_moment_sum_eq_zero χ δ 1 le_rfl, sqrt_zero]
  positivity

/-- The Gaussian half moment has the Gamma value in display 4.42 on page 43.
This identity does not assert the separate decimal bound 2.15581.
-/
theorem gaussian_half_moment :
    (∫ t in Set.Ioi (0 : ℝ), t ^ ((1 : ℝ) / 2 - 1) * exp (-t ^ 2 / 2)) =
      Gamma (1 / 4) / (2 : ℝ) ^ ((3 : ℝ) / 4) := by
  have hg := Gaussian269.gaussian_moment (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  have hi : (∫ t in Set.Ioi (0 : ℝ), t ^ ((1 : ℝ) / 2 - 1) * exp (-t ^ 2 / 2)) =
      ∫ t in Set.Ioi (0 : ℝ), t ^ ((1 : ℝ) / 2 - 1) * exp (-((1 / 2) * t ^ 2)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [show -t ^ 2 / 2 = -((1 / 2 : ℝ) * t ^ 2) by ring]
  rw [hi, hg]
  norm_num only [show (1 : ℝ) / (1 / 2) = 2 by norm_num,
    show ((1 : ℝ) / 2) / 2 = 1 / 4 by norm_num]
  apply (eq_div_iff (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne').mpr
  have hp : (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ ((3 : ℝ) / 4) = 2 := by
    rw [← rpow_add (by norm_num)]
    norm_num
  calc
    _ = (1 / 2 : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ ((3 : ℝ) / 4)) * Gamma (1 / 4) := by ring
    _ = _ := by rw [hp]; ring

/-- The critical line Mellin norm is bounded by the Gaussian half moment.
Source P0014 page 39 display 4.30 and page 43 display 4.42.
-/
theorem mellin_norm_le_gamma_quarter (δ : ℝ) (s : ℂ) (hs : s.re = 1 / 2) :
    ‖Decomp269a.gaussianMellin δ s‖ ≤ Gamma (1 / 4) / (2 : ℝ) ^ ((3 : ℝ) / 4) := by
  have h := Gaussian269.mellin_norm_le δ s
  rw [hs, gaussian_half_moment] at h
  exact h

end LeanLab.HelfgottMajor.Gaussian388
