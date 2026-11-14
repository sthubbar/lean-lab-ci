import LeanLab.ExceptionalSet.ParitySmoothing553
import LeanLab.ExceptionalSet.OddKernel467
import LeanLab.ExceptionalSet.KernelTail385

/-!
P0082 page370 displays40 and41, the existing corrected parity periodization.
The coefficients are an explicit dilation of the already proved shifted kernel.
The Fourier identity follows from the clean Poisson formula on main.
Source: https://doi.org/10.5802/aif.1621
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.ParityFourier553
open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (Kfun eC ftR)
open LeanLab.ExceptionalSet.OddKernel467 (evenKernel)
open LeanLab.ExceptionalSet.KernelTransform264 (weight)
open LeanLab.ExceptionalSet.ParityAudit467 (correctedParityPeriodization)

/-- P0082 page370 display40, explicit coefficients for the existing corrected weight. -/
noncomputable def coefficientKernel (Δ x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * evenKernel Δ ((1 / 2) * x)

/-- P0082 page370 display40, the coefficient kernel is integrable. -/
theorem coefficient_integrable (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    Integrable (coefficientKernel Δ) := by
  exact ((OddKernel467.evenKernel_integrable Δ hΔ hΔ1).comp_mul_left'
    (by norm_num : (1 / 2 : ℝ) ≠ 0)).const_mul (1 / 2 : ℂ)

/-- P0082 page370 display40, the explicit coefficient kernel is continuous. -/
theorem coefficient_continuous (Δ : ℝ) : Continuous (coefficientKernel Δ) := by
  exact continuous_const.mul ((OddKernel467.evenKernel_continuous Δ).comp
    (continuous_const.mul continuous_id))

/-- P0082 page370 display40, Fourier scaling of the explicit coefficients. -/
theorem ftR_coefficient (Δ y : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ftR (coefficientKernel Δ) y = (weight Δ (4 * y + 1) : ℂ) := by
  have hs : FourierTransform.fourier (fun x : ℝ =>
      (1 / 2 : ℂ) * evenKernel Δ ((1 / 2) * x)) y =
      (1 / 2 : ℂ) * FourierTransform.fourier (fun x : ℝ => evenKernel Δ ((1 / 2) * x)) y := by
    simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [Decomp404b.ftR_eq_fourier]
  change FourierTransform.fourier (fun x : ℝ =>
    (1 / 2 : ℂ) * evenKernel Δ ((1 / 2) * x)) y = _
  rw [hs, TriangleKernel264.fourier_comp_pos_mul (evenKernel Δ)
    (by norm_num : (0 : ℝ) < 1 / 2), ← Decomp404b.ftR_eq_fourier,
    OddKernel467.ftR_evenKernel Δ _ hΔ hΔ1]
  norm_num
  congr 1
  ring

/-- P0082 page370 display40, the transformed coefficient kernel has compact support. -/
theorem coefficient_transform_support (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ∀ y : ℝ, 1 < |y| → ftR (coefficientKernel Δ) y = 0 := by
  intro y hy
  rw [ftR_coefficient Δ y hΔ hΔ1]
  have hh : 1 ≤ |4 * y + 1| := by
    rw [le_abs]
    rcases lt_abs.mp hy with hy | hy
    · left
      linarith
    · right
      linarith
  rw [KernelTransform264.weight_zero hΔ hΔ1 hh]
  simp

/-- P0082 page370 before display40, exact Fourier series for the existing
corrected periodization. Both its weight and coefficients are explicit data. -/
theorem corrected_fourier_series (Δ x : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∑' h : ℤ, coefficientKernel Δ h * eC (h * x)) =
      (correctedParityPeriodization Δ x : ℂ) := by
  have hp := Decomp464j.poisson_summation_supplied (coefficientKernel Δ)
    (coefficient_integrable Δ hΔ hΔ1) (coefficient_continuous Δ)
    (coefficient_transform_support Δ hΔ hΔ1) (-x) 0
  have he (y : ℝ) := ftR_coefficient Δ y hΔ hΔ1
  have hz : eC (0 : ℝ) = 1 := by simp [U1539.eC]
  simp only [zero_add, zero_mul, hz, one_mul, mul_neg, neg_neg, he] at hp
  unfold correctedParityPeriodization
  rw [Complex.ofReal_tsum]
  calc
    _ = ∑' h : ℤ, (weight Δ (4 * (-x + (h : ℝ)) + 1) : ℂ) := hp
    _ = _ := by
      apply tsum_congr
      intro h
      congr 1
      ring

/-- P0082 page370 display40, exact norm of the explicit coefficient kernel. -/
theorem norm_coefficient (Δ x : ℝ) :
    ‖coefficientKernel Δ x‖ = (1 / 4 : ℝ) * |Kfun Δ (x / 4)| := by
  have he : (1 / 2 : ℝ) * ((1 / 2) * x) = x / 4 := by ring
  simp only [coefficientKernel, evenKernel, he, norm_mul, U1539.norm_eC, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num <;> ring

/-- P0082 page370 display40, uniform coefficient bound including frequency zero. -/
theorem coefficient_uniform (Δ x : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ‖coefficientKernel Δ x‖ ≤ 1 / 2 := by
  rw [norm_coefficient]
  have h := KernelTail385.kernel_abs_le_two_sub Δ (x / 4) hΔ hΔ1
  linarith

/-- P0082 page370 display40, explicit inverse square coefficient decay.
The nonzero frequency hypothesis preserves the ordinary real division convention. -/
theorem coefficient_inverse_square (Δ x : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hx : x ≠ 0) :
    ‖coefficientKernel Δ x‖ ≤ 4 / (Δ * (Real.pi * x) ^ 2) := by
  have h := KernelTail385.kernel_abs_le_inverse_square Δ (x / 4) hΔ hΔ1
    (div_ne_zero hx (by norm_num))
  calc
    _ = (1 / 4 : ℝ) * |Kfun Δ (x / 4)| := norm_coefficient Δ x
    _ ≤ (1 / 4 : ℝ) * (1 / (Δ * (Real.pi * (x / 4)) ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by field_simp [hΔ.ne', Real.pi_ne_zero, hx] <;> ring

/-- P0082 page370 display40, a convenient constant one for nonzero coefficients. -/
theorem coefficient_nonzero_bound (Δ x : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hx : x ≠ 0) : ‖coefficientKernel Δ x‖ ≤ 1 / (Δ * x ^ 2) := by
  apply (coefficient_inverse_square Δ x hΔ hΔ1 hx).trans
  have hD : 0 < Δ * (Real.pi * x) ^ 2 := mul_pos hΔ (sq_pos_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx))
  have hD' : 0 < Δ * x ^ 2 := mul_pos hΔ (sq_pos_of_ne_zero hx)
  apply (div_le_div_iff₀ hD hD').mpr
  have hp : 4 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hΔ.le (sq_nonneg x))]

/-- P0082 page370 display40, absolute summability of the actual integer coefficients. -/
theorem coefficient_norm_summable (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    Summable (fun h : ℤ => ‖coefficientKernel Δ h‖) := by
  let S : TopologicalSpace.Compacts ℝ := ⟨{0}, isCompact_singleton⟩
  have hc := coefficient_continuous Δ
  have hs := Decomp464i.leaf_translate_norm_supplied (coefficientKernel Δ)
    (coefficient_integrable Δ hΔ hΔ1) hc (coefficient_transform_support Δ hΔ hΔ1) S
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _ hs
  intro h
  have hb := (((⟨coefficientKernel Δ, hc⟩ : C(ℝ, ℂ)).comp
    (ContinuousMap.addRight (h : ℝ))).restrict S).norm_coe_le_norm ⟨0, by simp [S]⟩
  simpa only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ContinuousMap.coe_addRight, zero_add] using hb

/-- P0082 page370 display41, absolute convergence survives a unit phase. -/
theorem coefficient_phase_summable (Δ x : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    Summable (fun h : ℤ => coefficientKernel Δ h * eC (h * x)) := by
  apply Summable.of_norm
  simpa only [norm_mul, U1539.norm_eC, mul_one] using coefficient_norm_summable Δ hΔ hΔ1

/-- P0082 page370 display41, interchange of the actual corrected Fourier
series with any finite weighted block sum. Absolute convergence is proved above. -/
theorem weighted_fourier_identity (s : Finset ℕ) (v : ℕ → ℝ) (f : ℕ → ℂ)
    (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∑ n ∈ s, (correctedParityPeriodization Δ (v n / 2) : ℂ) * f n) =
      ∑' h : ℤ, coefficientKernel Δ h * (∑ n ∈ s, eC (h * (v n / 2)) * f n) := by
  let g := fun (n : ℕ) (h : ℤ) => coefficientKernel Δ h * eC (h * (v n / 2)) * f n
  have hs (n : ℕ) (_ : n ∈ s) : Summable (g n) :=
    (coefficient_phase_summable Δ (v n / 2) hΔ hΔ1).mul_right (f n)
  calc
    _ = ∑ n ∈ s, ∑' h : ℤ, g n h := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [g]
      rw [tsum_mul_right, corrected_fourier_series Δ (v n / 2) hΔ hΔ1]
    _ = ∑' h : ℤ, ∑ n ∈ s, g n h := (Summable.tsum_finsetSum hs).symm
    _ = _ := by
      apply tsum_congr
      intro h
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [g]
      ring

/-- P0082 page370 second equality of display41, the actual corrected
smooth block phase is a series of shifted unfiltered block phases. -/
theorem phase_fourier_identity (s : Finset ℕ) (v : ℕ → ℝ) (t Δ : ℝ)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∑ n ∈ s, (correctedParityPeriodization Δ (v n / 2) : ℂ) * eC (t * v n)) =
      ∑' h : ℤ, coefficientKernel Δ h * (∑ n ∈ s, eC ((t + h / 2) * v n)) := by
  rw [weighted_fourier_identity s v (fun n => eC (t * v n)) Δ hΔ hΔ1]
  apply tsum_congr
  intro h
  apply congrArg (fun z : ℂ => coefficientKernel Δ h * z)
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Fejer467.phase_add]
  congr 1
  ring

/-- P0082 page370 display41, full Fourier approximation error for any
finite even parity block. Only the boundary count remains on the right. -/
theorem parity_fourier_error (s : Finset ℕ) (v : ℕ → ℝ) (t Δ : ℝ)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ‖(∑ n ∈ s.filter (fun n => Even ⌊v n⌋), eC (t * v n)) -
      ∑' h : ℤ, coefficientKernel Δ h * (∑ n ∈ s, eC ((t + h / 2) * v n))‖ ≤
        ((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
          1 - Δ / 2 < Int.fract (v n))).card : ℝ) := by
  have h := ParitySmoothing553.finite_parity_smoothing_error s v
    (fun n => eC (t * v n)) Δ hΔ hΔ1 (fun n hn => (U1539.norm_eC _).le)
  rw [phase_fourier_identity s v t Δ hΔ hΔ1] at h
  exact h

/-- P0082 page369 cognate odd case, the integer shift changes only a unit
factor in each Fourier coefficient. -/
theorem shifted_coefficient_norm (Δ t : ℝ) (h j : ℤ) :
    ‖coefficientKernel Δ h * eC (h * j / 2 - t * j)‖ = ‖coefficientKernel Δ h‖ := by
  rw [norm_mul, U1539.norm_eC, mul_one]

/-- P0082 page369 cognate odd case and page370 display41, exact corrected
Fourier identity for both shifted parity phase conventions. -/
theorem shifted_phase_fourier_identity (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ)
    (j : ℤ) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∑ n ∈ s, (correctedParityPeriodization Δ ((v n + j) / 2) : ℂ) * eC (t * (v n - j))) =
      ∑' h : ℤ, (coefficientKernel Δ h * eC (h * j / 2 - t * j)) *
        (∑ n ∈ s, eC ((t + h / 2) * v n)) := by
  rw [weighted_fourier_identity s (fun n => v n + j) (fun n => eC (t * (v n - j))) Δ hΔ hΔ1]
  apply tsum_congr
  intro h
  have he (n : ℕ) :
      eC (h * ((v n + j) / 2)) * eC (t * (v n - j)) =
        eC (h * j / 2 - t * j) * eC ((t + h / 2) * v n) := by
    rw [← Fejer467.phase_add, ← Fejer467.phase_add]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

/-- P0082 page369 cognate odd case and page370 display41, actual Fourier
approximation error for either shifted parity on any finite block. -/
theorem shifted_parity_fourier_error (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ)
    (j : ℤ) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ‖(∑ n ∈ s.filter (fun n => Even (⌊v n⌋ + j)), eC (t * (v n - j))) -
      ∑' h : ℤ, (coefficientKernel Δ h * eC (h * j / 2 - t * j)) *
        (∑ n ∈ s, eC ((t + h / 2) * v n))‖ ≤
        ((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
          1 - Δ / 2 < Int.fract (v n))).card : ℝ) := by
  have h := ParitySmoothing553.finite_shifted_parity_smoothing_error s v
    (fun n => eC (t * (v n - j))) j Δ hΔ hΔ1 (fun n hn => (U1539.norm_eC _).le)
  rw [shifted_phase_fourier_identity s v t j Δ hΔ hΔ1] at h
  exact h

end LeanLab.ExceptionalSet.ParityFourier553
