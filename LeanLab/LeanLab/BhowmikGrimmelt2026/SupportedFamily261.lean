/-
A second moment bound using pointwise control on the multiplier support.
Source: P0029 page 27, the minor arc part of the proof of display 7.8.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.WeightedFamily261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped NNReal

/-- A support bound for the smoothed sum improves the consecutive square energy. -/
theorem supported_increment261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |ϕ x| ≤ M)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {X N : ℕ} (hN : 2 ≤ N) (hNX : N ≤ X)
    {W : ℝ → ℂ} (hW : Measurable W) {B U : ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hWB : ∀ α, ‖W α‖ ≤ B)
    (hsup : ∀ n ≤ X, ∀ α, W α ≠ 0 → ‖Sphi ϕ n α‖ ≤ U) :
    (∫ α in (0 : ℝ)..1,
      ‖Sphi ϕ N α ^ 2 * W α - Sphi ϕ (N - 1) α ^ 2 * W α‖ ^ 2) ≤
        24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log N / N := by
  have hLp := (smoothed_multiplier_memLp261 hM hbound hW hB hWB N).sub
    (smoothed_multiplier_memLp261 hM hbound hW hB hWB (N - 1))
  have hi : IntervalIntegrable
      (fun α => ‖Sphi ϕ N α ^ 2 * W α - Sphi ϕ (N - 1) α ^ 2 * W α‖ ^ 2)
      volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact hLp.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hc : Continuous (fun α => ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ ^ 2) :=
    ((continuous_Sphi ϕ N).sub (continuous_Sphi ϕ (N - 1))).norm.pow 2
  have hpoint (α : ℝ) :
      ‖Sphi ϕ N α ^ 2 * W α - Sphi ϕ (N - 1) α ^ 2 * W α‖ ≤
        (2 * B * U) * ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ := by
    by_cases hz : W α = 0
    · simp only [hz, mul_zero, sub_self, norm_zero]
      positivity
    · rw [show Sphi ϕ N α ^ 2 * W α - Sphi ϕ (N - 1) α ^ 2 * W α =
        (Sphi ϕ N α - Sphi ϕ (N - 1) α) *
          (Sphi ϕ N α + Sphi ϕ (N - 1) α) * W α by ring,
        norm_mul, norm_mul]
      have hs : ‖Sphi ϕ N α + Sphi ϕ (N - 1) α‖ ≤ 2 * U := by
        exact (norm_add_le _ _).trans (by
          linarith [hsup N hNX α hz, hsup (N - 1) (by omega) α hz])
      calc
        _ ≤ ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ * (2 * U) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
            (hWB α) (norm_nonneg _) (by positivity)
        _ = _ := by ring
  calc
    _ ≤ ∫ α in (0 : ℝ)..1,
        (2 * B * U) ^ 2 * ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi
        ((continuous_const.mul hc).intervalIntegrable 0 1)
      intro α hα
      simpa only [Pi.mul_apply, mul_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (hpoint α) 2
    _ = (2 * B * U) ^ 2 *
        ∫ α in (0 : ℝ)..1, ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (2 * B * U) ^ 2 * (6 * (L : ℝ) ^ 2 * Real.log N / N) :=
      mul_le_mul_of_nonneg_left (Sphi_increment_energy261 hϕ hL hN) (sq_nonneg _)
    _ = _ := by ring

/-- The true smoothing family has a support sensitive second moment with an explicit log loss. -/
theorem supported_family261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {X : ℕ} (hX : 2 ≤ X)
    {W : ℝ → ℂ} (hW : Measurable W) {B U : ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hWB : ∀ α, ‖W α‖ ≤ B)
    (hsup : ∀ n ≤ X, ∀ α, W α ≠ 0 → ‖Sphi ϕ n α‖ ≤ U) :
    ∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))‖ ^ 2 ≤
        24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X * (1 + Real.log X) := by
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hb : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left M 0)
  let F : ℕ → ℝ → ℂ := fun N α => Sphi ϕ N α ^ 2 * W α
  have hS0 : Sphi ϕ 0 = 0 := by funext α; simp [Sphi]
  have hS1 : Sphi ϕ 1 = 0 := by funext α; norm_num [Sphi, Finset.sum_range_succ]
  have hLp (j : ℕ) : MemLp (F j) 2 (volume.restrict (Set.Ioc 0 1)) :=
    smoothed_multiplier_memLp261 (le_max_right M 0) hb hW hB hWB j
  have hzero : F 0 = 0 := by funext α; simp [F, hS0]
  have hint (j : ℕ) : IntervalIntegrable (F j) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (hLp j)
  have hinc (j : ℕ) (_hj : j ∈ Finset.Icc 1 X) :
      MemLp (fun α => F j α - F (j - 1) α) 2 (volume.restrict (Set.Ioc 0 1)) :=
    (hLp j).sub (hLp (j - 1))
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hE (j : ℕ) (hj : j ∈ Finset.Icc 1 X) :
      (∫ α in (0 : ℝ)..1, ‖F j α - F (j - 1) α‖ ^ 2) ≤
        24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log X / j := by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjX : j ≤ X := (Finset.mem_Icc.mp hj).2
    by_cases heq : j = 1
    · subst j
      simp only [F, hS1, hS0, Nat.sub_self, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, sub_self, norm_zero,
        intervalIntegral.integral_zero]
      positivity
    · have hj2 : 2 ≤ j := by omega
      apply (supported_increment261 hϕ (le_max_right M 0) hb hL hj2 hjX hW hB hU hWB hsup).trans
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      apply div_le_div_of_nonneg_right _ hjpos.le
      apply mul_le_mul_of_nonneg_left (Real.log_le_log hjpos (by exact_mod_cast hjX))
      positivity
  have hharm : (∑ j ∈ Finset.Icc 1 X, (1 : ℝ) / j) ≤ 1 + Real.log X := by
    have h := harmonic_le_one_add_log X
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using h
  calc
    _ ≤ (X : ℝ) * ∑ j ∈ Finset.Icc 1 X,
        ∫ α in (0 : ℝ)..1, ‖F j α - F (j - 1) α‖ ^ 2 :=
      family_variation_bessel261 X F hzero hint hinc
    _ ≤ (X : ℝ) * ∑ j ∈ Finset.Icc 1 X,
        24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log X / j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hE) (Nat.cast_nonneg X)
    _ = (24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X) *
        ∑ j ∈ Finset.Icc 1 X, (1 : ℝ) / j := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hharm (by positivity)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.supported_increment261
#print axioms LeanLab.BhowmikGrimmelt2026.supported_family261
