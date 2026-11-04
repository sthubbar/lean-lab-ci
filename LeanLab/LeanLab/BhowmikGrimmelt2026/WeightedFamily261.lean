/-
A uniform second moment for the actual smoothing family.
Source: P0029 pages 26 and 27, the smoothing issue in the proof of display 7.8.
The multiplier is fixed across N. The smoothed prime sum is allowed to vary with N.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Family261
import LeanLab.BhowmikGrimmelt2026.Smoothing261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped NNReal

/-- A bounded measurable multiplier times a smoothed square lies in L2. -/
theorem smoothed_multiplier_memLp261 {ϕ : ℝ → ℝ} {M B : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, |ϕ x| ≤ M)
    {W : ℝ → ℂ} (hW : Measurable W) (hB : 0 ≤ B) (hWB : ∀ α, ‖W α‖ ≤ B)
    (N : ℕ) :
    MemLp (fun α => Sphi ϕ N α ^ 2 * W α) 2 (volume.restrict (Set.Ioc 0 1)) := by
  apply MemLp.of_bound (((continuous_Sphi ϕ N).pow 2).measurable.mul hW).aestronglyMeasurable
    ((6 * M * N) ^ 2 * B)
  apply Filter.Eventually.of_forall
  intro α
  change ‖Sphi ϕ N α ^ 2 * W α‖ ≤ _
  rw [norm_mul, norm_pow]
  exact mul_le_mul
    (pow_le_pow_left₀ (norm_nonneg _) (Sphi_uniform261 hM hbound N α) 2)
    (hWB α) (norm_nonneg _) (sq_nonneg _)

/-- Consecutive smoothed squares have energy of order N log N with a bounded multiplier. -/
theorem smoothed_square_increment261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |ϕ x| ≤ M)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ)
    {W : ℝ → ℂ} (hW : Measurable W) {B : ℝ} (hB : 0 ≤ B)
    (hWB : ∀ α, ‖W α‖ ≤ B) {N : ℕ} (hN : 2 ≤ N) :
    (∫ α in (0 : ℝ)..1,
      ‖Sphi ϕ N α ^ 2 * W α - Sphi ϕ (N - 1) α ^ 2 * W α‖ ^ 2) ≤
      864 * B ^ 2 * M ^ 2 * (L : ℝ) ^ 2 * N * Real.log N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hprev : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N - 1 ≤ N)
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
        (12 * B * M * N) * ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ := by
    rw [show Sphi ϕ N α ^ 2 * W α - Sphi ϕ (N - 1) α ^ 2 * W α =
      (Sphi ϕ N α - Sphi ϕ (N - 1) α) *
        (Sphi ϕ N α + Sphi ϕ (N - 1) α) * W α by ring,
      norm_mul, norm_mul]
    have hs : ‖Sphi ϕ N α + Sphi ϕ (N - 1) α‖ ≤ 12 * M * N := by
      calc
        _ ≤ ‖Sphi ϕ N α‖ + ‖Sphi ϕ (N - 1) α‖ := norm_add_le _ _
        _ ≤ 6 * M * N + 6 * M * (N - 1 : ℕ) :=
          add_le_add (Sphi_uniform261 hM hbound N α) (Sphi_uniform261 hM hbound (N - 1) α)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hprev (by positivity : 0 ≤ 6 * M)]
    calc
      _ ≤ ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ * (12 * M * N) * B := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
          (hWB α) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ α in (0 : ℝ)..1,
        (12 * B * M * N) ^ 2 * ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi
        ((continuous_const.mul hc).intervalIntegrable 0 1)
      intro α hα
      simpa only [Pi.mul_apply, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hpoint α) 2
    _ = (12 * B * M * N) ^ 2 *
        ∫ α in (0 : ℝ)..1, ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (12 * B * M * N) ^ 2 * (6 * (L : ℝ) ^ 2 * Real.log N / N) :=
      mul_le_mul_of_nonneg_left (Sphi_increment_energy261 hϕ hL hN) (sq_nonneg _)
    _ = _ := by field_simp <;> ring

/-- Uniform second moment for the actual varying smoothing and any fixed bounded multiplier. -/
theorem smoothed_family_explicit261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |ϕ x| ≤ M)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {X : ℕ} (hX : 2 ≤ X)
    {W : ℝ → ℂ} (hW : Measurable W) {B : ℝ} (hB : 0 ≤ B)
    (hWB : ∀ α, ‖W α‖ ≤ B) :
    ∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))‖ ^ 2 ≤
      864 * M ^ 2 * (L : ℝ) ^ 2 * B ^ 2 * (X : ℝ) ^ 3 * Real.log X := by
  let F : ℕ → ℝ → ℂ := fun N α => Sphi ϕ N α ^ 2 * W α
  have hS0 : Sphi ϕ 0 = 0 := by funext α; simp [Sphi]
  have hS1 : Sphi ϕ 1 = 0 := by funext α; norm_num [Sphi, Finset.sum_range_succ]
  have hLp (j : ℕ) : MemLp (F j) 2 (volume.restrict (Set.Ioc 0 1)) :=
    smoothed_multiplier_memLp261 hM hbound hW hB hWB j
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
        864 * B ^ 2 * M ^ 2 * (L : ℝ) ^ 2 * X * Real.log X := by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjX : j ≤ X := (Finset.mem_Icc.mp hj).2
    by_cases heq : j = 1
    · subst j
      simp only [F, hS1, hS0, Nat.sub_self, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, sub_self, norm_zero,
        intervalIntegral.integral_zero]
      positivity
    · have hj2 : 2 ≤ j := by omega
      apply (smoothed_square_increment261 hϕ hM hbound hL hW hB hWB hj2).trans
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      have hjX' : (j : ℝ) ≤ X := by exact_mod_cast hjX
      have hlog : Real.log (j : ℝ) ≤ Real.log X := Real.log_le_log hjpos hjX'
      have hjlog : 0 ≤ Real.log (j : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hj1)
      nlinarith [mul_le_mul hjX' hlog hjlog (Nat.cast_nonneg X),
        mul_le_mul_of_nonneg_left (mul_le_mul hjX' hlog hjlog (Nat.cast_nonneg X))
          (by positivity : 0 ≤ 864 * B ^ 2 * M ^ 2 * (L : ℝ) ^ 2)]
  calc
    _ ≤ (X : ℝ) * ∑ j ∈ Finset.Icc 1 X,
        ∫ α in (0 : ℝ)..1, ‖F j α - F (j - 1) α‖ ^ 2 :=
      family_variation_bessel261 X F hzero hint hinc
    _ ≤ (X : ℝ) * ∑ _j ∈ Finset.Icc 1 X,
        864 * B ^ 2 * M ^ 2 * (L : ℝ) ^ 2 * X * Real.log X :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hE) (Nat.cast_nonneg X)
    _ = _ := by simp; ring

/-- The cutoff alone determines the constant in the uniform multiplier family bound. -/
theorem smoothed_family_bound261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ W : ℝ → ℂ, Measurable W →
      ∀ B : ℝ, 0 ≤ B → (∀ α, ‖W α‖ ≤ B) →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))‖ ^ 2 ≤
          C * B ^ 2 * (X : ℝ) ^ 3 * Real.log X := by
  obtain ⟨M, hbound⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  refine ⟨864 * (max M 0) ^ 2 * (L : ℝ) ^ 2, by positivity, ?_⟩
  intro X hX W hW B hB hWB
  have hb : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hbound x).trans (le_max_left M 0)
  exact smoothed_family_explicit261 hϕ (le_max_right M 0) hb hL hX hW hB hWB

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.smoothed_multiplier_memLp261
#print axioms LeanLab.BhowmikGrimmelt2026.smoothed_square_increment261

#print axioms LeanLab.BhowmikGrimmelt2026.smoothed_family_explicit261
#print axioms LeanLab.BhowmikGrimmelt2026.smoothed_family_bound261
