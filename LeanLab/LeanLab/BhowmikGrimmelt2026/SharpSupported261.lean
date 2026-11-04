/-
Weighted variation for the actual supported family in display 7.8, page 27.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SupportedFamily261
import LeanLab.BhowmikGrimmelt2026.WeightedVariation261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped NNReal

/-- The true smoothing family has a support sensitive second moment without an extra harmonic logarithm. -/
theorem supported_family_sharp261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {X : ℕ} (hX : 2 ≤ X)
    {W : ℝ → ℂ} (hW : Measurable W) {B U : ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hWB : ∀ α, ‖W α‖ ≤ B)
    (hsup : ∀ n ≤ X, ∀ α, W α ≠ 0 → ‖Sphi ϕ n α‖ ≤ U) :
    ∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))‖ ^ 2 ≤
        96 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X := by
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
  have h := family_inverse_energy261 X F hzero hint hinc
    (by positivity : 0 ≤ 24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log X) hE
  convert h using 1 <;> ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.supported_family_sharp261
