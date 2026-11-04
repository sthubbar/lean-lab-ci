/-
P0059 arXiv 1407.7902v1 page 5 Section 2.5.
Elementary finiteness and convergence for the actual zero-count definitions.
AI wrote this Lean code. CODEX task259. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroInputs259
import Mathlib.NumberTheory.LSeries.ZetaZeros

namespace LeanLab.KadiriLumley2014.Task259

open Real Set

/-- Every bounded positive-height portion of the open critical strip has finitely many zeros. -/
theorem finite_strip_zeros_height (T : ℝ) :
    {z : ℂ | riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im ≤ T}.Finite := by
  have hf := (isCompact_closedBall (0 : ℂ) (|T| + 2)).inter_riemannZetaZeros_finite
  apply hf.subset
  intro z hz
  refine ⟨?_, hz.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hn := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hz.2.1, abs_of_pos hz.2.2.2.1] at hn
  linarith [hz.2.2.1, hz.2.2.2.2, le_abs_self T]

/-- Every real zero family vanishing above a fixed positive-height cutoff is summable. -/
theorem summable_bounded_positive_zero_family (T : ℝ) (f : ℂ → ℝ)
    (hcut : ∀ ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}, T < (ρ : ℂ).im → f ρ = 0) :
    Summable (fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} =>
      if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * f ρ else 0) := by
  classical
  have hpre := Set.Finite.preimage
    (f := (Subtype.val : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} → ℂ))
    Subtype.val_injective.injOn (finite_strip_zeros_height T)
  apply summable_of_ne_finset_zero (s := hpre.toFinset)
  intro ρ hρ
  by_cases hp : 0 < (ρ : ℂ).im
  · rw [ite_eq_left hp]
    have ht : T < (ρ : ℂ).im := by
      by_contra h
      apply hρ
      apply (Set.Finite.mem_toFinset hpre).mpr
      exact ⟨ρ.property.1, ρ.property.2.1, ρ.property.2.2, hp, le_of_not_gt h⟩
    rw [hcut ρ ht, mul_zero]
  · simp [hp]

/-- The family defining N of T is summable at every real cutoff. -/
theorem zeroCount_summable (T : ℝ) :
    Summable (fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} =>
      if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (if (ρ : ℂ).im < T then 1 else 0) else 0) := by
  refine summable_bounded_positive_zero_family T (fun ρ : ℂ => if ρ.im < T then 1 else 0) ?_
  intro ρ hρ
  exact if_neg (not_lt_of_ge hρ.le)

/-- The actual positive-ordinate zero count is nonnegative. -/
theorem zeroCount_nonneg (T : ℝ) : 0 ≤ zeroCount T := by
  unfold zeroCount positiveZeroSum
  apply tsum_nonneg
  intro ρ
  split_ifs <;> positivity

/-- The actual zero count is monotone in the cutoff, with convergence supplied by finiteness. -/
theorem zeroCount_mono : Monotone zeroCount := by
  intro T U hTU
  unfold zeroCount positiveZeroSum
  apply Summable.tsum_le_tsum _ (zeroCount_summable T) (zeroCount_summable U)
  intro ρ
  by_cases hp : 0 < (ρ : ℂ).im
  · simp only [ite_eq_left hp]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    split_ifs with hT hU
    · rfl
    · exact absurd (hT.trans_le hTU) hU
    · norm_num
    · rfl
  · simp [hp]

end LeanLab.KadiriLumley2014.Task259
