/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Tail113

namespace LeanLab.Tchudakov1938.Decomp362a
open Filter
open LeanLab.Tchudakov1938.Tail113 LeanLab.Tchudakov1938.Positive113
open LeanLab.Tchudakov1938.Euler113 LeanLab.Tchudakov1938.Decomp113

/-- LEAF. P0064, page 29, inequality 8. The logarithmic error scale tends to zero. -/
theorem loglog_scale_tendsto :
    Tendsto (fun x : ℝ => (Real.log (Real.log x))^2 / Real.log x) atTop (nhds 0) := by
  simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
    Real.tendsto_log_atTop

/-- LEAF. P0064, page 29, inequality 8. Any two fixed multiples of the error scale have sum tending to zero. -/
theorem combined_tendsto (c_9 c_12 : ℝ) :
    Tendsto (fun x : ℝ => c_9 * (Real.log (Real.log x))^2 / Real.log x +
      c_12 * (Real.log (Real.log x))^2 / Real.log x) atTop (nhds 0) := by
  simpa only [mul_div_assoc, mul_zero, add_zero] using
    (loglog_scale_tendsto.const_mul c_9).add (loglog_scale_tendsto.const_mul c_12)

/-- P0064, page 29, inequality 8. Exact statement of DecompJ290.tail_bound_combined. -/
theorem tail_bound_combined (M : ℝ) (hM : 0 < M) (c_9 c_12 : ℝ) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ m : ℕ, 0 < m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      c_9 * (Real.log (Real.log x))^2 / Real.log x + c_12 * (Real.log (Real.log x))^2 / Real.log x ≤ (1 / 4 : ℝ) := by
  have h := (combined_tendsto c_9 c_12).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨X, hX⟩ := eventually_atTop.mp h
  exact ⟨max 3 X, le_max_left _ _, fun x hx _ _ _ _ =>
    (hX x ((le_max_right _ _).trans hx)).le⟩

/-- P0064, page 29, inequalities 3 and 4. The zero-cutoff tail for m equal to two is nonzero. -/
theorem zero_cutoff_tail_lower : (1 / 2 : ℝ) ≤ ‖tailSeries 2 0‖ := by
  have h := partial_add_tail 2 (by norm_num) 0
  have hp : partialSeries 2 0 = 0 := by
    simp [partialSeries, coefficientNat]
  rw [hp, zero_add] at h
  rw [h]
  exact (singular_series_lower 2 (by norm_num) (by decide)).trans (Complex.re_le_norm _)

/-- P0064, page 29, inequality 8 audit. The unrestricted sealed tail_bound_terms proposition is false.
This audits the formalization. The paper restricts x and the cutoff. -/
theorem unrestricted_tail_bound_terms_false :
    ¬ (∃ c_9 c_12 : ℝ, 0 < c_9 ∧ 0 < c_12 ∧ ∀ x : ℝ, ∀ m xi : ℕ,
    ‖tailSeries m xi‖ ≤ c_9 * (Real.log (Real.log x))^2 / Real.log x + c_12 * (Real.log (Real.log x))^2 / Real.log x) := by
  rintro ⟨c_9, c_12, _, _, h⟩
  have hz := h 1 2 0
  norm_num at hz
  have hl := zero_cutoff_tail_lower
  rw [hz, norm_zero] at hl
  norm_num at hl

/-- P0064, page 29, inequality 8 audit. Even arbitrarily large x cannot repair the
unrestricted bound while the cutoff remains zero. The cutoff relation is essential. -/
theorem fixed_cutoff_counterexample (c_9 c_12 X : ℝ) :
    ∃ x : ℝ, 3 ≤ x ∧ X ≤ x ∧
      c_9 * (Real.log (Real.log x))^2 / Real.log x +
      c_12 * (Real.log (Real.log x))^2 / Real.log x < ‖tailSeries 2 0‖ := by
  have h := (combined_tendsto c_9 c_12).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Y, hY⟩ := eventually_atTop.mp h
  refine ⟨max 3 (max X Y), le_max_left _ _, ?_, ?_⟩
  · exact (le_max_left X Y).trans (le_max_right _ _)
  · exact (hY _ ((le_max_right X Y).trans (le_max_right _ _))).trans_le
      zero_cutoff_tail_lower

end LeanLab.Tchudakov1938.Decomp362a
