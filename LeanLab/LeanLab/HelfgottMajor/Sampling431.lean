import LeanLab.HelfgottMajor.Decomp389b

/-!
Source checks and scalar prerequisites for the signed sampling leaves.
Source book Part IV pages 431 to 434, Lemma 16.9 and display 16.26.
These checks do not refute the sealed Gaussian sampling inequality.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Sampling431
open Real MeasureTheory Set Filter
open scoped Topology

/-- A hard cutoff with a nonzero retained endpoint is not continuous at that endpoint.
This audits the continuity hypothesis of Lemma 16.9 in its page 433 application.
It is a general cutoff check, not a counterexample to the Gaussian zero bound.
-/
theorem cutoff_not_continuous (f : ℝ → ℝ) (T : ℝ) (hf : f T ≠ 0) :
    ¬ContinuousAt (fun t : ℝ => if t ≤ T then f t else 0) T := by
  intro hc
  have hleft := hc.tendsto.mono_left (show 𝓝[>] T ≤ 𝓝 T from nhdsWithin_le_nhds)
  have hright : Tendsto (fun t : ℝ => if t ≤ T then f t else 0) (𝓝[>] T) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_Ioi] at ht
    simp [not_le.mpr ht]
  have heq := tendsto_nhds_unique hleft hright
  simp only [le_refl, ite_true] at heq
  exact hf heq

/-- The square of the printed zero count error envelope is not integrable to infinity.
This audits the infinite upper limit printed in book display 16.26.
The later page 434 estimate instead integrates only up to T0.
-/
theorem error_envelope_square_not_integrable :
    ¬IntegrableOn (fun t : ℝ => (0.15 * log t + 3.389) ^ 2) (Ioi 1) := by
  intro hi
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 1) := by
    apply hi.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hl : 0 ≤ log t := log_nonneg (le_of_lt ht)
    norm_num only [norm_one]
    nlinarith [sq_nonneg (0.15 * log t + 3.389)]
  have hh : ‖(1 : ℝ)‖ₑ = 0 ∨ volume (Ioi (1 : ℝ)) < ⊤ :=
    (integrableOn_const_iff (C := (1 : ℝ))).mp hconst
  simpa using hh

end LeanLab.HelfgottMajor.Sampling431
