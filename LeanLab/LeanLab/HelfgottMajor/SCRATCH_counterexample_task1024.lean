import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_high_half_le

/-!
Scratch check for FREE-nv-glm7 task1024: `high_half_weight_pos_part_le` is FALSE.
Counterexample: q = 1, χ = trivial character mod 1, δ = 0, T = 2.
On [1, 2] the log weight log(t / (2π)) is strictly negative, so its positive part is 0,
making the left side 0, while the right side is a positive constant times a strictly
negative integral. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- The Gaussian Mellin transform with δ = 0 composed with the critical line is analytic. -/
private lemma analytic_h : AnalyticOnNhd ℂ (fun z : ℂ => gaussianMellin 0 ((1 / 2 : ℂ) + z * Complex.I)) Set.univ := by
  intro z _
  have hre : ((1 / 2 : ℂ) + z * Complex.I).re = 1 / 2 := by simp
  have h := gaussian_mellin_analyticAt 0 ((1 / 2 : ℂ) + z * Complex.I) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  exact (h.comp z (by
    have : AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w * Complex.I) z := by
      apply AnalyticAt.add (analyticAt_const _ _) (AnalyticAt.mul (analyticAt_id z) analyticAt_const)
    exact this))

/-- The norm of the Gaussian Mellin transform on the critical line is positive at some point of
[1, 2]: otherwise the analytic function would vanish on a segment and hence identically, but at
s = 1 the Mellin transform is the positive Gaussian integral. -/
private lemma exists_pos_norm_gaussianMellin :
    ∃ c ∈ Set.Icc (1 : ℝ) 2, 0 < ‖gaussianMellin 0 ((1 / 2 : ℂ) + (c : ℝ) * Complex.I)‖ := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 → gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) = 0 := by
    intro t ht
    rw [← norm_eq_zero]
    exact le_antisymm (hcon t ht) (norm_nonneg _)
  have hseg : ∃ᶠ z in 𝓝[≠] ((1 / 2 : ℂ) + (3 / 2 : ℝ) * Complex.I),
      (fun w : ℂ => gaussianMellin 0 ((1 / 2 : ℂ) + w * Complex.I)) z = 0 := by
    apply Filter.frequently_iff.mpr
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hU
    -- pick t close to 3/2 with 1 ≤ t ≤ 2
    refine ⟨(1 / 2 : ℂ) + (max 1 (3 / 2 - ε / 2) : ℝ) * Complex.I, ?_, ?_⟩
    · sorry
    · sorry
  sorry

end LeanLab.HelfgottMajor.Decomp431a
