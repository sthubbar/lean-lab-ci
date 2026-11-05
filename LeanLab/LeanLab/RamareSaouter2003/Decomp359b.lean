import LeanLab.RamareSaouter2003.Decomp290c

/-!
P0099 p. 14, Lemma 2 and its written proof.
Only the finite positive square-tail estimate is OPEN.
The assembly uses the proved functional equation symmetry and Mathlib summability.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp359b

open L3Zeta L3Zeros

/-- LEAF. P0099 p. 14, Lemma 2 proof at m = 1 and T = 1000.
The positive-ordinate half has the finite partial-sum upper bound obtained
by integrating N and applying Lemma 1. This leaf asserts no convergence
and treats only positive ordinates and the square denominator. -/
theorem positive_square_partial_bound (s : Finset ZI) :
    (∑ i ∈ s, if (1000 : ℝ) < gZ i then 1 / (gZ i) ^ 2 else 0) ≤
      L2 1 1000 / (2 * 1000) := by
  sorry

/-- P0099 p. 14, first equality in the Lemma 2 proof.
The negative partial sum is bounded by the positive one after the
multiplicity-preserving functional equation map. CONDITIONAL ON
positive_square_partial_bound. -/
theorem negative_square_partial_bound (s : Finset ZI) :
    (∑ i ∈ s, if (1000 : ℝ) < -gZ i then 1 / (-gZ i) ^ 2 else 0) ≤
      L2 1 1000 / (2 * 1000) := by
  classical
  have h := positive_square_partial_bound (s.image σZ)
  rw [Finset.sum_image (fun _ _ _ _ hh => σZ_injective hh)] at h
  simpa only [L1Zeta.gZ_σ_neg] using h

/-- P0099 p. 14, Lemma 2 with m at least one and T = 1000.
Higher reciprocal powers are dominated by the square tail on both signs.
CONDITIONAL ON positive_square_partial_bound. -/
theorem reciprocal_tail_summable (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun i : ZI => if (1000 : ℝ) < |gZ i| then
      1 / |gZ i| ^ (m + 1) else 0) := by
  classical
  apply summable_of_sum_le (c := L2 1 1000 / 1000)
  · intro i
    change 0 ≤ if (1000 : ℝ) < |gZ i| then 1 / |gZ i| ^ (m + 1) else 0
    split_ifs <;> positivity
  · intro s
    have hp := positive_square_partial_bound s
    have hn := negative_square_partial_bound s
    have hb : (∑ i ∈ s, if (1000 : ℝ) < |gZ i| then
        1 / |gZ i| ^ (m + 1) else 0) ≤
        (∑ i ∈ s, if (1000 : ℝ) < gZ i then 1 / (gZ i) ^ 2 else 0) +
        ∑ i ∈ s, if (1000 : ℝ) < -gZ i then 1 / (-gZ i) ^ 2 else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      by_cases h : (1000 : ℝ) < |gZ i|
      · have hpow : |gZ i| ^ 2 ≤ |gZ i| ^ (m + 1) :=
          pow_le_pow_right₀ (by linarith : 1 ≤ |gZ i|) (by omega)
        have hle := one_div_le_one_div_of_le (by positivity : 0 < |gZ i| ^ 2) hpow
        rcases le_or_gt 0 (gZ i) with hg | hg
        · rw [abs_of_nonneg hg] at h hle
          simpa [abs_of_nonneg hg, h, show ¬(1000 : ℝ) < -gZ i by linarith] using hle
        · rw [abs_of_neg hg] at h hle
          simpa [abs_of_neg hg, h, show ¬(1000 : ℝ) < gZ i by linarith] using hle
      · simp only [if_neg h]
        positivity
    linarith

end LeanLab.RamareSaouter2003.Decomp359b

#print axioms LeanLab.RamareSaouter2003.Decomp359b.positive_square_partial_bound
#print axioms LeanLab.RamareSaouter2003.Decomp359b.negative_square_partial_bound
#print axioms LeanLab.RamareSaouter2003.Decomp359b.reciprocal_tail_summable
