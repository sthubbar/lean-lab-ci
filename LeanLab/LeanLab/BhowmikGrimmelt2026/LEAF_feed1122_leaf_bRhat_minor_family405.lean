/-
Split of `leaf_bRhat_minor_family405` of SPLIT_continuous_weighted_family405 along the
proof of Lemma 7.3, page 26 to 27 of P0029, display 7.8. The paper uses only two facts
about the discrete rational weight on the minor arcs: it is of order one there, Lemma 7.2,
display 7.5 second case, and the smoothed fourth moment over the minor arcs obeys the
Vinogradov and Vaughan minor arc budget with logarithm power five. The first fact is the
proved uniform bound `bRhat_uniform451`, together with continuity `continuous_bRhat`.
The second fact, phrased for any measurable bounded multiplier, is the one open leaf.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp405b
import LeanLab.BhowmikGrimmelt2026.UniformMinorWeight451

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF: Lemma 7.3 proof, page 27, the minor arc part of display 7.8: Parseval followed
by the bound `∫_𝔪 |S_φ|^4 ≪ (X^3/R + X^{13/5}) (log X)^5`, with the multiplier only known to
be bounded, as `1 - b̂_R = O(1)` is all the paper uses there. Here the multiplier is any
measurable function bounded by `B`, and the smoothing family `Sphi ϕ N` varies with `N`
as in the lab's statement. Class HARD: this is the real analytic minor arc fourth moment
with logarithm power five; the lab currently has only power nine, see
`minor_family_log9_uniform451`. -/
theorem leaf_minor_bounded_multiplier_feed1122 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ X →
      ∀ W : ℝ → ℂ, Measurable W → ∀ B : ℝ, 0 ≤ B → (∀ α, ‖W α‖ ≤ B) →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) α‖ ^ 2 ≤
        C * B ^ 2 * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- The exact statement of `leaf_bRhat_minor_family405`, assembled from the bounded
multiplier leaf above and the proved uniform bound `bRhat_uniform451`, Lemma 7.2 page 26. -/
theorem leaf_bRhat_minor_family405_from_leaves {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) α‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hleaf⟩ := leaf_minor_bounded_multiplier_feed1122 hϕ ϑ hϑ hϑ'
  obtain ⟨D, hD, hDb⟩ := bRhat_uniform451 hG
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : (1 : ℝ) ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < (X : ℝ) ^ ϑ := by linarith
  have hscale' : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ X := by
    have := mul_le_mul_of_nonneg_right hη1 hXp.le
    linarith
  have hT : ∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ϑ⌋₊, 0 < η * X * q / (X : ℝ) ^ ϑ := by
    intro q hq
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    positivity
  have hmeas : Measurable (bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ)) :=
    (continuous_bRhat hG.supp hG.even _ _ hT).measurable
  have hbd : ∀ α, ‖bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α‖ ≤ D :=
    fun α => hDb X ((X : ℝ) ^ ϑ) η hR1 hη hscale α
  have h := hleaf X hX hscale' _ hmeas D hD.le hbd
  exact h

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_bRhat_minor_family405_from_leaves
