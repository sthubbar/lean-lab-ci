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
import LeanLab.BhowmikGrimmelt2026.MinorUniform451
import LeanLab.BhowmikGrimmelt2026.SPLIT_minor_bare_family328

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- Formerly a LEAF, now sorry free burst-20261124 S9-20, CONDITIONAL ON
`split_leaf_sphi_minor_log2` of SPLIT_minor_bare_family328, hence on its open input, the minor
arc partial sum bound at logarithm power two. Lemma 7.3 proof, page 27, the minor arc part of display 7.8: Parseval followed
by the bound `∫_𝔪 |S_φ|^4 ≪ (X^3/R + X^{13/5}) (log X)^5`, with the multiplier only known to
be bounded, as `1 - b̂_R = O(1)` is all the paper uses there. Here the multiplier is any
measurable function bounded by `B`, and the smoothing family `Sphi ϕ N` varies with `N`
as in the lab's statement. Class HARD: this is the real analytic minor arc fourth moment
with logarithm power five; the lab currently has only power nine, see
`minor_family_log9_uniform451`. Proof: restrict the multiplier to the minor arcs, take
the supremum of the smoothed sum there from `split_leaf_sphi_minor_log2`, and apply the proved
family bound `supported_family_sharp261`; the power part is `minor_budget_identity451`. -/
theorem leaf_minor_bounded_multiplier_feed1122 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ X →
      ∀ W : ℝ → ℂ, Measurable W → ∀ B : ℝ, 0 ≤ B → (∀ α, ‖W α‖ ≤ B) →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) α‖ ^ 2 ≤
        C * B ^ 2 * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  obtain ⟨C₁, hC₁, h₁⟩ := split_leaf_sphi_minor_log2 hϕ
  refine ⟨192 * C₁ ^ 2 * (L : ℝ) ^ 2, by positivity, ?_⟩
  intro X hX _hscale W hW B hB hWB
  set R : ℝ := (X : ℝ) ^ ϑ with hRdef
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < R := by linarith
  have hRX : R ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = _ := Real.rpow_one _
  let W' : ℝ → ℂ := fun α => if MajorArc X R α then 0 else W α
  have hW' : Measurable W' := measurable_const.ite (measurableSet_majorArc84 X R) hW
  have hWB' (α : ℝ) : ‖W' α‖ ≤ B := by
    by_cases hm : MajorArc X R α
    · simp only [W', if_pos hm, norm_zero]; exact hB
    · simpa [W', hm] using hWB α
  set A : ℝ := (X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ) with hAdef
  set U : ℝ := C₁ * A * Real.log X ^ 2 with hUdef
  have hU : 0 ≤ U := by positivity
  have hsup (n : ℕ) (hn : n ≤ X) (α : ℝ) (hne : W' α ≠ 0) : ‖Sphi ϕ n α‖ ≤ U := by
    have hm : ¬ MajorArc X R α := by
      intro hh
      exact hne (by simp [W', hh])
    exact h₁ X hX R hR1 hRX n hn α hm
  have hfam := supported_family_sharp261 hϕ hL hX hW' hB hU hWB' hsup
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X R α}.indicator
          (fun α => Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) α) =
        ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W' α * ee (-(N * α)) := by
    apply intervalIntegral.integral_congr
    intro α _
    by_cases hm : MajorArc X R α <;> simp [W', Set.indicator, hm]
  simp_rw [heq]
  have hA2 : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hRp.le]
  have hD2 : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
    norm_num
  have hsq : A ^ 2 ≤ 2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← hA2, ← hD2, hAdef]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  have hlogX : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  calc
    _ ≤ 96 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X := hfam
    _ = 96 * C₁ ^ 2 * (L : ℝ) ^ 2 * B ^ 2 * A ^ 2 * X * Real.log X ^ 5 := by
      rw [hUdef]; ring
    _ ≤ 96 * C₁ ^ 2 * (L : ℝ) ^ 2 * B ^ 2 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 5 := by
      gcongr
    _ = 192 * C₁ ^ 2 * (L : ℝ) ^ 2 * B ^ 2 *
        (((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) * X) * Real.log X ^ 5 := by ring
    _ = _ := by rw [minor_budget_identity451 hXp R]; ring

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

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_minor_bounded_multiplier_feed1122
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_bRhat_minor_family405_from_leaves
