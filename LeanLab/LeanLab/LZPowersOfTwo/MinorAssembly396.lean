/-
P0079 pages 11 to 12, minor-arc assembly through the paired moment input.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp396d

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 pages 11 to 12, displays 41 to 43. CONDITIONAL ON
paired_second_moment396 and minor_bad353. This is the exact minor_upper353
statement. The exceptional set and its complement divide the tolerance. -/
theorem minor_upper396 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in minor293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (ν ^ (s - 2) * Cq r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [minor_good396 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (δ / 2) (by positivity),
    minor_bad353 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (δ / 2) (by positivity)] with X hg hb
  have hbad : MeasurableSet (badPower353 s ν μ ε X) := by
    unfold badPower353
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    apply Continuous.measurable
    unfold powerSum293 character293
    fun_prop
  have hsplit := integral_inter_add_sdiff (s := minor293 X (cutoff293 s μ ε X)) hbad
    (integrand_integrable293 s l1 l2 μ γ η ε X).integrableOn
  rw [← hsplit]
  calc
    _ ≤ ‖∫ α in minor293 X (cutoff293 s μ ε X) ∩ badPower353 s ν μ ε X,
        integrand293 s l1 l2 μ γ η ε X α‖ +
      ‖∫ α in minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X,
        integrand293 s l1 l2 μ γ η ε X α‖ := norm_add_le _ _
    _ ≤ _ := by linarith


end LeanLab.LZPowersOfTwo
