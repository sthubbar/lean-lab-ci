/-
P0079 pages 11 to 12, the two minor arc contributions.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 6, and Parsell page 370, Lemma 5.
The exceptional set is the union over all power coefficients. -/
def badPower353 (s : ℕ) (ν : ℝ) (μ : ℕ → ℝ) (ε X : ℝ) : Set ℝ :=
  {α | ∃ i : Fin s, ν * cutoff293 s μ ε X <
    ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖}

/-- LEAF. P0079 page 11 display 41 and page 11 display 42.
On the complement of the exceptional set, Cauchy Schwarz and Lemma 4 give
the displayed minor coefficient with an arbitrary positive tolerance.
This leaf makes no estimate on the exceptional part. -/
theorem minor_good353 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in (minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (ν ^ (s - 2) * Cq r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  sorry

/-- LEAF. P0079 pages 11 to 12, displays 38 to 40 and 43.
The integral over the exceptional set is little o of eta X L to the s.
The proof uses the exceptional measure estimate and the prime fourth moment.
This leaf makes no estimate on the ordinary part of the minor arc. -/
theorem minor_bad353 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in (minor293 X (cutoff293 s μ ε X) ∩ badPower353 s ν μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        δ * η * X * (cutoff293 s μ ε X) ^ s := by
  sorry

/-- P0079 pages 11 to 12, the conclusions after displays 41 and 43.
CONDITIONAL ON minor_good353 and minor_bad353. This is the exact minor target. -/
theorem minor_upper353 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
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
  filter_upwards [minor_good353 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
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
