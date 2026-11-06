/-
Split of the large values step, display 3.4 of the Section 3 mean value input, whose single leaf
is `hybrid_large_values` in DecompC165c. The one estimate is cut into the two moment branches it
is built from: the second moment branch, used where the squared energy summand dominates, and the
third moment branch, used where the cubic summand dominates. The two branches are open leaves.
The assembly `hybrid_large_values_split` below is proved from them with no sorry and does not use
the unsplit leaf.

The regime test `G ^ 2 * q * T` against `V ^ 4` is exactly the test of which of the two printed
summands is the larger one: the cubic summand is the squared one times `G ^ 2 * q * T / V ^ 4`.
Both regimes are inhabited, so no branch carries a hypothesis that cannot hold.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165c

namespace LeanLab.BHP1997.DecompC165c
open MeanSquareC165

/-- LEAF. Step 1 of the split, the second moment branch of the large values estimate. The
cardinality is charged to the squared energy summand alone, and only under the regime hypothesis
`G ^ 2 * q * T <= V ^ 4`, where the cubic summand of the full estimate is at most the squared one,
so this is the full estimate restricted to that regime. -/
theorem large_values_second_branch :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T V : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
        Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
        energy a c1 c2 F ^ 2 * ((q : ℝ) * T) ≤ V ^ 4 →
        (S.card : ℝ) ≤ C * Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2) := by
  sorry

/-- LEAF. Step 2 of the split, the third moment branch of the large values estimate. The
cardinality is charged to the cubic energy summand alone, and only under the complementary regime
hypothesis `V ^ 4 <= G ^ 2 * q * T`, where the squared summand is at most the cubic one, so this
is again the full estimate restricted to that regime. -/
theorem large_values_third_branch :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T V : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
        Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
        V ^ 4 ≤ energy a c1 c2 F ^ 2 * ((q : ℝ) * T) →
        (S.card : ℝ) ≤
          C * Real.log x ^ 2 * (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6) := by
  sorry

/-- Step 3 of the split, the elementary bookkeeping: whichever regime of the pair holds, the
branch that applies charges the cardinality to a summand of the printed sum, and the summands are
nonnegative, so the branch bound lifts to the printed sum with the larger of the two constants. -/
theorem hybrid_large_values_split : Lemma1LargeValues := by
  intro B c1 c2 hc1 hc2
  obtain ⟨C1, hC1, h1⟩ := large_values_second_branch B c1 c2 hc1 hc2
  obtain ⟨C2, hC2, h2⟩ := large_values_third_branch B c1 c2 hc1 hc2
  have hM : C1 ≤ max C1 C2 := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max C1 C2 := hC1.le.trans hM
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 hM, ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  have hL : (0 : ℝ) ≤ Real.log x ^ 2 := sq_nonneg _
  have hF0 : (0 : ℝ) < F := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hT0 : (0 : ℝ) < T := by linarith
  have hE : (0 : ℝ) ≤ energy a c1 c2 F := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hS1 : (0 : ℝ) ≤ energy a c1 c2 F * F / V ^ 2 := by positivity
  have hS2 : (0 : ℝ) ≤ energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6 := by positivity
  rcases le_total (energy a c1 c2 F ^ 2 * ((q : ℝ) * T)) (V ^ 4) with hcase | hcase
  · have hb := h1 x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint hcase
    have hstep1 : C1 * Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2) ≤
        max C1 C2 * Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2) := by
      have hh := mul_le_mul_of_nonneg_right hM (mul_nonneg hL hS1)
      calc C1 * Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2)
          = C1 * (Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2)) := by ring
        _ ≤ max C1 C2 * (Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2)) := hh
        _ = max C1 C2 * Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2) := by ring
    have hstep2 : max C1 C2 * Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2) ≤
        max C1 C2 * Real.log x ^ 2 *
          (energy a c1 c2 F * F / V ^ 2 +
            energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6) := by
      have hle : energy a c1 c2 F * F / V ^ 2 ≤
          energy a c1 c2 F * F / V ^ 2 +
            energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6 := le_add_of_nonneg_right hS2
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hL) hM0
      calc max C1 C2 * Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2)
          = max C1 C2 * (Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2)) := by ring
        _ ≤ max C1 C2 * (Real.log x ^ 2 *
              (energy a c1 c2 F * F / V ^ 2 +
                energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6)) := hh
        _ = _ := by ring
    exact hb.trans (hstep1.trans hstep2)
  · have hb := h2 x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint hcase
    have hstep1 : C2 * Real.log x ^ 2 * (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6) ≤
        max C1 C2 * Real.log x ^ 2 * (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6) := by
      have hh := mul_le_mul_of_nonneg_right (le_max_right C1 C2) (mul_nonneg hL hS2)
      calc C2 * Real.log x ^ 2 * (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6)
          = C2 * (Real.log x ^ 2 * (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6)) := by
            ring
        _ ≤ max C1 C2 * (Real.log x ^ 2 *
              (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6)) := hh
        _ = max C1 C2 * Real.log x ^ 2 *
              (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6) := by ring
    have hstep2 : max C1 C2 * Real.log x ^ 2 *
          (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6) ≤
        max C1 C2 * Real.log x ^ 2 *
          (energy a c1 c2 F * F / V ^ 2 +
            energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6) := by
      have hle : energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6 ≤
          energy a c1 c2 F * F / V ^ 2 +
            energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6 := le_add_of_nonneg_left hS1
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hL) hM0
      calc max C1 C2 * Real.log x ^ 2 *
            (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6)
          = max C1 C2 * (Real.log x ^ 2 *
              (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6)) := by ring
        _ ≤ max C1 C2 * (Real.log x ^ 2 *
              (energy a c1 c2 F * F / V ^ 2 +
                energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6)) := hh
        _ = _ := by ring
    exact hb.trans (hstep1.trans hstep2)

end LeanLab.BHP1997.DecompC165c
