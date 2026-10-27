/-
P0022, pages 368 to 370. Equation 20 discharged in the existing Parseval reduction.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Kaniecki1995.Series20
import LeanLab.Kaniecki1995.U7152Parseval
import LeanLab.Kaniecki1995.Lemma5U1416

namespace LeanLab.Kaniecki1995.Parseval20
open Real MeasureTheory Set

/-- Page 369. CONDITIONAL ON the displayed Parseval inequality with the printed g.
Equation 20 is proved, so the existing Parseval18BC input follows. -/
theorem parseval18BC_of_g
    (hP : RiemannHypothesis → ∀ T σ : ℝ, 7.02 < T → 1 / 2 < σ → σ ≤ 3 / 4 →
      (∫⁻ τ in Ioi (0 : ℝ), ENNReal.ofReal (U7152.tauIntegrand T σ τ)) ≤
        ENNReal.ofReal (1 / (2 * π)) *
          ∫⁻ t, ENNReal.ofReal (kern T σ t *
            ‖logDerivZeta (L5.sAt σ t) + Series20.gSeries (L5.sAt σ t)‖ ^ 2)) :
    U7152.Parseval18BC := by
  intro hRH T σ hT hσ hσ'
  simpa only [Series20.eq20 hσ, ← add_assoc] using hP hRH T σ hT hσ hσ'

/-- Page 369. CONDITIONAL ON the displayed Parseval inequality with g.
The exponential substitution, conjugation fold and equation 20 are all proved. -/
theorem parseval1920_of_g
    (hP : RiemannHypothesis → ∀ T σ : ℝ, 7.02 < T → 1 / 2 < σ → σ ≤ 3 / 4 →
      (∫⁻ τ in Ioi (0 : ℝ), ENNReal.ofReal (U7152.tauIntegrand T σ τ)) ≤
        ENNReal.ofReal (1 / (2 * π)) *
          ∫⁻ t, ENNReal.ofReal (kern T σ t *
            ‖logDerivZeta (L5.sAt σ t) + Series20.gSeries (L5.sAt σ t)‖ ^ 2)) :
    L5.Parseval1920 := U7152.parseval1920_of_18BC (parseval18BC_of_g hP)

/-- Pages 368 to 370. Guarded Lemma 5, CONDITIONAL ON guarded Lemma 4
and the displayed Parseval inequality with g. Equation 20 is no longer cited. -/
theorem lemma5_guarded_of_g (h4 : L5.Lemma4G)
    (hP : RiemannHypothesis → ∀ T σ : ℝ, 7.02 < T → 1 / 2 < σ → σ ≤ 3 / 4 →
      (∫⁻ τ in Ioi (0 : ℝ), ENNReal.ofReal (U7152.tauIntegrand T σ τ)) ≤
        ENNReal.ofReal (1 / (2 * π)) *
          ∫⁻ t, ENNReal.ofReal (kern T σ t *
            ‖logDerivZeta (L5.sAt σ t) + Series20.gSeries (L5.sAt σ t)‖ ^ 2)) :
    L5.Lemma5G := L5U1416.lemma5G_of_U1416 h4 (parseval1920_of_g hP)

end LeanLab.Kaniecki1995.Parseval20

#print axioms LeanLab.Kaniecki1995.Parseval20.parseval18BC_of_g
#print axioms LeanLab.Kaniecki1995.Parseval20.parseval1920_of_g
#print axioms LeanLab.Kaniecki1995.Parseval20.lemma5_guarded_of_g
