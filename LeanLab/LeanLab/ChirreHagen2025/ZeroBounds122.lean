import LeanLab.ChirreHagen2025.Statements

/-!
P0075 Lemma 2.2, pages 3 and 4.
The sums count the analytic multiplicity of each zero.
These are CITED propositions, with no theorem asserting them.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.ZeroBounds122

/-- P0075 equations 2.2 and 2.3: the zero kernel, with analytic multiplicity. -/
noncomputable def zeroKernel (a t : ℝ)
    (ρ : {s : ℂ // riemannZeta s = 0 ∧ s.re = 1 / 2}) : ℝ :=
  (analyticOrderNatAt riemannZeta ρ : ℝ) / (a + (t - (ρ : ℂ).im) ^ 2)

/-- CITED. P0075 Lemma 2.2 part 1, page 3, equation 2.2. -/
def lemma2_2_part1 : Prop := RiemannHypothesis → ∀ t : ℝ, 4 ≤ |t| →
  Summable (zeroKernel 6 t) ∧
    (∑' ρ, zeroKernel 6 t ρ) ≤ Real.log |t| / (2 * Real.sqrt 6)

/-- CITED. P0075 Lemma 2.2 part 2, page 3, equation 2.3. -/
def lemma2_2_part2 : Prop := RiemannHypothesis → ∀ t : ℝ, 100 ≤ |t| →
  Summable (zeroKernel (1 / 4) t) ∧
    (∑' ρ, zeroKernel (1 / 4) t ρ) ≤ 9 * Real.log |t|

end LeanLab.ChirreHagen2025.ZeroBounds122
