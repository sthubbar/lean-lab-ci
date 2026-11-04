/-
AI wrote the Lean code. Goldbach is open.
The strong PNT is reused from the lab port of PrimeNumberTheoremAnd,
Apache 2.0, commit c39a751132c88b6e8080b74c74023fd95b3d8be0.
This file supplies the scalar input of the page 7 Akeno reduction.
-/
import LeanLab.Akeno2026.DecompJ267
import LeanLab.PNTPort.StrongPNT.Bridge

namespace LeanLab.Akeno2026.PNTInstance221
open Finset Real
open scoped ArithmeticFunction.vonMangoldt
open DecompJ267

/-- Page 7 PNT input with a constant uniform over all truncated partial sums. -/
theorem scalar_pnt221 :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ m : ℕ, m ≤ ⌊X⌋₊ + 1 →
        |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ C * X / Real.log X ^ A := by
  exact uniform_partial_of_pointwise221
    (pointwise_pnt_of_strong221 LeanLab.PNTPort.psi_explicit_strong)

/-- Page 7 full reduction. CONDITIONAL ON Theorem 3.1 and hSingular only. -/
theorem levelGP_of_thm31_singular221 (θ : ℝ) (hθ : θ ≤ 1)
    (h31 : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → BetaLevel θ η)
    (hSingular : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      ∀ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d| ≤ Cs * Real.log X ^ 2 / d) :
    LevelGP θ := by
  exact levelGP_of_thm31_PNT_singular221 θ hθ h31 scalar_pnt221 hSingular

end LeanLab.Akeno2026.PNTInstance221
