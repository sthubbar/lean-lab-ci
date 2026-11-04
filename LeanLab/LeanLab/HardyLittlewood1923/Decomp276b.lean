/-
AI wrote this Lean code for CODEX task276.
P0004 pages 23 to 25 equations 3.124 to 3.142.
Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.Decomp276a
import LeanLab.HardyLittlewood1923.WeightedContour

namespace LeanLab.HardyLittlewood1923.Decomp276b

open Real Finset
open scoped ArithmeticFunction.Moebius
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp105
open LeanLab.HardyLittlewood1923.Decomp276a

/-- The prime generating series in exponential coordinates.
P0004 page 5 equation 1.31. -/
noncomputable def primeSeries (z : ℂ) : ℂ :=
  ∑' m : ℕ, if m.Prime then (Real.log m : ℂ) * Complex.exp (-(m : ℂ) * z) else 0

/-- P0004 page 5 equation 1.31. The prime series is absolutely convergent in the right half plane. -/
theorem primeSeries_summable {z : ℂ} (hz : 0 < z.re) :
    Summable (fun m : ℕ => if m.Prime then
      (Real.log m : ℂ) * Complex.exp (-(m : ℂ) * z) else 0) := by
  have hb : ∀ m : ℕ, ‖if m.Prime then (Real.log m : ℂ) else 0‖ ≤
      ArithmeticFunction.vonMangoldt m := by
    intro m
    split_ifs with hm
    · rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg m), ArithmeticFunction.vonMangoldt_apply_prime hm]
    · simp
  simpa only [ite_mul, zero_mul] using (Task52.summable_exponential hb hz)

/-- The local parameter Y on the circle of radius exp of minus one over n.
P0004 page 23 equation 3.121 and page 25 equation 3.151. -/
noncomputable def localY (n : ℕ) (θ : ℝ) : ℂ := 1 / (n : ℂ) - Complex.I * θ

/-- The rational arc main approximation phi at r equal to three.
P0004 page 19 equation 2.822 and page 22 equation 3.118. -/
noncomputable def localPhi (n q : ℕ) (θ : ℝ) : ℂ :=
  ((μ q : ℂ) / (q.totient : ℂ)) / localY n θ

/-- The error Phi on the rational arc, using angular measure in radians.
P0004 page 23 equations 3.121 to 3.124. -/
noncomputable def localError (n p q : ℕ) (θ : ℝ) : ℂ :=
  primeSeries (localY n (2 * π * (p : ℝ) / q + θ)) - localPhi n q θ

/-- P0004 page 23 equation 3.121. The real part of Y is the positive radius parameter. -/
theorem localY_re (n : ℕ) (θ : ℝ) : (localY n θ).re = 1 / (n : ℝ) := by
  simp [localY]

/-- P0004 page 23 equation 3.121. The real axis value of the local parameter. -/
theorem localY_zero (n : ℕ) : localY n 0 = ((1 / (n : ℝ) : ℝ) : ℂ) := by
  simp [localY]

/-- LEAF. P0004 page 23 equation 3.124.
The uniform rational arc error retains the exponent Theta plus one quarter.
It contains no coefficient extraction and no finite singular series. -/
theorem uniform_arc_error {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ C * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A := by
  sorry

/-- LEAF. P0004 pages 22 to 25 equations 3.119, 3.131, 3.141 and 3.142.
The uniform arc error gives the coefficient error through two square mean integrals.
The input is the pointwise bound, rather than a cited analytic theorem. -/
theorem coefficient_error_of_uniform {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hE : ∃ A : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ C * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- P0004 pages 24 and 25, the exact sealed minor_arcs_bound statement from DecompJ203.
CONDITIONAL on the two OPEN leaves here and the shared model evaluation leaf. -/
theorem minor_arcs_bound {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  exact finite_approximation_of_farey hΘ0
    (coefficient_error_of_uniform hΘ0 hΘ1 (uniform_arc_error hΘ0 hΘ1 hZ))

#print axioms primeSeries_summable
#print axioms localY_re
#print axioms localY_zero
#print axioms uniform_arc_error
#print axioms coefficient_error_of_uniform
#print axioms minor_arcs_bound

end LeanLab.HardyLittlewood1923.Decomp276b
