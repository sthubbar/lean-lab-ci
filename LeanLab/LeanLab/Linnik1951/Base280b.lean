/-
P0093 Sections 3 to 10. Analytic decomposition of error_bound111.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp280a
import LeanLab.Linnik1951.Repair493Data

namespace LeanLab.Linnik1951

/-- P0093 page 159, the character prime sum preceding equation 5.1. -/
noncomputable def characterPrime280 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (α : ℝ) : ℂ :=
  ∑' p : Nat.Primes, χ (p : ℕ) * (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
    Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)

/-- CITED. P0093 page 159 equation 5.2 with equal nonprincipal characters
and tau equal to N to the one seventh. This is the Mellin estimate used below. -/
def MellinBound280 : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ ((N : ℝ) ^ (1 / 7 : ℝ)) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        (∫ α in -(1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))..(1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
          ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log N ^ 13

/-- P0093 page 165 Section 8. Major arcs with Q equal to N to the one tenth
and tau equal to N to the one seventh, clipped to the unit interval. -/
noncomputable def majorArcs280 (N : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ ∃ r : ℚ, (r.den : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
    |α - r| ≤ 1 / ((r.den : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))}

/-- P0093 pages 162 and 167. Exceptional minor points where T is large. -/
noncomputable def exceptionalArcs280 (N : ℕ) (η : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ α ∉ majorArcs280 N ∧
    (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖}

/-- P0093 page 167 before equation 10.1. The remaining minor points. -/
noncomputable def goodMinorArcs280 (N : ℕ) (η : ℝ) : Set ℝ :=
  Set.Icc 0 1 \ (majorArcs280 N ∪ exceptionalArcs280 N η)

/-- P0093 pages 154 and 167 equations 2.2 and 10.2. Real contribution of a
measurable arc set, including the factor e from exponential damping. -/
noncomputable def arcContribution280 (k N : ℕ) (s : Set ℝ) : ℝ :=
  Real.exp 1 * (∫ α in s, primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
    Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)).re


end LeanLab.Linnik1951
