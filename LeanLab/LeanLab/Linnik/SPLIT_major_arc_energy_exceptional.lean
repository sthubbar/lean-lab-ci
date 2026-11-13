/-
Split of the positive exceptional conductor major arc frequency estimate.
The frequency error is the norm of the difference of the arc integral and the
main term, so the estimate follows from a bound on each of the two summands.
Task497 source audit, Gallagher 1975 p.131 displays 13 and 15 to 17.
The paper bounds the difference of the integral and the main term. The separate
summand bounds below require an additional estimate. Both remain open.
Decomp497a records exact support cases and necessary main scale budgets.
It proves the separate main leaf equivalent to eventual absence of exceptional
conductors below P for all sufficiently small theta. Neither side is proved.
This is a question about the lab split and asserts no paper error.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp486b
import LeanLab.Linnik.Decomp497a

namespace LeanLab.Linnik.Decomp486b

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet majorArcs Jn singSeries)
open LeanLab.Linnik.U7204 (Sg)

/-- LEAF. Step one of the triangle inequality. The integral over the major arcs of the squared generating function against the complex exponential, taken in norm, is at most the scaled weight times the sum of the divisor term, the corrected energy term and the exceptional coefficient term, for the parameters of the exceptional case. -/
theorem leaf_arc_integral_part_bound :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by
  sorry

/-- LEAF. Step two of the triangle inequality. The product of the correlation count with the singular series, taken in norm, is at most the scaled weight times the sum of the divisor term, the corrected energy term and the exceptional coefficient term, for the parameters of the exceptional case. -/
theorem leaf_main_series_part_bound :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → ‖(Jn N n : ℂ) * singSeries n‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by
  sorry

/-- The positive exceptional conductor estimate follows from the two summand bounds.
Combine the two bounds with the triangle inequality, add the constants and take the
smaller of the two exponent thresholds. -/
theorem major_arc_energy_exceptional_split
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by
  obtain ⟨K₁, θ₁, hK₁, hθ₁, hθ₁', hz₁⟩ := leaf_arc_integral_part_bound
  obtain ⟨K₂, θ₂, hK₂, hθ₂, hθ₂', hz₂⟩ := leaf_main_series_part_bound
  refine ⟨K₁ + K₂, min θ₁ θ₂, by linarith, lt_min hθ₁ hθ₂,
    (min_le_left _ _).trans hθ₁', ?_⟩
  intro θ hθ hθm
  obtain ⟨N₁, hN₁⟩ := hz₁ θ hθ (hθm.trans (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hz₂ θ hθ (hθm.trans (min_le_right _ _))
  refine ⟨max 2 (max N₁ N₂), ?_⟩
  intro N hN r γ hr hrpos n hn
  have h2N : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right 2 _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right 2 _).trans hN)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hP1 : 1 ≤ (N : ℝ) ^ θ :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) hθ.le
  have htw : 0 ≤ totientWeight n := by unfold totientWeight; positivity
  have hA : 0 ≤ Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card :=
    mul_nonneg (div_nonneg (Real.log_nonneg hP1) (by positivity)) (by positivity)
  have hE := normalizedEnergy_nonneg h2N θ r γ
  have hEE : 0 ≤ (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ :=
    mul_nonneg (by linarith) hE
  have hEx : 0 ≤ exceptionalWeight r n := by unfold exceptionalWeight; positivity
  have hMP : 0 ≤ ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) :=
    mul_nonneg (mul_nonneg (div_nonneg (by positivity) (pow_pos hlog 2).le) htw)
      (by linarith)
  have hI := hN₁ N hN1 r γ hr hrpos n hn
  have hT := hN₂ N hN2 r γ hr hrpos n hn
  have hsplit : complexFrequencyError N θ n ≤
      ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ +
      ‖(Jn N n : ℂ) * singSeries n‖ := by
    unfold complexFrequencyError
    exact norm_sub_le _ _
  calc complexFrequencyError N θ n ≤
      ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ +
      ‖(Jn N n : ℂ) * singSeries n‖ := hsplit
    _ ≤ K₁ * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) + K₂ * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := add_le_add hI hT
    _ = (K₁ + K₂) * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by ring

end LeanLab.Linnik.Decomp486b

open LeanLab.Linnik.Decomp486b in
#print axioms major_arc_energy_exceptional_split
