/-
Split of the conductor zero major arc frequency estimate.
The frequency error is the norm of the difference of the arc integral and the main
term, so the estimate follows from a bound on each of the two summands separately.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp486b

namespace LeanLab.Linnik.Decomp486b

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries)
open LeanLab.Linnik.U7204 (Sg)

/-- A uniform absolute bound for the singular series at a nonzero frequency.
The two cited estimates at Gallagher 1975 p.130 bound the truncated series by
the totient weight and its tail by the same weight times the divisor count.
Taking the truncation level beyond the tail constant removes the divisor
count from the final uniform bound. -/
theorem singSeries_norm_le_totientWeight (n : ℤ) (hn : n ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ‖singSeries n‖ ≤ K * totientWeight n := by
  obtain ⟨K₂, hK₂, hW⟩ := LeanLab.Linnik.MajorArcEnergy.singular_weighted_sums_cited
  obtain ⟨K₃, hK₃, hT⟩ := LeanLab.Linnik.MajorArcEnergy.singular_tail_cited
  let d : ℝ := (n.natAbs.divisors.card : ℝ)
  let P : ℝ := max 2 (K₃ * d / K₂ + 1)
  refine ⟨2 * K₂, mul_pos (by positivity) hK₂, ?_⟩
  have hP2 : 2 ≤ P := le_max_left _ _
  have hP0 : 0 < P := by linarith
  have htw : 0 ≤ totientWeight n := by
    exact (LeanLab.Linnik.MajorArcEnergy.one_le_totientWeight hn).le
  have hWsum := hW P n hP2 hn
  have htail := hT P n hP2 hn
  have htrunc : ‖LeanLab.Linnik.MajorArcEnergy.singTrunc P n‖ ≤
      K₂ * totientWeight n := by
    calc
      ‖LeanLab.Linnik.MajorArcEnergy.singTrunc P n‖ =
          ‖∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
            ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
              LeanLab.Linnik.MajorArcEnergy.ramanujanSum q n‖ := rfl
      _ ≤ ∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
          ‖((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
            LeanLab.Linnik.MajorArcEnergy.ramanujanSum q n‖ := norm_sum_le _ _
      _ = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
          ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 *
            ‖LeanLab.Linnik.MajorArcEnergy.ramanujanSum q n‖ := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [LeanLab.Linnik.MajorArcEnergy.norm_summand]
        simp
      _ ≤ K₂ * totientWeight n := hWsum.2
  have hratio : K₃ * d / P ≤ K₂ := by
    rw [div_le_iff₀ hP0]
    have hP : K₃ * d / K₂ + 1 ≤ P := le_max_right _ _
    have hK₂0 : 0 < K₂ := hK₂
    have hK₃d : 0 ≤ K₃ * d := by positivity
    nlinarith
  calc
    ‖singSeries n‖ ≤ ‖LeanLab.Linnik.MajorArcEnergy.singTrunc P n‖ +
        ‖singSeries n - LeanLab.Linnik.MajorArcEnergy.singTrunc P n‖ := by
      have heq : singSeries n = LeanLab.Linnik.MajorArcEnergy.singTrunc P n +
          (singSeries n - LeanLab.Linnik.MajorArcEnergy.singTrunc P n) := by ring
      rw [heq]
      exact norm_add_le _ _
    _ ≤ K₂ * totientWeight n + K₃ * totientWeight n * d / P := by
      gcongr
      exact htail
    _ ≤ K₂ * totientWeight n + K₂ * totientWeight n := by
      have hmul : K₃ * totientWeight n * d / P ≤ K₂ * totientWeight n := by
        rw [show K₃ * totientWeight n * d / P = totientWeight n * (K₃ * d / P) by ring]
        exact mul_le_mul_of_nonneg_left hratio htw
      linarith
    _ = 2 * K₂ * totientWeight n := by ring

/-- LEAF. Step one of the triangle inequality: the major arc integral of the squared
generating function against the character exponential, taken in norm, is at most the
constant times the scale N over log squared N, the totient weight of the frequency,
and the sum of the divisor count term and the corrected energy term, the energy being
the conductor zero normalized energy. -/
theorem leaf_arc_integral_part_bound :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 →
          ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
                LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := by
  sorry

/-- LEAF. Step two of the triangle inequality: the product of the correlation count
with the singular series, taken in norm, is at most the constant times the same scale
N over log squared N, the totient weight of the frequency, and the sum of the divisor
count term and the conductor zero corrected energy term. -/
theorem leaf_main_series_part_bound :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 →
          ‖(Jn N n : ℂ) * singSeries n‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := by
  sorry

/-- The conductor zero frequency estimate follows from the two summand bounds.
Combine the two bounds with the triangle inequality, add the constants and take the
smaller of the two exponent thresholds. -/
theorem major_arc_energy_zero_split
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
          K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
            (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
              (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0)
:= by
  obtain ⟨K₁, θ₁, hK₁, hθ₁, hθ₁', hz₁⟩ := leaf_arc_integral_part_bound
  obtain ⟨K₂, θ₂, hK₂, hθ₂, hθ₂', hz₂⟩ := leaf_main_series_part_bound
  refine ⟨K₁ + K₂, min θ₁ θ₂, by linarith, lt_min hθ₁ hθ₂,
    (min_le_left _ _).trans hθ₁', ?_⟩
  intro θ hθ hθm
  obtain ⟨N₁, hN₁⟩ := hz₁ θ hθ (hθm.trans (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hz₂ θ hθ (hθm.trans (min_le_right _ _))
  refine ⟨max 2 (max N₁ N₂), ?_⟩
  intro N hN n hn
  have hN1 : N₁ ≤ N := (le_max_left N₁ N₂).trans ((le_max_right 2 _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right N₁ N₂).trans ((le_max_right 2 _).trans hN)
  have hsplit : complexFrequencyError N θ n ≤
      ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
          ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ +
        ‖(Jn N n : ℂ) * singSeries n‖ := by
    unfold complexFrequencyError
    exact norm_sub_le _ _
  have hI := hN₁ N hN1 n hn
  have hT := hN₂ N hN2 n hn
  calc complexFrequencyError N θ n ≤
      ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
          ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ +
        ‖(Jn N n : ℂ) * singSeries n‖ := hsplit
    _ ≤ K₁ * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) +
        K₂ * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := add_le_add hI hT
    _ = (K₁ + K₂) * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := by
      ring

end LeanLab.Linnik.Decomp486b

open LeanLab.Linnik.Decomp486b in
#print axioms major_arc_energy_zero_split
