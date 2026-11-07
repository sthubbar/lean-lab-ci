/-
A split of the mean square estimate `meanSquare38` into four leaves, plus an assembly that
combines them.

The mean square runs over every `N ≤ X`, so the first step is the parity of `N`.  On an odd `N`
the singular series vanishes, because a pair of odd summands cannot sum to an odd number, so
there `E2` is just the weighted representation count `r2`, and only the prime powers `N - 2^k`
survive.  The even `N` are the part with a main term and carry all of the analytic content: the
major arcs, where the zero-free hypothesis governs the zeros, and the minor arcs, bounded by a
second moment.  The exponent `3/2 + 2Θ + ε` is large enough to absorb the odd part and the
logarithms because a zero-free bound can never hold below `Θ = 1/2`.

The leaves are (1) the exponent compatibility `1/2 ≤ Θ` forced by the functional equation,
(2) the vanishing of the singular series at an odd `N`, (3) the second moment of `r2` over the
odd `N`, and (4) the second moment of `E2` over the even `N`.
AI wrote the Lean code.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-- LEAF. Step 1, the exponent: a zero-free bound at level `Θ` can never hold with `Θ` below one
half, since the functional equation puts a zero of the Riemann zeta function on the line
`Re s = 1/2`. This is the step that lets the mean square exponent `3/2 + 2Θ + ε` dominate an
exponent of two and a logarithm, so every `Θ` under the hypothesis of the theorem is at least
`1/2`. -/
theorem meanSquare38_theta_lower {Θ : ℝ} (hZ : ZeroBound Θ) : 1 / 2 ≤ Θ := by
  sorry

/-- LEAF. Step 2, the odd numbers: the singular series vanishes at an odd `N`. A local factor of
the Euler product of the singular series at the prime two counts pairs of odd summands, and an
odd `N` has none, so the whole product vanishes. This is the step that removes the main term
`N 𝔖(N)` from `E2 N` on the odd `N`. -/
theorem meanSquare38_odd_singular (N : ℕ) (hN : Odd N) : singular N = 0 := by
  sorry

/-- LEAF. Step 3, the second moment over the odd `N`: for an odd `N` a summand of `N` which is a
prime power must be a power of two, so `r2 N` is at most `log 2` times a sum of `Λ` over the
`N - 2^k`. Squaring and summing over the odd `N ≤ X` therefore costs a fixed power of a
logarithm, which a `(log X) ^ 4` absorbs into a constant times `X ^ 2`. -/
theorem meanSquare38_odd_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Odd N), (r2 N) ^ 2 ≤ C * (X : ℝ) ^ 2 := by
  sorry

/-- LEAF. Step 4, the second moment over the even `N`: this is the analytic content of the
estimate, for the `N` that carry a main term. The circle method splits `r2` into the major arcs,
where the zero-free hypothesis bounds the contribution of the zeros, and the minor arcs, whose
second moment is bounded by a mean square of the prime exponential sum; the resulting mean square
of `E2` over the even `N ≤ X` is at most a constant times `X ^ (3/2 + 2Θ + ε)`. -/
theorem meanSquare38_even_energy (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- The mean square estimate, assembled from the four leaves: the sum over `N ≤ X` splits into
the even and the odd `N`, the odd part becomes the second moment of `r2` by the vanishing of the
singular series there, and both parts are dominated by `X ^ (3/2 + 2Θ + ε)` because `Θ ≥ 1/2`
puts two below that exponent. -/
theorem meanSquare38_split : MeanSquare38 := by
  intro Θ hΘ hZ ε hε
  obtain ⟨C₁, hC₁⟩ := meanSquare38_even_energy Θ hΘ hZ ε hε
  obtain ⟨C₂, hC₂pos, hC₂⟩ := meanSquare38_odd_energy
  refine ⟨C₁ + C₂, ?_⟩
  intro X hX
  have hhalf : (1 : ℝ) / 2 ≤ Θ := meanSquare38_theta_lower hZ
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hp : (2 : ℝ) ≤ 3 / 2 + 2 * Θ + ε := by linarith
  have hXp : (X : ℝ) ^ (2 : ℝ) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 hp
  have hXp2 : (X : ℝ) ^ 2 ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    simpa using hXp
  have hsplit :
      (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2) +
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 =
      ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2 :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 X)
      (p := fun N => Even N) (f := fun N => (E2 N) ^ 2)
  have hodd :
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 ≤ C₂ * (X : ℝ) ^ 2 := by
    have hEq :
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 =
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Odd N), (r2 N) ^ 2 := by
      refine Finset.sum_congr ?_ ?_
      · ext N
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1, Nat.not_even_iff_odd.mp h.2⟩,
          fun h => ⟨h.1, Nat.not_even_iff_odd.mpr h.2⟩⟩
      · intro N hN
        rw [Finset.mem_filter] at hN
        have h0 : singular N = 0 := meanSquare38_odd_singular N hN.2
        simp only [E2, h0, mul_zero, sub_zero]
    rw [hEq]
    exact hC₂ X hX
  have heven := hC₁ X hX
  calc ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2
      = (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2) +
          ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 := hsplit.symm
    _ ≤ C₁ * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + C₂ * (X : ℝ) ^ 2 := by linarith
    _ ≤ C₁ * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + C₂ * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
      have := mul_le_mul_of_nonneg_left hXp2 hC₂pos.le
      linarith
    _ = (C₁ + C₂) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.meanSquare38_split
