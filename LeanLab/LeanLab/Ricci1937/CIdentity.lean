import LeanLab.Ricci1937.CIdentityDecomp
import LeanLab.Ricci1937.CErrorAbsorption
import LeanLab.Ricci1937.CLinear

/-!
Ricci 1937, page 74: Theorem C part 1 for the identity polynomial.
This proves one degree one instance, not all primitive linear polynomials.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Filter Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The elementary upper count for F = X. -/
theorem c1Identity_upper :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      (c1IdentityCount ξ : ℝ) < a * ξ / Real.log ξ := by
  obtain ⟨K, hK, hprime⟩ := ricci_primeCounting_upper
  obtain ⟨D, hD, hpairs⟩ := ricciPrimePairValues_upper (α := (1 : ℝ) / 6) (by norm_num)
  have hsqrt := ricci_power_error_absorb (κ := (1 : ℝ) / 2) (a := 2)
    (by norm_num) (by norm_num) 1
  have hevent : ∀ᶠ n : ℕ in atTop,
      (c1IdentityCount n : ℝ) < (K + D + 2) * n / Real.log n := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hprime, hpairs,
      hsqrt, eventually_ge_atTop 4] with n hnprime hnpairs hnsqrt hn4
    have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log n := Real.log_pos hnR
    have hprime' : (n.primeCounting : ℝ) ≤ K * n / Real.log n := by
      simpa only [Nat.floor_natCast] using hnprime
    have hsqrt' : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) / Real.log n := by
      convert hnsqrt using 1 <;> norm_num
    have hfloor : (⌊(n : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℝ) ≤ (n : ℝ) / Real.log n :=
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans hsqrt'
    have hcount : (c1IdentityCount n : ℝ) ≤
        (⌊(n : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℝ) + n.primeCounting +
          #(ricciPrimePairValues n ((1 : ℝ) / 6)) := by
      exact_mod_cast c1Identity_count_le n hn4
    calc
      (c1IdentityCount n : ℝ) ≤
          (n : ℝ) / Real.log n + K * n / Real.log n + D * n / Real.log n := by
        linarith
      _ = (K + D + 1) * n / Real.log n := by ring
      _ < (K + D + 2) * n / Real.log n := by
        apply div_lt_div_of_pos_right _ hlog
        nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨K + D + 2, by positivity, N, fun ξ hξ => hN ξ (by omega)⟩

/-- The two sided count of Theorem C part 1 for F = X. -/
theorem c1Identity_estimate :
    ∃ a₁ a₂ : ℝ, 0 < a₁ ∧ 0 < a₂ ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      a₁ * ξ / Real.log ξ < c1IdentityCount ξ ∧
      (c1IdentityCount ξ : ℝ) < a₂ * ξ / Real.log ξ := by
  obtain ⟨a₁, ha₁, N₁, h₁⟩ := c1Identity_lower
  obtain ⟨a₂, ha₂, N₂, h₂⟩ := c1Identity_upper
  exact ⟨a₁, a₂, ha₁, ha₂, max N₁ N₂, fun ξ hξ =>
    ⟨h₁ ξ (by omega), h₂ ξ (by omega)⟩⟩

/-- The identity instance uses exactly the existing Fval normalization. -/
theorem theoremC1_identity :
    ∃ a₁ a₂ : ℝ, 0 < a₁ ∧ 0 < a₂ ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      a₁ * ξ / Real.log ξ < #{n ∈ Icc (1 : ℕ) ξ | AlmostGT 2
        (((n : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) (Fval (Polynomial.X : Polynomial ℤ) n)} ∧
      (#{n ∈ Icc (1 : ℕ) ξ | AlmostGT 2 (((n : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
        (Fval (Polynomial.X : Polynomial ℤ) n)} : ℝ) < a₂ * ξ / Real.log ξ := by
  simpa only [Fval_of_linear Polynomial.monic_X.isPrimitive (by simp),
    Polynomial.eval_X, Int.toNat_natCast, c1IdentityCount] using c1Identity_estimate

end
end LeanLab.Ricci1937
