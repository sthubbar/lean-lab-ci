/-
Split of nonprincipal_sum435 into four smaller estimates from P0093 page 159
equation 5.2. Each LEAF isolates one factor of the bound: the single
character integral, the totient count, the R dependence, and the
logarithmic power. The assembly nonprincipal_sum435_F665 proves the exact
target statement from those leaves without sorry.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_doubled_system_expansion435

namespace LeanLab.Linnik1951

open MeasureTheory
open Filter
open scoped Topology

/-! ### LEAF lemmas for the nonprincipal Mellin estimate -/

/-- LEAF. P0093 page 159 equation 5.1 for a single nonprincipal character.
The square integral of one character prime sum over the interval of radius
two over R is at most a constant times N over R times log N to the
thirteenth, independent of the modulus. This is the per-character Mellin
bound before summing over all nonprincipal characters. -/
theorem single_character_integral_bound_F665 (hG : LeanLab.DERZ1997.GRH) :
    ∃ (X : ℝ), 0 < X ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ (q : ℕ) [NeZero q], 2 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        (∫ z in -(2 / R)..(2 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤
          X * ((N : ℝ) / R * Real.log N ^ 13) := by
  sorry

/-- LEAF. The number of nonprincipal characters modulo q is at most the
totient of q. This is the counting step that introduces the totient factor
into the final bound. -/
theorem nonprincipal_character_count_F665 (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) ≤
      (q.totient : ℝ) := by
  sorry

/-- LEAF. P0093 page 159 equation 5.2, the R dependence. For fixed N and q,
the bound N over R times log N to the thirteenth decreases as R increases,
and the interval of radius two over R shrinks accordingly. This leaf
captures that the worst case is R equals one. -/
theorem radius_dependence_bound_F665 (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (R : ℝ)
    (hR1 : 1 ≤ R) (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) (X : ℝ) (hX : 0 < X) :
    X * ((N : ℝ) / R * Real.log N ^ 13) ≤ X * ((N : ℝ) / 1 * Real.log N ^ 13) := by
  sorry

/-- LEAF. P0093 page 159 equation 5.2, the logarithmic power absorption.
For N at least some absolute threshold, log N to the thirteenth is at most
N to the one seventh, so the bound can be simplified. This leaf provides
the inequality that absorbs the logarithmic factor. -/
theorem log_power_absorption_F665 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → Real.log N ^ 13 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
  sorry

/-! ### Assembly theorem -/

/-- The exact statement of nonprincipal_sum435, proved from the four LEAF
lemmas above. -/
theorem nonprincipal_sum435_F665 (hG : LeanLab.DERZ1997.GRH) :
    ∃ X : ℝ, 0 < X ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ (q : ℕ) [NeZero q], 2 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ∫ z in -(2 / R)..(2 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤
          X * (q.totient : ℝ) * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨X, hX, N1, hsingle⟩ := single_character_integral_bound_F665 hG
  obtain ⟨N2, hlog⟩ := log_power_absorption_F665
  refine ⟨X, hX, max N1 N2, ?_⟩
  intro N hN q _ hq hqN R hR1 hR2
  have hN1 : N1 < N := lt_of_lt_of_le (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_lt_of_le (le_max_right _ _) hN
  have hlogN : Real.log N ^ 13 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := hlog N hN2
  calc
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ∫ z in -(2 / R)..(2 / R), ‖characterPrime280 χ N z‖ ^ 2)
      ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          (X * ((N : ℝ) / R * Real.log N ^ 13)) := by
      refine Finset.sum_le_sum fun χ hχ => ?_
      rw [Finset.mem_filter] at hχ
      exact hsingle N hN1 q hq hqN R hR1 hR2 χ hχ.2
    _ = ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) *
          (X * ((N : ℝ) / R * Real.log N ^ 13)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q.totient : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)) := by
      have hcount := nonprincipal_character_count_F665 q hq
      nlinarith [hX, hcount]
    _ = X * (q.totient : ℝ) * ((N : ℝ) / R * Real.log N ^ 13) := by ring

end LeanLab.Linnik1951
