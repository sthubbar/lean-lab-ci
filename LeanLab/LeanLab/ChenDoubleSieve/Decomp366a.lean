import LeanLab.ChenDoubleSieve.Decomp366h
import LeanLab.ChenDoubleSieve.Decomp363b
import LeanLab.ChenDoubleSieve.Decomp348b

/-!
Supply split for the finite F4 lower bound.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
The discrepancy has not been absorbed into the sieve error.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The absolute pair discrepancy is nonnegative. -/
theorem rawRemainder4_nonneg (B : ℝ) (N : ℕ) : 0 ≤ rawRemainder4 B N := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- LEAF. Wu 2004 page 39 equation 10.5, lower sieve part of the
application of Lemma 2.2, as in the preceding page 38 argument.
Retain the arithmetic progression discrepancy with its sieve constant.
Retain the li main term and the total reciprocal totient mass.
Only the local density scale is normalized into Theta.
Neither the li replacement nor the mean value bound has been applied. -/
theorem pair_linear_sieve_with_remainder (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        liMain4 f B N - δ * Θ N * lowerTotientMass4 N -
          C * rawRemainder4 B N ≤ sieveTerms N 4 := by
  sorry

/-- Wu 2004 page 39 equation 10.5, mean value part of the
application of Lemma 2.3, as in the preceding error display on that page.
This bound contains no sifted count and no linear sieve function.
OPEN only through Task363.remainder_log_cubic. No new pair mean value leaf is used. -/
theorem pair_remainder_log_cubic : ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      rawRemainder4 B N ≤ D * (N : ℝ) / log N ^ 3 := by
  exact pair_remainder_of_single Task363.remainder_log_cubic

/-- The exact sealed main4_lower target follows from the two smaller inputs.
OPEN through the lower sieve construction and the pair mean value estimate.
This assembly calls neither original OPEN theorem. -/
theorem main4_lower_supplied (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main4 f B N - η * Θ N ≤ sieveTerms N 4 := by
  intro η hη
  obtain ⟨K, hK, M, hM⟩ := lowerTotientMass4_bounded
  obtain ⟨C, hC, hs⟩ := pair_linear_sieve_with_remainder F f h
    (η / (3 * K)) (by positivity)
  obtain ⟨B, hB, D, hD, L, hL⟩ := pair_remainder_log_cubic
  obtain ⟨J, hJ⟩ := hs B hB
  obtain ⟨T, hT⟩ := Task363.log_cubic_absorbed (C * D) (η / 3)
    (mul_nonneg hC hD) (by positivity)
  obtain ⟨U, hU⟩ := liMain4_error_absorbed F f h B hB (η / 3) (by positivity)
  refine ⟨B, hB, max 2 (max M (max L (max J (max T U)))), ?_⟩
  intro N hEven hN
  have ht : 0 < Θ N := Θ_pos (by omega)
  have hbudget : η / (3 * K) * Θ N * lowerTotientMass4 N ≤ η / 3 * Θ N := by
    calc
      _ ≤ η / (3 * K) * Θ N * K :=
        mul_le_mul_of_nonneg_left (hM N (by omega)) (by positivity)
      _ = _ := by field_simp
  have hraw := mul_le_mul_of_nonneg_left (hL N hEven (by omega)) hC
  have hsmall := hT N (by omega)
  have heq : C * (D * (N : ℝ) / log N ^ 3) =
      (C * D) * (N : ℝ) / log N ^ 3 := by ring
  rw [heq] at hraw
  have hbound := hJ N hEven (by omega)
  have hli := le_trans (le_abs_self (main4 f B N - liMain4 f B N))
    (hU N hEven (by omega))
  linarith

end LeanLab.ChenDoubleSieve.Task366
