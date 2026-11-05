import LeanLab.ChenDoubleSieve.Decomp367j

/-!
Reuse the single modulus mean value input in the exact finite F5 supply.
Source: https://arxiv.org/pdf/0705.1652, pages 6, 38 and 39 equation 10.5.
The pair estimate reuses the existing single modulus mean value input.
The lower sieve construction and the existing single modulus input remain OPEN.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The finite level is at most N when its logarithmic loss is nonnegative
and log N is at least one. -/
theorem sieveLevel_le_self {N : ℕ} (hN : 2 ≤ N) (hlog : 1 ≤ log (N : ℝ))
    {B : ℝ} (hB : 0 ≤ B) : Task363.sieveLevel B N ≤ N := by
  calc
    _ ≤ Task363.sieveLevel 0 N := Task363.sieveLevel_antitone hlog hB
    _ = (N : ℝ) ^ (1 / 2 : ℝ) := by simp [Task363.sieveLevel]
    _ ≤ (N : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
    _ = N := rpow_one _

/-- The existing single modulus mean value estimate implies the pair estimate.
CONDITIONAL ON the explicitly displayed single modulus analytic input. -/
theorem pair_remainder_of_single
    (hsingle : ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        Task363.rawRemainder B N ≤ D * (N : ℝ) / log N ^ 3) :
    ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        rawRemainder5 B N ≤ D * (N : ℝ) / log N ^ 3 := by
  obtain ⟨B, hB, D, hD, M, hM⟩ := hsingle
  have hl : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hl.eventually_ge_atTop 1)
  refine ⟨B, hB, 144 * D, by positivity, max 2 (max M J), ?_⟩
  intro N hEven hN
  calc
    _ ≤ 144 * Task363.rawRemainder B N :=
      rawRemainder5_le_single (by omega) (sieveLevel_le_self (by omega) (hJ N (by omega)) hB.le)
    _ ≤ 144 * (D * (N : ℝ) / log N ^ 3) := by gcongr; exact hM N hEven (by omega)
    _ = (144 * D) * (N : ℝ) / log N ^ 3 := by ring

/-- The exact pair mean value target is supplied by the existing single modulus leaf.
OPEN through Task363.remainder_log_cubic only. No pair mean value leaf is called. -/
theorem pair_remainder_supplied : ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      rawRemainder5 B N ≤ D * (N : ℝ) / log N ^ 3 := by
  exact pair_remainder_of_single Task363.remainder_log_cubic

/-- The exact sealed main5_lower target now uses the raw lower sieve leaf
and the existing single modulus mean value input only.
OPEN through pair_linear_sieve_with_remainder and Task363.remainder_log_cubic. -/
theorem main5_lower_from_single (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main5 f B N - η * Θ N ≤ sieveTerms N 5 := by
  intro η hη
  obtain ⟨K, hK, M, hM⟩ := lowerTotientMass5_bounded
  obtain ⟨C, hC, hs⟩ := pair_linear_sieve_with_remainder F f h
    (η / (3 * K)) (by positivity)
  obtain ⟨B, hB, D, hD, L, hL⟩ := pair_remainder_supplied
  obtain ⟨J, hJ⟩ := hs B hB
  obtain ⟨T, hT⟩ := Task363.log_cubic_absorbed (C * D) (η / 3)
    (mul_nonneg hC hD) (by positivity)
  obtain ⟨U, hU⟩ := liMain5_error_absorbed F f h B hB (η / 3) (by positivity)
  refine ⟨B, hB, max 2 (max M (max L (max J (max T U)))), ?_⟩
  intro N hEven hN
  have ht : 0 < Θ N := Θ_pos (by omega)
  have hbudget : η / (3 * K) * Θ N * lowerTotientMass5 N ≤ η / 3 * Θ N := by
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
  have hli := le_trans (le_abs_self (main5 f B N - liMain5 f B N))
    (hU N hEven (by omega))
  linarith

end LeanLab.ChenDoubleSieve.Task367
