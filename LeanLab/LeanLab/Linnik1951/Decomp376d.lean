/-
P0093 pages 165 to 168. Separate the local expansion from its relative correction.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357b

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 168 left side of equation 10.7 without its implicit
constant. This is the nonnegative logarithmic relative correction,
retaining the finite singular coefficient at each residual. -/
noncomputable def majorRelative376 (k N : ℕ) : ℝ :=
  ∑ ν ∈ residualTuples357 k N,
    ((N - ∑ i, 2 ^ (ν i).val : ℕ) : ℝ) /
      Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2 *
      (1 / Real.sqrt (Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ))) *
      |truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val)|

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2.
The local major arc expansion leaves its logarithmic relative correction
explicit. The other term weakens the power saving in equation 8.2.
No estimate for the relative correction is included here. -/
theorem major_expansion_remainder376 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        A * majorRelative376 k N +
          A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
  sorry

/-- LEAF. P0093 page 168 equation 10.7. The logarithmic relative
correction is negligible compared with scale for fixed k. This arithmetic
summation has no GRH or Mellin hypothesis and contains no arc integral. -/
theorem major_relative_negligible376 (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      majorRelative376 k N ≤ ε * scale111 k N := by
  sorry

/-- P0093 page 168 equation 10.7. Exact major_to_truncated357 statement.
CONDITIONAL on the local expansion and arithmetic relative correction
leaves. Fixed logarithmic powers are absorbed using the proved bound. -/
theorem major_to_truncated_decomposed376 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        ε * scale111 k N := by
  obtain ⟨A, hA, Na, ha⟩ := major_expansion_remainder376 hG hM k hk
  obtain ⟨Nr, hr⟩ := major_relative_negligible376 k hk (ε / (2 * A)) (by positivity)
  obtain ⟨Np, hp⟩ := power_saving_negligible357 A (1 / 1000) hA
    (by norm_num) (k + 13) (ε / 2) (by positivity)
  refine ⟨max 2 (max Na (max Nr Np)), ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNa : Na < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNr : Nr < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNp : Np < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hscale : (N : ℝ) ≤ scale111 k N := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h2.le)
    have hr : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hl)
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hr)
  have hrel : A * majorRelative376 k N ≤ (ε / 2) * scale111 k N := by
    calc
      _ ≤ A * (ε / (2 * A) * scale111 k N) :=
        mul_le_mul_of_nonneg_left (hr N hev hNr) hA.le
      _ = _ := by field_simp [hA.ne']
  have hpower : A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) ≤
      (ε / 2) * scale111 k N :=
    (hp N hNp).trans (mul_le_mul_of_nonneg_left hscale (by positivity))
  calc
    _ ≤ A * majorRelative376 k N +
        A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := ha N hev hNa
    _ ≤ (ε / 2) * scale111 k N + (ε / 2) * scale111 k N := add_le_add hrel hpower
    _ = _ := by ring

end LeanLab.Linnik1951
