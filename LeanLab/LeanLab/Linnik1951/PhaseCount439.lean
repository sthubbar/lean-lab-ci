/-
P0093 page 163 equations 7.10 and 7.11.
Count phases outside a prescribed binary radius using their cosine deficits.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Phase439

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 163 equation 7.11. The number of phases farther than
two to negative r from every integer, times the quadratic threshold, is
at most their total cosine deficit. This is the finite counting step. -/
theorem bad_phase_card439 (M r : ℕ) (α : ℝ) :
    ((M : ℝ) - (nearIntegerIndices412 M r α).card) * (8 * ((1 / 2 : ℝ) ^ r) ^ 2) ≤
      ∑ m ∈ range M, (1 - Real.cos (2 * Real.pi * (α * (2 : ℝ) ^ (m + 1)))) := by
  classical
  let B := range M \ nearIntegerIndices412 M r α
  have hsub : nearIntegerIndices412 M r α ⊆ range M := Finset.filter_subset _ _
  have hcard : (nearIntegerIndices412 M r α).card ≤ M := by
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hbad (m : ℕ) (hm : m ∈ B) : 8 * ((1 / 2 : ℝ) ^ r) ^ 2 ≤
      1 - Real.cos (2 * Real.pi * (α * (2 : ℝ) ^ (m + 1))) := by
    obtain ⟨hmrange, hmnot⟩ := Finset.mem_sdiff.mp hm
    let x := α * (2 : ℝ) ^ (m + 1)
    have hfar : (1 / 2 : ℝ) ^ r < |x - (round x : ℤ)| := by
      by_contra hle
      apply hmnot
      exact Finset.mem_filter.mpr ⟨hmrange, round x, le_of_not_gt hle⟩
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ r) hfar.le 2
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans (phase_distance_deficit439 x)
  calc
    _ = ∑ _m ∈ B, (8 * ((1 / 2 : ℝ) ^ r) ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      dsimp [B]
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_range, Nat.cast_sub hcard]
    _ ≤ ∑ m ∈ B, (1 - Real.cos (2 * Real.pi * (α * (2 : ℝ) ^ (m + 1)))) :=
      Finset.sum_le_sum hbad
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun m hm hnot => sub_nonneg.mpr (Real.cos_le_one _))

end LeanLab.Linnik1951
