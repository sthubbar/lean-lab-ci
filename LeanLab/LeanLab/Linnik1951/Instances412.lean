/-
P0093 pages 162 and 163. Concrete and positive measure supply instances.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp412c
import LeanLab.Linnik1951.Packing412

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- P0093 page 162 equation 7.7. At N equal to two the finite
polynomial at zero has its single positive term exp of negative one. -/
theorem power_trunc_two412 : powerTrunc412 2 0 = (Real.exp (-1) : ℂ) := by
  norm_num [powerTrunc412]

/-- P0093 page 163 equation 7.11. A whole interval around zero, of
radius two to the negative sum of M and r, has all M dyadic phases in range.
This is a positive length instance of the binary concentration set. -/
theorem near_indices_interval412 (M r : ℕ) (α : ℝ)
    (hα : |α| ≤ (1 / 2 : ℝ) ^ (M + r)) :
    (nearIntegerIndices412 M r α).card = M := by
  classical
  have heq : nearIntegerIndices412 M r α = range M := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    refine ⟨0, ?_⟩
    simp only [Int.cast_zero, sub_zero, abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
    have hpow : (2 : ℝ) ^ (m + 1) ≤ 2 ^ M :=
      pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hm)
    calc
      _ ≤ (1 / 2 : ℝ) ^ (M + r) * (2 : ℝ) ^ M :=
        mul_le_mul hα hpow (by positivity) (by positivity)
      _ = (1 / 2 : ℝ) ^ r := by
        rw [pow_add, one_div_pow]
        field_simp
  rw [heq, Finset.card_range]

/-- P0093 page 163 equation 7.11 and page 165 entropy measure bound.
For every nonnegative exceptional fraction the actual binary phase
set in three periods has strictly positive measure at each finite M.
This excludes an empty set justification of the entropy supply leaf. -/
theorem binary_set_positive_measure412 (M r : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    0 < volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} := by
  let R := (1 / 2 : ℝ) ^ (M + r)
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsub : Set.Icc (-R) R ⊆ {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} := by
    intro α hα
    refine ⟨⟨by linarith [hα.1], by linarith [hα.2]⟩, ?_⟩
    rw [near_indices_interval412 M r α (abs_le.mpr hα)]
    nlinarith [mul_nonneg hε (Nat.cast_nonneg (α := ℝ) M)]
  have hfinite : volume {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc] : volume (Set.Icc (-1 : ℝ) 2) ≠ ⊤)
      (measure_mono (fun α hα => hα.1))
  have hpos : 0 < volume.real (Set.Icc (-R) R) := by
    rw [Real.volume_real_Icc, sub_neg_eq_add, max_eq_left (by linarith : 0 ≤ R + R)]
    linarith
  exact hpos.trans_le (measureReal_mono hsub hfinite)

/-- P0093 page 162 equation 7.7. For every N at least two and every
positive eta, phase zero lies in the actual finite polynomial large
value set. The eventual concentration hypothesis is therefore nonempty. -/
theorem finite_large_value_zero412 (N : ℕ) (hN : 2 ≤ N) (η : ℝ) (hη : 0 < η) :
    (0 : ℝ) ∈ {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖} := by
  have hlog : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have hlogR : (1 : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hlog
  have hb := power_trunc_zero_lower412 N (by omega)
  have hp : 0 < ‖powerTrunc412 N 0‖ := by nlinarith [Real.exp_pos (-1)]
  exact ⟨by norm_num, by nlinarith [mul_pos hη hp]⟩

end LeanLab.Linnik1951
