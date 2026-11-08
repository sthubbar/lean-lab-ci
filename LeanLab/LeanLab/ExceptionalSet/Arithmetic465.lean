import LeanLab.ExceptionalSet.Gcd465
import LeanLab.HeathBrown1985.DivisorEps
import LeanLab.HeathBrown1985.Elementary

/-!
The divisor arithmetic after P0082 page 364 display 22.
These statements do not use a distribution estimate for the sparse sequence.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Finset Real

/-- P0082 page 364 after display 22. A conductor above E to one seventh
makes tau r divided by r at most a fixed multiple of E to minus one twelfth. -/
theorem divisor_count_ratio :
    ∃ D : ℝ, 0 < D ∧ ∀ E : ℝ, 1 ≤ E → ∀ r : ℕ, 1 ≤ r →
      E ^ (1 / 7 : ℝ) < (r : ℝ) →
        (r.divisors.card : ℝ) / r ≤ D * E ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨D, hD, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 4 (by norm_num)
  refine ⟨D, hD, fun E hE r hr hlarge => ?_⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hpower : (r : ℝ) ^ (-(3 / 4 : ℝ)) ≤ E ^ (-(1 / 12 : ℝ)) := by
    calc
      _ ≤ (E ^ (1 / 7 : ℝ)) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hE0 _) hlarge.le (by norm_num)
      _ = E ^ (-(3 / 28 : ℝ)) := by rw [← Real.rpow_mul hE0.le]; norm_num
      _ ≤ E ^ (-(1 / 12 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  calc
    _ ≤ (D * (r : ℝ) ^ ((4 : ℝ)⁻¹)) / r :=
      div_le_div_of_nonneg_right (hτ r hr) hr0.le
    _ = D * (r : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [mul_div_assoc, ← Real.rpow_sub_one hr0.ne']
      norm_num
    _ ≤ D * E ^ (-(1 / 12 : ℝ)) := mul_le_mul_of_nonneg_left hpower hD.le

/-- P0082 page 364 display 22. Sigma r divided by r is at most one plus log r. -/
theorem divisor_sum_ratio (r : ℕ) (hr : 0 < r) :
    (∑ d ∈ r.divisors, (d : ℝ)) / r ≤ 1 + Real.log r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  calc
    _ = ∑ d ∈ r.divisors, (d : ℝ)⁻¹ := by
      rw [← Nat.sum_div_divisors r (fun d : ℕ => (d : ℝ)), sum_div]
      apply sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      have hdvd : d ∣ r := (Nat.mem_divisors.mp hd).1
      rw [Nat.cast_div_charZero hdvd]
      have hdR0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
      field_simp [hdR0, hr0.ne']
    _ ≤ ∑ d ∈ Icc 1 r, (d : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hr (Nat.mem_divisors.mp hd).1⟩
      · intro d _ _
        positivity
    _ ≤ 1 + Real.log r := LeanLab.HeathBrown1985.sum_inv_Icc_le_log r

end LeanLab.ExceptionalSet.Supply465
