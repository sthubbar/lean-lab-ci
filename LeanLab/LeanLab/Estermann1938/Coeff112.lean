import LeanLab.Estermann1938.Decomp112
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Estermann 1938, P0091, pages 311 and 313, the coefficient in display 33.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Coeff112
open scoped BigOperators
open Decomp112

/-- The logarithmic weight of every natural number is nonnegative, display 33. -/
theorem weight_nonneg (s : ℕ) : 0 ≤ weight s := by
  exact inv_nonneg.mpr (Real.log_natCast_nonneg s)

/-- The logarithmic weights decrease on the range in display 34. -/
theorem weight_antitone {s t : ℕ} (hs : 2 ≤ s) (hst : s ≤ t) : weight t ≤ weight s := by
  have hlog : 0 < Real.log s := Real.log_pos (by exact_mod_cast (by omega : 1 < s))
  have hmono : Real.log s ≤ Real.log t :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < s)) (by exact_mod_cast hst)
  simpa only [weight, one_div] using one_div_le_one_div_of_le hlog hmono

/-- The coefficient in display 33 is nonnegative, page 311. -/
theorem b_nonneg (n m : ℕ) : 0 ≤ b n m := by
  unfold b
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (weight_nonneg p.1) (weight_nonneg p.2)

/-- Displays 33 to 36 reindexed by s when 4 ≤ m ≤ n. -/
theorem b_eq_sum {n m : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n) :
    b n m = ∑ s ∈ Finset.Icc 2 (m - 2), weight s * weight (m - s) := by
  classical
  unfold b
  apply Finset.sum_bij (fun p _ => p.1)
  · intro p hp
    obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨⟨hs, hsn⟩, ⟨ht, htn⟩⟩ :=
      (Finset.mem_product.mp hp).imp Finset.mem_Icc.mp Finset.mem_Icc.mp
    exact Finset.mem_Icc.mpr ⟨hs, by omega⟩
  · intro p hp q hq heq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext heq
    omega
  · intro s hs
    obtain ⟨hs, hsm⟩ := Finset.mem_Icc.mp hs
    refine ⟨(s, m - s), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hs, by omega⟩, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    · dsimp
      omega
  · intro p hp
    have heq := (Finset.mem_filter.mp hp).2
    have ht : p.2 = m - p.1 := by omega
    rw [ht]

/-- Page 313, the inequality immediately before display 48. -/
theorem b_lower {n m : ℕ} (hn : 2 ≤ n) (hmn : m ≤ n) :
    ((m : ℝ) - 3) / Real.log n ^ 2 ≤ b n m := by
  by_cases hm : 4 ≤ m
  · rw [b_eq_sum hm hmn]
    have hc : ((Finset.Icc 2 (m - 2)).card : ℝ) = (m : ℝ) - 3 := by
      rw [Nat.card_Icc]
      have he : m - 2 + 1 - 2 = m - 3 := by omega
      rw [he, Nat.cast_sub (by omega : 3 ≤ m)]
      norm_num
    calc
      ((m : ℝ) - 3) / Real.log n ^ 2 =
          ∑ s ∈ Finset.Icc 2 (m - 2), weight n * weight n := by
        rw [Finset.sum_const, nsmul_eq_mul, hc]
        unfold weight
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        obtain ⟨hs, hsm⟩ := Finset.mem_Icc.mp hs
        apply mul_le_mul (weight_antitone hs (by omega : s ≤ n))
          (weight_antitone (by omega : 2 ≤ m - s) (by omega : m - s ≤ n))
          (weight_nonneg n) (weight_nonneg s)
  · have hnum : (m : ℝ) - 3 ≤ 0 := by exact_mod_cast (show (m : ℤ) - 3 ≤ 0 by omega)
    exact (div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)).trans (b_nonneg n m)

/-- Reciprocal logs are at most two on the range in display 34. -/
theorem weight_le_two {s : ℕ} (hs : 2 ≤ s) : weight s ≤ 2 := by
  apply (weight_antitone (by decide : 2 ≤ 2) hs).trans
  unfold weight
  apply (inv_le_comm₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num : (0 : ℝ) < 2)).mpr
  norm_num
  nlinarith [Real.log_two_gt_d9]

/-- Reciprocal logs are at most one once the index is at least three. -/
theorem weight_le_one {s : ℕ} (hs : 3 ≤ s) : weight s ≤ 1 := by
  apply (weight_antitone (by decide : 2 ≤ 3) hs).trans
  unfold weight
  apply (inv_le_comm₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3)) (by norm_num : (0 : ℝ) < 1)).mpr
  norm_num
  nlinarith [Real.log_three_gt_d9]

/-- Display 33 has only the pair 2,2 at total frequency four. -/
theorem b_four {n : ℕ} (hn : 2 ≤ n) : b n 4 = weight 2 * weight 2 := by
  classical
  have hf : ((Finset.Icc 2 n).product (Finset.Icc 2 n)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 = 4) = {(2, 2)} := by
    ext p
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨hs, hsn⟩, ⟨ht, htn⟩⟩, heq⟩
      exact Prod.ext (by omega) (by omega)
    · intro hp
      subst p
      exact ⟨⟨⟨le_rfl, hn⟩, ⟨le_rfl, hn⟩⟩, rfl⟩
  unfold b
  rw [hf]
  simp

/-- Displays 33 to 36: projection to s injects the ordered pairs into 2 through n. -/
theorem pair_card_le (n m : ℕ) :
    (((Finset.Icc 2 n).product (Finset.Icc 2 n)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 = m)).card ≤ n := by
  classical
  apply le_trans (Finset.card_le_card_of_injOn Prod.fst ?_ ?_)
      (show (Finset.Icc 2 n).card ≤ n by rw [Nat.card_Icc]; omega)
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hpq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext hpq
    omega

/-- Page 311, after display 37: b is at most twice the cutoff. -/
theorem b_upper (n m : ℕ) : b n m ≤ 2 * n := by
  classical
  by_cases hn : 2 ≤ n
  · by_cases hm : m = 4
    · subst m
      rw [b_four hn]
      have hw := weight_le_two (by decide : 2 ≤ 2)
      have hp := weight_nonneg 2
      have hmul := mul_le_mul hw hw hp (by norm_num : (0 : ℝ) ≤ 2)
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    · let P := ((Finset.Icc 2 n).product (Finset.Icc 2 n)).filter
          (fun p : ℕ × ℕ => p.1 + p.2 = m)
      have hterm : ∀ p ∈ P, weight p.1 * weight p.2 ≤ 2 := by
        intro p hp
        obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
        obtain ⟨⟨hs, hsn⟩, ⟨ht, htn⟩⟩ :=
          (Finset.mem_product.mp hp).imp Finset.mem_Icc.mp Finset.mem_Icc.mp
        have hh : 3 ≤ p.1 ∨ 3 ≤ p.2 := by omega
        rcases hh with hh | hh
        · have hh' := mul_le_mul (weight_le_one hh) (weight_le_two ht)
            (weight_nonneg p.2) (by norm_num : (0 : ℝ) ≤ 1)
          simpa using hh'
        · have hh' := mul_le_mul (weight_le_two hs) (weight_le_one hh)
            (weight_nonneg p.2) (by norm_num : (0 : ℝ) ≤ 2)
          simpa using hh'
      calc
        b n m = ∑ p ∈ P, weight p.1 * weight p.2 := rfl
        _ ≤ ∑ _p ∈ P, (2 : ℝ) := Finset.sum_le_sum hterm
        _ = (P.card : ℝ) * 2 := by simp
        _ ≤ 2 * n := by
          have hc : (P.card : ℝ) ≤ n := by exact_mod_cast pair_card_le n m
          linarith
  · have hi : Finset.Icc 2 n = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      have hh := Finset.mem_Icc.mp hs
      omega
    simp [b, hi]

#print axioms weight_le_two
#print axioms weight_le_one
#print axioms b_four
#print axioms pair_card_le
#print axioms b_upper

#print axioms weight_nonneg
#print axioms weight_antitone
#print axioms b_nonneg
#print axioms b_eq_sum
#print axioms b_lower

end LeanLab.Estermann1938.Coeff112
