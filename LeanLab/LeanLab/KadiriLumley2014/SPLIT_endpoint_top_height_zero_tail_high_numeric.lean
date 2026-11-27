/-
Numeric helper for SPLIT_endpoint_top_height_zero_tail_high.lean.  This file proves the
finite arithmetic leaf for the four high rows of Table 2 using Lemma 3.1 of
Kadiri and Lumley 2014 and exact rational kernel checks.

AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.TableCertificates259
import LeanLab.KadiriLumley2014.WeightHigherFactor

namespace LeanLab.KadiriLumley2014.Task92
open Real
open Task64

/-- The higher factor of display 2.24 times its exponential factor is bounded by the
Lemma 3.1 factorial bound. -/
theorem top_factor_le_S10g (m : ℕ) {δ u q j : ℝ} (hδ : 0 < δ) (hu : 0 < u) (hu2 : u ≤ 1 / 2)
    (hq : 0 ≤ q) (hQ : ((1 + δ) ^ (2 * m + 3) - 1) / (δ * (2 * m + 3)) ≤ q ^ 2)
    (hj : 0 < j) (hj2 : j ^ 2 ≤ 2 * m + 1) :
    higherFactor m δ * (Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m) ≤
      q * ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * j) * 3 / (u * δ ^ m) := by
  have hF := higher_factor_bound m hδ
  have hlam : lambdaHigher m δ ≤ q * ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * j) := by
    unfold lambdaHigher
    have h1 : Real.sqrt (((1 + δ) ^ (2 * m + 3) - 1) / (δ * (2 * m + 3))) ≤ q :=
      (Real.sqrt_le_sqrt hQ).trans_eq (Real.sqrt_sq hq)
    have h2 : j ≤ Real.sqrt (2 * m + 1) := Real.le_sqrt_of_sq_le hj2
    apply div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
      (mul_le_mul_of_nonneg_left h2 (by positivity))
  have he1 : Real.exp u ≤ 1 / (1 - u) :=
    Real.exp_bound_div_one_sub_of_interval hu.le (by linarith)
  have he2 : 1 / (1 - u) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hEu : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hE : (Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m) ≤ 3 / (u * δ ^ m) :=
    div_le_div₀ (by norm_num) (by linarith) (by positivity)
      (mul_le_mul_of_nonneg_right hEu (by positivity))
  have hE0 : 0 ≤ (Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m) := by
    have : 0 < Real.exp u - 1 := lt_of_lt_of_le hu hEu
    positivity
  have hB0 : 0 ≤ q * ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * j) := by positivity
  rw [mul_div_assoc]
  calc higherFactor m δ * ((Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m))
      ≤ (q * ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * j)) * (3 / (u * δ ^ m)) :=
        mul_le_mul (hF.trans hlam) hE hE0 hB0
    _ = _ := by ring

/-- Real facts about one Table 2 row. -/
theorem top_row_reals_S10g {r : PrintedRow} (hr : r ∈ tableTwo) :
    (0 : ℝ) < r.deltaQ ∧ (0 : ℝ) < r.uQ ∧ (r.uQ : ℝ) ≤ 1 / 2 := by
  have hs := table_small_steps r hr
  refine ⟨by exact_mod_cast hs.1, ?_, ?_⟩
  · have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  · have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    have h2 : ((0.0001 : ℚ) : ℝ) ≤ 1 / 2 := by norm_num
    linarith

/-- Per row form of the numeric leaf, with the remaining inequality checked exactly. -/
theorem top_numeric_of_row_S10g {r : PrintedRow} (hr : r ∈ tableTwo) (q j : ℚ) (hq : 0 ≤ q)
    (hj : 0 < j)
    (hQ : ((1 + r.deltaQ) ^ (2 * r.m + 3) - 1) / (r.deltaQ * (2 * r.m + 3)) ≤ q ^ 2)
    (hj2 : j ^ 2 ≤ 2 * r.m + 1)
    (hnum : q * ((2 * r.m + 1).factorial : ℚ) / ((r.m.factorial : ℚ) * j) * 3 /
        (r.uQ * r.deltaQ ^ r.m) * (1 / (3000000000000 : ℚ) ^ r.m) ≤ 1 / 100000) :
    higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) / ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (3000000000000 : ℝ) ^ r.m) ≤ 1 / 100000 := by
  obtain ⟨hδ, hu, hu2⟩ := top_row_reals_S10g hr
  have hC := top_factor_le_S10g r.m (q := (q : ℝ)) (j := (j : ℝ)) hδ hu hu2
    (by exact_mod_cast hq) (by exact_mod_cast hQ) (by exact_mod_cast hj) (by exact_mod_cast hj2)
  have hN : ((q : ℝ) * ((2 * r.m + 1).factorial : ℝ) / ((r.m.factorial : ℝ) * j) * 3 /
      ((r.uQ : ℝ) * (r.deltaQ : ℝ) ^ r.m) * (1 / (3000000000000 : ℝ) ^ r.m) ≤ 1 / 100000) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hnum
    push_cast at h ⊢
    linarith
  exact (mul_le_mul_of_nonneg_right hC (by positivity)).trans hN

/-- The numeric leaf at the verified height 3e12 for rows 58, 59, 60 and 150. -/
theorem endpoint_top_numeric_S10_helper {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) / ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (3000000000000 : ℝ) ^ r.m) ≤ 1 / 100000 := by
  have hr' := hr
  simp only [tableTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at hhigh <;> try omega
  all_goals
    exact top_numeric_of_row_S10g hr' (11 / 10) 11 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms top_factor_le_S10g
#print axioms top_numeric_of_row_S10g
#print axioms endpoint_top_numeric_S10_helper

end LeanLab.KadiriLumley2014.Task92
