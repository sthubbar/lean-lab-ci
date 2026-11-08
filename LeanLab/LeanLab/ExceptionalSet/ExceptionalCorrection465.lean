import LeanLab.ExceptionalSet.GammaTwoMean465

/-!
P0082 page364 case ii d, the elementary exceptional correction bounds.
No zero free region or major arc expansion is supplied by these statements.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Supply465
open Real Finset

/-- P0082 page364 case ii d and page359 display13. The finite exceptional
correction sum is at most m to beta when P is at least two and beta at most
one. This bound does not assume an exceptional character exists. -/
theorem exceptional_correction_sum_le (P m : ℕ) (hP : 2 ≤ P) (hm : 1 ≤ m)
    (β : ℝ) (hβ : β ≤ 1) :
    ∑ k ∈ Ioo P (m - P), ((k : ℝ) * (m - k : ℕ)) ^ (β - 1) ≤ (m : ℝ) ^ β := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hterm (k : ℕ) (hk : k ∈ Ioo P (m - P)) :
      ((k : ℝ) * (m - k : ℕ)) ^ (β - 1) ≤ (m : ℝ) ^ (β - 1) := by
    have hkI := mem_Ioo.mp hk
    have hk2 : 2 ≤ k := by omega
    have hkM : k ≤ m := by omega
    have hmk2 : 2 ≤ m - k := by omega
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hmkR : (2 : ℝ) ≤ (m - k : ℕ) := by exact_mod_cast hmk2
    have hsum : (k : ℝ) + (m - k : ℕ) = m := by exact_mod_cast (Nat.add_sub_of_le hkM)
    have hprod : (m : ℝ) ≤ (k : ℝ) * (m - k : ℕ) := by nlinarith
    exact Real.rpow_le_rpow_of_nonpos hm0 hprod (by linarith)
  have hcard : ((Ioo P (m - P)).card : ℝ) ≤ m := by
    have hs : Ioo P (m - P) ⊆ range m := by intro k hk; have := (mem_Ioo.mp hk).2; exact mem_range.mpr (by omega)
    exact_mod_cast (card_le_card hs).trans (by simp)
  calc
    _ ≤ ∑ _k ∈ Ioo P (m - P), (m : ℝ) ^ (β - 1) := sum_le_sum hterm
    _ = ((Ioo P (m - P)).card : ℝ) * (m : ℝ) ^ (β - 1) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * (m : ℝ) ^ (β - 1) := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hm0.le _)
    _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (β - 1) := by rw [Real.rpow_one]
    _ = (m : ℝ) ^ (1 + (β - 1)) := (Real.rpow_add hm0 1 (β - 1)).symm
    _ = (m : ℝ) ^ β := by congr 1; ring

/-- P0082 page364 case ii d, an explicit elementary cancellation factor.
For t between zero and one, one minus exp of minus t is at least half t. -/
theorem half_le_one_sub_exp_neg (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have he := Real.add_one_le_exp t
  have hexp : 0 < Real.exp t := Real.exp_pos _
  have htpos : 0 < 1 + t := by linarith
  have hinv : 1 / Real.exp t ≤ 1 / (1 + t) := one_div_le_one_div_of_le htpos (by linarith)
  rw [Real.exp_neg, ← one_div] 
  have hdiv : t / 2 ≤ t / (1 + t) := by
    apply div_le_div_of_nonneg_left ht htpos
    linarith
  have hid : 1 - 1 / (1 + t) = t / (1 + t) := by field_simp; ring
  linarith

/-- P0082 page364 case ii d. When the cancellation parameter is at most
one, m minus m to beta has the explicit lower bound used after display20. -/
theorem power_gap_lower (m β : ℝ) (hm : 1 ≤ m) (hβ : β ≤ 1)
    (ht : (1 - β) * Real.log m ≤ 1) :
    m * (1 - β) * Real.log m / 2 ≤ m - m ^ β := by
  have hm0 : 0 < m := by linarith
  have ht0 : 0 ≤ (1 - β) * Real.log m := mul_nonneg (by linarith) (Real.log_nonneg hm)
  have h := mul_le_mul_of_nonneg_left (half_le_one_sub_exp_neg ((1 - β) * Real.log m) ht0 ht) hm0.le
  have hid : m * Real.exp (-((1 - β) * Real.log m)) = m ^ β := by
    rw [← Real.exp_log hm0, ← Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos _)]
    rw [Real.log_exp]
    congr 1
    ring
  nlinarith

/-- P0082 page364 case ii d. The elementary exponential cancellation has
a uniform lower bound with its parameter truncated at one. -/
theorem min_half_le_one_sub_exp_neg (t : ℝ) (ht : 0 ≤ t) :
    min t 1 / 2 ≤ 1 - Real.exp (-t) := by
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1]
    exact half_le_one_sub_exp_neg t ht ht1
  · rw [min_eq_right (le_of_not_ge ht1)]
    have h := half_le_one_sub_exp_neg 1 (by norm_num) (by norm_num)
    have he : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    linarith

/-- P0082 page364 case ii d. The power gap has a uniform explicit lower
bound without a smallness assumption on its cancellation parameter. -/
theorem power_gap_min_lower (m β : ℝ) (hm : 1 ≤ m) (hβ : β ≤ 1) :
    m * min ((1 - β) * Real.log m) 1 / 2 ≤ m - m ^ β := by
  have hm0 : 0 < m := by linarith
  have ht0 : 0 ≤ (1 - β) * Real.log m := mul_nonneg (by linarith) (Real.log_nonneg hm)
  have h := mul_le_mul_of_nonneg_left (min_half_le_one_sub_exp_neg ((1 - β) * Real.log m) ht0) hm0.le
  have hid : m * Real.exp (-((1 - β) * Real.log m)) = m ^ β := by
    rw [← Real.exp_log hm0, ← Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  nlinarith

/-- P0082 page363 case ii b after display21. A correction of relative
size at most two thirds leaves at least one third of the main term. -/
theorem linear_correction_lower (m S J T : ℝ) (hm : 0 ≤ m) (hS : 0 ≤ S)
    (hJ : |J| ≤ m) (hT : |T| ≤ (2 / 3) * S) :
    m * S / 3 ≤ m * S + J * T := by
  have ha : |J * T| ≤ m * ((2 / 3) * S) := by
    rw [abs_mul]
    exact mul_le_mul hJ hT (abs_nonneg _) hm
  have hlow := (abs_le.mp ha).1
  nlinarith

/-- P0082 page364 case ii d. Bounding the correction sum by m to beta
and its singular factor in absolute value by S leaves the explicit power
gap. CONDITIONAL ON those two stated correction bounds. -/
theorem linear_correction_gap_lower (m β S J T : ℝ) (hm : 1 ≤ m) (hβ : β ≤ 1)
    (hS : 0 ≤ S) (hJ0 : 0 ≤ J) (hJ : J ≤ m ^ β) (hT : |T| ≤ S) :
    S * m * min ((1 - β) * Real.log m) 1 / 2 ≤ m * S + J * T := by
  have htlow := (abs_le.mp hT).1
  have hjmul := mul_le_mul_of_nonneg_right hJ hS
  have hJlow := mul_le_mul_of_nonneg_left htlow hJ0
  have hgap := mul_le_mul_of_nonneg_left (power_gap_min_lower m β hm hβ) hS
  nlinarith

end LeanLab.ExceptionalSet.Supply465
