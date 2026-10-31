/-
AI wrote this Lean code for CODEX task58.
Centered polynomial enclosures for the two remaining nested integrals.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Series
import LeanLab.ChenPrimeExceptional.Task58Primitive

open Real Finset

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- The logarithm polynomial also has a symmetric remainder bound. -/
theorem logPoly_error_abs {q a : ℝ} (hqa : |q| ≤ a) (ha : a < 1) (n : ℕ) :
    |log (1 + q) - logPoly n q| ≤ a ^ (n + 1) / (1 - a) := by
  have hq1 : |(-q)| < 1 := by rw [abs_neg]; exact hqa.trans_lt ha
  have h := abs_log_sub_add_sum_range_le hq1 n
  rw [abs_neg, sub_neg_eq_add] at h
  have he : |log (1 + q) - logPoly n q| =
      |(∑ i ∈ range n, (-q) ^ (i + 1) / (i + 1)) + log (1 + q)| := by
    congr 1
    unfold logPoly
    ring
  rw [he]
  exact h.trans (div_le_div₀ (pow_nonneg ((abs_nonneg q).trans hqa) _)
    (pow_le_pow_left₀ (abs_nonneg q) hqa _) (by linarith) (by linarith))

/-- Eight atanh terms give a rational approximation to log of three halves. -/
def logThreeHalvesApprox : ℝ := 2 * ∑ i ∈ range 8,
  (1 / 5 : ℝ) ^ (2 * i + 1) / (2 * i + 1)

theorem logThreeHalves_error :
    |log (3 / 2 : ℝ) - logThreeHalvesApprox| ≤ (3 / 1000000000000 : ℝ) := by
  have h := sum_range_sub_log_div_le (x := (1 / 5 : ℝ)) (by norm_num) 8
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)] at h
  have he : (1 + (1 / 5 : ℝ)) / (1 - 1 / 5) = 3 / 2 := by norm_num
  rw [he] at h
  calc
    _ = |2 * (1 / 2 * log (3 / 2 : ℝ) -
        ∑ i ∈ range 8, (1 / 5 : ℝ) ^ (2 * i + 1) / (2 * i + 1))| := by
      congr 1
      unfold logThreeHalvesApprox
      ring
    _ = 2 * |1 / 2 * log (3 / 2 : ℝ) -
        ∑ i ∈ range 8, (1 / 5 : ℝ) ^ (2 * i + 1) / (2 * i + 1)| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * ((1 / 5 : ℝ) ^ (2 * 8 + 1) / (1 - (1 / 5 : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ _ := by norm_num

/-- The centered logarithm polynomial on the full inner integration interval. -/
def centeredLogPoly (w : ℝ) : ℝ := logThreeHalvesApprox + logPoly 20 ((2 * w - 1) / 3)

/-- The centered reciprocal polynomial on the full inner integration interval. -/
def centeredReciprocalPoly (w : ℝ) : ℝ := (2 / 5) * geomPoly 16 (-(2 * w - 1) / 5)

/-- Their product approximates the inner kernel. -/
def centeredInnerPoly (w : ℝ) : ℝ := centeredLogPoly w * centeredReciprocalPoly w

theorem centeredLogPoly_error {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |log (1 + w) - centeredLogPoly w| ≤ (2 / 10000000000 : ℝ) := by
  have harg : |(2 * w - 1) / 3| ≤ (1 / 3 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hw.1, hw.2]
  have hpoly := logPoly_error_abs harg (by norm_num : (1 / 3 : ℝ) < 1) 20
  have hlog := logThreeHalves_error
  have he : log (1 + w) - centeredLogPoly w =
      (log (3 / 2 : ℝ) - logThreeHalvesApprox) +
      (log (1 + (2 * w - 1) / 3) - logPoly 20 ((2 * w - 1) / 3)) := by
    have hfactor : (1 + w : ℝ) = (3 / 2) * (1 + (2 * w - 1) / 3) := by ring
    rw [hfactor, log_mul (by norm_num) (by linarith [hw.1] : (1 : ℝ) + (2 * w - 1) / 3 ≠ 0)]
    unfold centeredLogPoly
    ring
  rw [he]
  have htri := abs_add_le (log (3 / 2 : ℝ) - logThreeHalvesApprox)
    (log (1 + (2 * w - 1) / 3) - logPoly 20 ((2 * w - 1) / 3))
  have hnum : (1 / 3 : ℝ) ^ (20 + 1) / (1 - 1 / 3) ≤ (15 / 100000000000 : ℝ) := by norm_num
  linarith

theorem centeredReciprocalPoly_error {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |centeredReciprocalPoly w - 1 / (2 + w)| ≤ (4 / 1000000000000 : ℝ) := by
  have harg : |-(2 * w - 1) / 5| ≤ (1 / 5 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hw.1, hw.2]
  have hpoly := geomPoly_error harg (by norm_num : (1 / 5 : ℝ) < 1) 16
  have hr : 1 / (2 + w) = (2 / 5 : ℝ) * (1 / (1 - (-(2 * w - 1) / 5))) := by
    rw [mul_one_div]
    apply (div_eq_div_iff (by linarith [hw.1]) (by linarith [hw.1])).mpr
    ring
  rw [hr]
  unfold centeredReciprocalPoly
  rw [← mul_sub, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)]
  refine (mul_le_mul_of_nonneg_left hpoly (by norm_num : (0 : ℝ) ≤ 2 / 5)).trans ?_
  norm_num

theorem centeredLogPoly_abs_le_one {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |centeredLogPoly w| ≤ 1 := by
  have h := centeredLogPoly_error hw
  rw [abs_le] at h
  have h0 := log_nonneg (show 1 ≤ 1 + w by linarith [hw.1])
  have h1 := log_le_log (show (0 : ℝ) < 1 + w by linarith [hw.1])
    (show 1 + w ≤ 2 by linarith [hw.2])
  have h2 := log_two_lt_d9
  apply abs_le.mpr
  constructor <;> linarith

theorem centeredInnerPoly_error {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |centeredInnerPoly w - inner (2 + w)| ≤ (1 / 1000000000 : ℝ) := by
  have hL := centeredLogPoly_abs_le_one hw
  have hR := centeredReciprocalPoly_error hw
  have hlog := centeredLogPoly_error hw
  have hlog' : |centeredLogPoly w - log (1 + w)| ≤ (2 / 10000000000 : ℝ) := by
    rw [abs_sub_comm]
    exact hlog
  have hr : |1 / (2 + w)| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_pos (one_div_pos.mpr (by linarith [hw.1]) : (0 : ℝ) < 1 / (2 + w))]
    rw [div_le_iff₀ (by linarith [hw.1])]
    linarith [hw.1]
  have he : centeredInnerPoly w - inner (2 + w) =
      centeredLogPoly w * (centeredReciprocalPoly w - 1 / (2 + w)) +
      (centeredLogPoly w - log (1 + w)) * (1 / (2 + w)) := by
    unfold centeredInnerPoly inner
    have harg : (2 + w : ℝ) - 1 = 1 + w := by ring
    rw [harg]
    ring
  rw [he]
  calc
    _ ≤ |centeredLogPoly w * (centeredReciprocalPoly w - 1 / (2 + w))| +
        |(centeredLogPoly w - log (1 + w)) * (1 / (2 + w))| := abs_add_le _ _
    _ = |centeredLogPoly w| * |centeredReciprocalPoly w - 1 / (2 + w)| +
        |centeredLogPoly w - log (1 + w)| * |1 / (2 + w)| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (4 / 1000000000000 : ℝ) + (2 / 10000000000 : ℝ) * (1 / 2) :=
      add_le_add (mul_le_mul hL hR (abs_nonneg _) (by norm_num))
        (mul_le_mul hlog' hr (abs_nonneg _) (by norm_num))
    _ ≤ _ := by norm_num

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.logPoly_error_abs
#print axioms LeanLab.ChenPrimeExceptional.Task58.logThreeHalves_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.centeredLogPoly_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.centeredReciprocalPoly_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.centeredLogPoly_abs_le_one
#print axioms LeanLab.ChenPrimeExceptional.Task58.centeredInnerPoly_error
