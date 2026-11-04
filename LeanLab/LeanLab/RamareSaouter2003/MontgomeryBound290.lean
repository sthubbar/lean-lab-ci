import Mathlib

/-!
Negative result for a proof route to P0099 Lemma 5, printed p. 16.
The lab's Montgomery sieve bound in PNTPort/LargeSieve/MontgomeryBT.lean
has right side Q + (y + 2Q^2)/log(Q+1).
At y = 16 this exceeds the sharp right side 2y/log y for every Q at least one.
The comparison concerns the bounds, not the actual prime count.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.MontgomeryBound290

open Real

/-- For every interval length y at least 16, even the fraction in the
available Montgomery bound exceeds 2y/log y, for all allowed Q.
This rules out obtaining the sharp bound by choosing Q alone. -/
theorem fraction_too_large (y : ℝ) (hy : 16 ≤ y) (Q : ℕ) (hQ : 1 ≤ Q) :
    2 * y / Real.log y < (y + 2 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hy0 : 0 < y := by linarith
  have hqp : 0 < (Q : ℝ) + 1 := by positivity
  have hlogq : 0 < Real.log ((Q : ℝ) + 1) := Real.log_pos (by linarith)
  have h16 : 2 < Real.log (16 : ℝ) := by
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith [Real.log_two_gt_d9]
  have hlogy : 2 ≤ Real.log y :=
    h16.le.trans (Real.log_le_log (by norm_num) hy)
  have hlogy0 : 0 < Real.log y := by linarith
  have hratio := Real.log_le_sub_one_of_pos
    (div_pos (sq_pos_of_pos hqp) hy0)
  rw [Real.log_div (by positivity) hy0.ne', Real.log_pow] at hratio
  norm_num only [Nat.cast_ofNat] at hratio
  have hd : (2 * Real.log ((Q : ℝ) + 1) - Real.log y + 1) * y ≤
      ((Q : ℝ) + 1) ^ 2 := by
    apply (le_div_iff₀ hy0).mp
    linarith
  have hqs : (Q : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
  have hqbound : ((Q : ℝ) + 1) ^ 2 ≤ 4 * (Q : ℝ) ^ 2 := by nlinarith
  have hprod : 0 ≤ (Real.log y - 2) * (Q : ℝ) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  apply (div_lt_div_iff₀ hlogy0 hlogq).mpr
  nlinarith

/-- The available Montgomery sieve bound is too large at interval length 16,
for every allowed integer choice of Q. P0099 p. 16 requires the sharper
Montgomery and Vaughan 1973 bound, p. 121, display 1.12. -/
theorem bound_too_large (Q : ℕ) (hQ : 1 ≤ Q) :
    (2 * 16 : ℝ) / Real.log 16 <
      (Q : ℝ) + (16 + 2 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) := by
  have hq : 0 < (Q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hl : 0 < Real.log ((Q : ℝ) + 1) := Real.log_pos (by linarith)
  have hlog : Real.log ((Q : ℝ) + 1) ≤ Q := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : 0 < (Q : ℝ) + 1)
  have hweak : (Q : ℝ) + (16 + 2 * (Q : ℝ) ^ 2) / (Q : ℝ) ≤
      (Q : ℝ) + (16 + 2 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) := by
    have hd := div_le_div_of_nonneg_left
      (show (0 : ℝ) ≤ 16 + 2 * (Q : ℝ) ^ 2 by positivity) hl hlog
    linarith
  have h12 : (12 : ℝ) ≤ (Q : ℝ) + (16 + 2 * (Q : ℝ) ^ 2) / (Q : ℝ) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hq]
    nlinarith [sq_nonneg ((Q : ℝ) - 2)]
  have hsharp : (2 * 16 : ℝ) / Real.log 16 < 12 := by
    rw [div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 16))]
    have he : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [he]
    nlinarith [Real.log_two_gt_d9]
  exact hsharp.trans_le (h12.trans hweak)

end LeanLab.RamareSaouter2003.MontgomeryBound290

#print axioms LeanLab.RamareSaouter2003.MontgomeryBound290.bound_too_large

#print axioms LeanLab.RamareSaouter2003.MontgomeryBound290.fraction_too_large
