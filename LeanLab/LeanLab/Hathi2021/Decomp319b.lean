/-
P0101 Hu 2019, page 194, Lemma 2.3.
Method limit for the h = 1 bound in arXiv math/0201299, page 30, displays 43 and 44.
This is a limit of that method. It does not negate the exceptional set estimate.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.PairLinnik
import LeanLab.PlattTrudgian2014.H1Barrier
import LeanLab.PlattTrudgian2014.H2Barrier125

namespace LeanLab.Hathi2021.Decomp319b

/-- Helper for P0101 page 194, Lemma 2.3.
The h = 1 moment rate at the printed lambda is below three quarters for every
nonnegative parameter. The paper requires an exponent above three quarters.
The rate formula is arXiv math/0201299 page 30, displays 43 and 44 at h = 1. -/
theorem h1_moment_rate_insufficient {t : ℝ} (ht : 0 ≤ t) :
    t * (PairLinnik.lam : ℝ) - Real.log (Real.cosh t) <
      (3 / 4 : ℝ) * Real.log 2 := by
  have hh := LeanLab.PlattTrudgian2014.log_cosh_tangent
    (r := 17 / 4) (by norm_num) t
  rw [Real.cosh_log (by norm_num : (0 : ℝ) < 17 / 4)] at hh
  norm_num at hh
  have hu : Real.log (17 / 4 : ℝ) ≤ 2 * Real.log 2 + 1 / 16 := by
    rw [show (17 / 4 : ℝ) = 2 ^ 2 * (17 / 16) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 17 / 16)
    norm_num at h ⊢
    linarith
  have hl : Real.log (305 / 136 : ℝ) ≥ Real.log 2 + 33 / 305 := by
    rw [show (305 / 136 : ℝ) = 2 * (305 / 272) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 305 / 272)
    norm_num at h ⊢
    linarith
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  norm_num [PairLinnik.lam]
  nlinarith

#print axioms h1_moment_rate_insufficient

/-- Helper for P0101 page 194, Lemma 2.3.
The h = 2 rate from arXiv math/0201299 page 30 displays 43 and 44 is also
strictly below three quarters at every nonnegative parameter. -/
theorem h2_moment_rate_insufficient {t : ℝ} (ht : 0 ≤ t) :
    t * (PairLinnik.lam : ℝ) -
      Real.log (LeanLab.PlattTrudgian2014.twoBlockFactor t) / 2 <
        (3 / 4 : ℝ) * Real.log 2 := by
  have hh := LeanLab.PlattTrudgian2014.log_twoBlockFactor_tangent125
    (r := 4) (by norm_num) t
  rw [LeanLab.PlattTrudgian2014.twoBlockFactor_log (by norm_num : (0 : ℝ) < 4)] at hh
  norm_num at hh
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4] at hh
  have hl : Real.log (35 / 8 : ℝ) ≥ 2 * Real.log 2 + 3 / 35 := by
    rw [show (35 / 8 : ℝ) = 4 * (35 / 32) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), h4]
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 35 / 32)
    norm_num at h ⊢
    linarith
  have htwo := Real.log_two_lt_d9
  norm_num [PairLinnik.lam]
  nlinarith

#print axioms h2_moment_rate_insufficient

end LeanLab.Hathi2021.Decomp319b
