/-
P0093 page 160, the last display before equation 6.2 on page 161.
Arithmetic for the printed extension of the principal contour integral.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Linnik1951

/-- P0093 page 160, last display. With tau equal to N to the one seventh
and q at most N to the one tenth, q tau squared is at most square root N,
and square root N is absorbed by the displayed reciprocal arc error.
This supplies only the numerical step, not the contour norm bound. -/
theorem principal_contour_extension_scale549 (N q : ℕ) (hN : 3 ≤ N) (hq : 1 ≤ q)
    (hQ : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 ≤ Real.sqrt N ∧
      Real.sqrt N ≤ (N : ℝ) * Real.log N ^ 13 /
        ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNp : (0 : ℝ) < N := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hR : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (17 / 70 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right hQ (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hR0 : 0 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hsquare : ((N : ℝ) ^ (17 / 70 : ℝ)) ^ 2 = (N : ℝ) ^ (17 / 35 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    norm_num
  have hRsq : ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 ≤ Real.sqrt N := by
    calc
      _ ≤ ((N : ℝ) ^ (17 / 70 : ℝ)) ^ 2 := pow_le_pow_left₀ hR0 hR 2
      _ = (N : ℝ) ^ (17 / 35 : ℝ) := hsquare
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = _ := (Real.sqrt_eq_rpow _).symm
  have hRroot : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ Real.sqrt N := by
    calc
      _ ≤ (N : ℝ) ^ (17 / 70 : ℝ) := hR
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = _ := (Real.sqrt_eq_rpow _).symm
  have hlog : 1 ≤ Real.log N :=
    (Real.le_log_iff_exp_le hNp).mpr (Real.exp_one_lt_three.le.trans hNr)
  have hlog13 : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  refine ⟨hRsq, (le_div_iff₀ (by positivity)).mpr ?_⟩
  calc
    _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_left hRroot (by positivity)
    _ = N := Real.mul_self_sqrt hNp.le
    _ ≤ (N : ℝ) * Real.log N ^ 13 := le_mul_of_one_le_right hNp.le hlog13

end LeanLab.Linnik1951
