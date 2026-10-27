/-
Integer detection in display 3.1 on page 9 of P0029.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

/-- Page 9 display 3.1. Divisibility and a strict size bound detect the zero integer. -/
theorem zero_iff_dvd_and_abs107 {q n : ℤ} (hq : 0 < q) :
    n = 0 ↔ q ∣ n ∧ |n| < q := by
  constructor
  · intro hn
    subst n
    simpa using hq
  · rintro ⟨hd, hn⟩
    have ha : |n| < |q| := by simpa only [abs_of_pos hq] using hn
    have hnat : n.natAbs < q.natAbs := by
      exact_mod_cast (show (n.natAbs : ℤ) < (q.natAbs : ℤ) by
        simpa only [Int.natCast_natAbs] using ha)
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hnat

/-- Page 9 display 3.1, written with integer valued indicators. -/
theorem zero_indicator107 {q n : ℤ} (hq : 0 < q) :
    (if n = 0 then (1 : ℤ) else 0) =
      (if q ∣ n then (1 : ℤ) else 0) * (if |n| < q then (1 : ℤ) else 0) := by
  simp only [zero_iff_dvd_and_abs107 hq]
  split_ifs <;> simp_all

/-- Page 9, contour detection display immediately after 3.1. -/
theorem circle_detection107 (k : ℤ) {R : ℝ} (hR : 0 < R) :
    (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (∮ z in C(0, R), z ^ (k - 1)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    have hi : (∮ z in C(0, R), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
      simpa only [sub_zero] using circleIntegral.integral_sub_center_inv 0 hR.ne'
    have hd : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    change (1 / (2 * (Real.pi : ℂ) * Complex.I)) * (∮ z in C(0, R), z ^ (-1 : ℤ)) = 1
    simp only [zpow_neg_one]
    rw [hi, one_div, inv_mul_cancel₀ hd]
  · have he : k - 1 ≠ -1 := by omega
    have hi : (∮ z in C(0, R), z ^ (k - 1)) = 0 := by
      simpa only [sub_zero] using circleIntegral.integral_sub_zpow_of_ne he 0 0 R
    simp [hi, hk]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.zero_iff_dvd_and_abs107
#print axioms LeanLab.BhowmikGrimmelt2026.zero_indicator107

#print axioms LeanLab.BhowmikGrimmelt2026.circle_detection107
