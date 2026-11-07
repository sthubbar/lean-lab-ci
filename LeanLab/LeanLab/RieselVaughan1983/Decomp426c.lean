import LeanLab.RieselVaughan1983.Lemma6Theta

/-!
A negative comparison of two error envelopes used in DecompJ206.
The exponential square-root-log envelope is not the fixed power envelope.
This theorem concerns the envelopes, not the actual size of the psi error.
Source: Dusart HDR page 37, Theorem 45 and page 46, Corollary 46.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real

namespace LeanLab.RieselVaughan1983.Task426

/-- The cited Dusart exponential envelope exceeds the desired power envelope
for every L at least one million. It therefore cannot imply the power estimate
by a pointwise comparison of these two envelopes. No paper error is asserted. -/
theorem dusart_exponential_envelope_gt_power (L : ℝ) (hL : 1000000 ≤ L) :
    140 * exp (9 * L / 10) <
      exp L * sqrt (8 / Real.pi) *
        sqrt (sqrt (L / (569693 / 100000 : ℝ))) *
        exp (-sqrt (L / (569693 / 100000 : ℝ))) := by
  let R : ℝ := 569693 / 100000
  let X : ℝ := sqrt (L / R)
  have hL0 : 0 < L := by linarith
  have hR : 0 < R := by norm_num [R]
  have hXs : X ^ 2 = L / R := sq_sqrt (by positivity)
  have hLX : L = R * X ^ 2 := by rw [hXs]; field_simp
  have hX0 : 0 ≤ X := sqrt_nonneg _
  have hX100 : 100 ≤ X := by
    have hs : R * X ^ 2 = L := hLX.symm
    norm_num [R] at hs
    nlinarith
  have hXL : X ≤ L / 100 := by
    have hR1 : 1 ≤ R := by norm_num [R]
    have hs : X ^ 2 ≤ L := by
      rw [hLX]
      exact le_mul_of_one_le_left (sq_nonneg _) hR1
    nlinarith [mul_nonneg hX0 (show 0 ≤ X - 100 by linarith)]
  have hc : 1 ≤ sqrt (8 / Real.pi) := by
    apply (le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_lt_four]
  have hsqrt : 1 ≤ sqrt X := by
    apply (le_sqrt (by norm_num) hX0).mpr
    linarith
  have h140 : (140 : ℝ) < exp 10 := by
    have h := Lemma6Theta.exp_nat_ge 10
    norm_num at h
    linarith
  have hgap : 9 * L / 10 + 10 ≤ L - X := by linarith
  have hmain : 140 * exp (9 * L / 10) < exp (L - X) := by
    calc _ < exp 10 * exp (9 * L / 10) :=
      mul_lt_mul_of_pos_right h140 (exp_pos _)
      _ = exp (9 * L / 10 + 10) := by rw [← exp_add]; congr 1; ring
      _ ≤ exp (L - X) := exp_le_exp.mpr hgap
  have hcoef : 1 ≤ sqrt (8 / Real.pi) * sqrt X := one_le_mul_of_one_le_of_one_le hc hsqrt
  calc 140 * exp (9 * L / 10) < exp (L - X) := hmain
    _ ≤ exp (L - X) * (sqrt (8 / Real.pi) * sqrt X) :=
      le_mul_of_one_le_right (exp_pos _).le hcoef
    _ = exp L * sqrt (8 / Real.pi) * sqrt X * exp (-X) := by
      rw [sub_eq_add_neg, exp_add]
      ring

/-- The page 342 exponential envelope is larger than the first selected
page 358 relative error at log x equal to 18.42. This rejects a direct replacement
of the table row by Theorem 11, not the table row itself. -/
theorem schoenfeld_envelope_gt_first_row :
    (11976 / 10000000 : ℝ) < sqrt (8 / (17 * Real.pi)) *
      sqrt (sqrt ((921 / 50 : ℝ) / (9645908801 / 1000000000 : ℝ))) *
      exp (-sqrt ((921 / 50 : ℝ) / (9645908801 / 1000000000 : ℝ))) := by
  let X : ℝ := sqrt ((921 / 50 : ℝ) / (9645908801 / 1000000000 : ℝ))
  have hX0 : 0 ≤ X := sqrt_nonneg _
  have hXs : X ^ 2 = (921 / 50 : ℝ) / (9645908801 / 1000000000 : ℝ) :=
    sq_sqrt (by norm_num)
  norm_num at hXs
  have hXlo : 1 ≤ X := by nlinarith
  have hXhi : X ≤ 2 := by nlinarith
  have hc : (1 / 4 : ℝ) ≤ sqrt (8 / (17 * Real.pi)) := by
    apply (le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 17 * Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  have hsqrt : 1 ≤ sqrt X := by
    apply (le_sqrt (by norm_num) hX0).mpr
    linarith
  have he2 : exp (2 : ℝ) < 8 := by
    have h := pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos (1 : ℝ)).le
      (by decide : (2 : ℕ) ≠ 0)
    rw [exp_one_pow] at h
    norm_num at h
    linarith
  have heX : exp X < 8 := (exp_le_exp.mpr hXhi).trans_lt he2
  have hdecay : (1 / 8 : ℝ) < exp (-X) := by
    simpa only [one_div, exp_neg] using one_div_lt_one_div_of_lt (exp_pos X) heX
  have hcoef : (1 / 4 : ℝ) ≤ sqrt (8 / (17 * Real.pi)) * sqrt X := by
    calc (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) * sqrt X := by nlinarith
      _ ≤ sqrt (8 / (17 * Real.pi)) * sqrt X :=
        mul_le_mul_of_nonneg_right hc (sqrt_nonneg _)
  change (11976 / 10000000 : ℝ) < sqrt (8 / (17 * Real.pi)) * sqrt X * exp (-X)
  calc (11976 / 10000000 : ℝ) < (1 / 4 : ℝ) * (1 / 8 : ℝ) := by norm_num
    _ < (1 / 4 : ℝ) * exp (-X) := mul_lt_mul_of_pos_left hdecay (by norm_num)
    _ ≤ (sqrt (8 / (17 * Real.pi)) * sqrt X) * exp (-X) :=
      mul_le_mul_of_nonneg_right hcoef (exp_pos _).le

end LeanLab.RieselVaughan1983.Task426
