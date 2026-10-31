import LeanLab.RieselVaughan1983.Lemma5Final
import LeanLab.RieselVaughan1983.SieveWeights93

/-! Decomposition of Lemma 5 at the first row used by the lab.
AI wrote the Lean code. Binary Goldbach is OPEN.
The assembly has no local sorry. Its three analytic leaves remain unproved.
The sieve leaf uses Montgomery and Vaughan 1973 Corollary 1.
The weighted leaf uses Lemma 4 and the printed constant brackets.
-/

namespace LeanLab.RieselVaughan1983.Decomp93
open Real Finset
noncomputable section
open SieveWeights93

/-- The explicit lower polynomial from pages 47 and 54 at lambda = 3/2. -/
def lowerPolynomial (x : ℝ) : ℝ :=
  log x ^ 2 + (8463433 / 1000000) * log x - 9260623 / 1000000 -
    (9310077 / 1000) * x ^ (-(1 / 6 : ℝ)) -
    (2950889 / 100000) * x ^ (-(1 / 2 : ℝ))

/-- LEAF. Page 54 application of Montgomery and Vaughan 1973 Corollary 1,
followed by equations 3.12 and 3.18, for an even positive shift. The published
source is The large sieve, Mathematika 20, 1973, pages 119 to 134. -/
theorem mv_sieve (x : ℝ) (hx : exp 24 ≤ x) (h : ℕ) (hh : 0 < h) (he : Even h) :
    (#((Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime)) : ℝ) ≤
      x / Sn h (sqrt (2 / 3 * x)) + 2 * sqrt x := by
  sorry

/-- LEAF. Page 51 equation 3.13, with the product written as 1 divided by wt n. -/
theorem sum_comparison (n : ℕ) (hn : 0 < n) (he : Even n) (z : ℝ) (hz : 1 ≤ z) :
    Lemma3.S2 z / wt n ≤ Sn n z := by
  sorry

/-- Page 54 equation 3.19 for the interval 0 < p ≤ x.
CONDITIONAL ON mv_sieve and sum_comparison. -/
theorem sieve319 (x : ℝ) (hx : exp 24 ≤ x) (h : ℕ) (hh : 0 < h) :
    (#((Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime)) : ℝ) ≤
      (x / Lemma3.S2 (sqrt (2 / 3 * x)) + 2 * sqrt x) * wt h := by
  have hx25 : (25 : ℝ) ≤ x := by linarith [add_one_le_exp (24 : ℝ)]
  have hx0 : 0 < x := by linarith
  have hz : 1 ≤ sqrt (2 / 3 * x) := one_le_sqrt.mpr (by linarith)
  have hs := S2_pos _ hz
  have hw := one_le_wt h
  have hwp : 0 < wt h := by linarith
  have hroot : 1 ≤ sqrt x := one_le_sqrt.mpr (by linarith)
  by_cases he : Even h
  · have hsn := Sn_pos h he _ hz
    have hcomp := (div_le_iff₀ hwp).mp (sum_comparison h hh he _ hz)
    have hdiv : x / Sn h (sqrt (2 / 3 * x)) ≤
        x / Lemma3.S2 (sqrt (2 / 3 * x)) * wt h := by
      apply (div_le_iff₀ hsn).mpr
      calc x = x / Lemma3.S2 (sqrt (2 / 3 * x)) * Lemma3.S2 (sqrt (2 / 3 * x)) :=
          (div_mul_cancel₀ x hs.ne').symm
        _ ≤ x / Lemma3.S2 (sqrt (2 / 3 * x)) * (Sn h (sqrt (2 / 3 * x)) * wt h) :=
          mul_le_mul_of_nonneg_left hcomp (div_nonneg hx0.le hs.le)
        _ = _ := by ring
    have hrootw : 2 * sqrt x ≤ 2 * sqrt x * wt h :=
      le_mul_of_one_le_right (by positivity) hw
    calc _ ≤ x / Sn h (sqrt (2 / 3 * x)) + 2 * sqrt x := mv_sieve x hx h hh he
      _ ≤ _ := by nlinarith
  · have hcount := odd_shift_count x h he
    have hmain : 0 ≤ x / Lemma3.S2 (sqrt (2 / 3 * x)) := by positivity
    have hwmain : x / Lemma3.S2 (sqrt (2 / 3 * x)) + 2 * sqrt x ≤
        (x / Lemma3.S2 (sqrt (2 / 3 * x)) + 2 * sqrt x) * wt h :=
      le_mul_of_one_le_right (by positivity) hw
    linarith

/-- LEAF. Page 54 application of Lemma 4 with lambda = 3/2, using the lower
A6 and A7 brackets and the upper A8 and A9 brackets in equations 2.20 to 2.22. -/
theorem weighted_lower (x : ℝ) (hx : exp 24 ≤ x) :
    lowerPolynomial x < 8 * Ctw * Lemma3.S2 (sqrt (2 / 3 * x)) := by
  sorry

/-- LEAF. Page 55 bound F x > B at the row L = 24, B = 0.97.
This is stated after multiplication by the positive log x. -/
theorem row24 (x : ℝ) (hx : exp 24 ≤ x) :
    log x * (97 / 100 + log x) < lowerPolynomial x := by

  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 24) hx
  have hl : 24 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have he4 : (5459 / 100 : ℝ) ≤ exp 4 := by
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
      exp_one_gt_d9.le 4
    norm_num at he
    linarith
  have he12 : (100000 : ℝ) ≤ exp 12 := by
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
      exp_one_gt_d9.le 12
    norm_num at he
    linarith
  have hr6 : x ^ (-(1 / 6 : ℝ)) ≤ 100 / 5459 := by
    rw [rpow_def_of_pos hx0, show log x * -(1 / 6 : ℝ) = -(log x / 6) by ring,
      exp_neg]
    have he : (5459 / 100 : ℝ) ≤ exp (log x / 6) :=
      he4.trans (exp_le_exp.mpr (by linarith))
    apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
    nlinarith
  have hr2 : x ^ (-(1 / 2 : ℝ)) ≤ 1 / 100000 := by
    rw [rpow_def_of_pos hx0, show log x * -(1 / 2 : ℝ) = -(log x / 2) by ring,
      exp_neg]
    have he : (100000 : ℝ) ≤ exp (log x / 2) :=
      he12.trans (exp_le_exp.mpr (by linarith))
    apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
    nlinarith
  unfold lowerPolynomial
  nlinarith

/-- LEAF. Page 55 equation 3.21 and its displayed equivalent at L = 24, A = 0. -/
theorem comparison24 (x : ℝ) (hx : exp 24 ≤ x) :
    8 * Ctw * x / (log x * (97 / 100 + log x)) + 102 * sqrt x <
      8 * Ctw * x / (log x * (0 + log x)) := by
  exact key_102 24 0 (97 / 100) x eq321_24 (by norm_num) le_rfl (by norm_num) hx

/-- The cited Prop exactly as the lab states it at the first table row.
CONDITIONAL ON the unresolved sieve319 and weighted_lower leaves. -/
theorem lemma5Used24_decomposed : Lemma5Used 24 0 := by
  intro x hx h hh
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 24) hx
  have hl : 24 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hl0 : 0 < log x := by linarith
  have hd : 0 < log x * (97 / 100 + log x) := by positivity
  have hC := Ctw_pos
  have hw := wt_nonneg h
  have hlow := (row24 x hx).trans (weighted_lower x hx)
  have hs : 0 < Lemma3.S2 (sqrt (2 / 3 * x)) := by nlinarith
  have hdiv : x / Lemma3.S2 (sqrt (2 / 3 * x)) ≤
      8 * Ctw * x / (log x * (97 / 100 + log x)) := by
    apply (div_le_div_iff₀ hs hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlow.le hx0.le]
  have hbound := sieve319 x hx h hh
  have hcmp := comparison24 x hx
  have hroot := sqrt_nonneg x
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ hw
  linarith

end
end LeanLab.RieselVaughan1983.Decomp93

#print axioms LeanLab.RieselVaughan1983.Decomp93.mv_sieve
#print axioms LeanLab.RieselVaughan1983.Decomp93.sum_comparison
#print axioms LeanLab.RieselVaughan1983.Decomp93.sieve319
#print axioms LeanLab.RieselVaughan1983.Decomp93.weighted_lower
#print axioms LeanLab.RieselVaughan1983.Decomp93.row24
#print axioms LeanLab.RieselVaughan1983.Decomp93.comparison24
#print axioms LeanLab.RieselVaughan1983.Decomp93.lemma5Used24_decomposed
