/- AI wrote this Lean code, ROUTE BURST S63 burst-20261122. Goldbach is open.
Cited theta inputs in their published, corrected form, from which ThetaInputs224
derives the three BKLNW Table 15 rows it uses.
Sources: Buthe 2018, Math. Comp. 87, arXiv 1511.02032, Theorem 2 p. 2;
Broadbent, Kadiri, Lumley, Ng, Wilk et al. 2026, arXiv 2608.01498v1, Table 2 p. 39,
which recomputes the BKLNW table after the Buthe 2016 E2 erratum.
The elementary comparisons below are proved; the three LEAF inputs are cited. -/
import Mathlib

namespace LeanLab.BS2022GRH.ThetaLeavesS63
open Real

/-- LEAF: Buthe 2018 Theorem 2 display 1.6 p. 2, x minus theta x is at most 1.95 sqrt x
for 1423 ≤ x ≤ 10^19. Class HARD, cited computation: section 6 derives it from Lemma 1,
display 6.4, and the computed psi bounds of Table 1 with zeros up to height 10^11,
and by direct computation below 10^7. -/
theorem buthe2018_display16 (x : ℝ) (hx : 1423 ≤ x) (hx1 : x ≤ 1e19) :
    x - Chebyshev.theta x ≤ 1.95 * √x := by
  sorry

/-- LEAF: Broadbent et al. 2026 Table 2 p. 39, row log x0 = 40, column eta1:
for all x > e^40, |theta x - x| < 8.5536e-7 x / log x. Class HARD, cited analytic
and computational theorem, the corrected replacement of BKLNW Table 15 rows. -/
theorem broadbent2026_row40 (x : ℝ) (hx : exp 40 < x) :
    |Chebyshev.theta x - x| < 8.5536e-7 * x / log x := by
  sorry

/-- LEAF: Broadbent et al. 2026 Table 2 p. 39, row log x0 = 2500, column eta1:
for all x > e^2500, |theta x - x| < 2.6726e-10 x / log x. Class HARD, cited. -/
theorem broadbent2026_row2500 (x : ℝ) (hx : exp 2500 < x) :
    |Chebyshev.theta x - x| < 2.6726e-10 * x / log x := by
  sorry

/-! ### Proved elementary comparisons -/

/-- Tangent line bound at an anchor s0: if 3.9 log s0 and 3.9 are both at most c s0,
then 1.95 log x ≤ c sqrt x for every x with s0 ≤ sqrt x. -/
theorem log_le_of_anchor {c s0 L0 x : ℝ} (hs0 : 0 < s0) (hL : log s0 ≤ L0)
    (h1 : 3.9 * L0 ≤ c * s0) (h2 : 3.9 ≤ c * s0) (hx : s0 ≤ √x) :
    1.95 * log x ≤ c * √x := by
  set s := √x with hsdef
  have hs : 0 < s := lt_of_lt_of_le hs0 hx
  have hx0 : 0 < x := Real.sqrt_pos.mp hs
  have hls : log s = log x / 2 := Real.log_sqrt hx0.le
  have hq : log (s / s0) ≤ s / s0 - 1 := log_le_sub_one_of_pos (div_pos hs hs0)
  have hdiv : log (s / s0) = log s - log s0 := log_div hs.ne' hs0.ne'
  have hc : 3.9 / s0 ≤ c := by rw [div_le_iff₀ hs0]; linarith
  have hkey : 3.9 * (s / s0 - 1) ≤ c * s - c * s0 := by
    have e : 3.9 * (s / s0 - 1) = (s - s0) * (3.9 / s0) := by field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hx)
    linarith
  linarith

/-- exp 1 to the n is exp n, bounded below through exp 1 > 2.7182818283. -/
theorem exp_nat_ge (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ exp n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n

theorem log_anchor_6e11 : log (774596 : ℝ) ≤ 13.7 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h14 := exp_nat_ge 14
  have h03 : (0.7 : ℝ) ≤ exp (-0.3) := by linarith [add_one_le_exp (-0.3 : ℝ)]
  have hs : exp (13.7 : ℝ) = exp ((14 : ℕ) : ℝ) * exp (-0.3) := by
    rw [← exp_add]; norm_num
  rw [hs]
  have hp : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 14 := by positivity
  nlinarith [exp_pos ((14 : ℕ) : ℝ)]

/-- For x ≥ 6e11, 1.95 log x ≤ 6.9322e-5 sqrt x. -/
theorem anchor_6e11 (x : ℝ) (hx : 6e11 ≤ x) : 1.95 * log x ≤ 6.9322e-5 * √x := by
  apply log_le_of_anchor (s0 := 774596) (L0 := 13.7) (by norm_num) log_anchor_6e11
    (by norm_num) (by norm_num)
  calc (774596 : ℝ) = √((774596 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ √x := Real.sqrt_le_sqrt (by linarith)

theorem exp_18_5_ge : (8.4e7 : ℝ) ≤ exp 18.5 := by
  have h18 := exp_nat_ge 18
  have h05 : (1.5 : ℝ) ≤ exp 0.5 := by linarith [add_one_le_exp (0.5 : ℝ)]
  have hs : exp (18.5 : ℝ) = exp ((18 : ℕ) : ℝ) * exp 0.5 := by
    rw [← exp_add]; norm_num
  rw [hs]
  have hp : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 18 := by positivity
  nlinarith [exp_pos ((18 : ℕ) : ℝ)]

theorem sqrt_exp_37 : √(exp 37) = exp 18.5 := by
  rw [show (37 : ℝ) = 18.5 + 18.5 by norm_num, exp_add, Real.sqrt_mul_self (exp_pos _).le]

theorem exp_37_ge : (8.4e7 : ℝ) ≤ exp 37 := by
  have h := exp_18_5_ge
  have h1 : (1 : ℝ) ≤ exp 18.5 := by linarith
  rw [show (37 : ℝ) = 18.5 + 18.5 by norm_num, exp_add]
  nlinarith

/-- For x > e^37, 1.95 log x ≤ 8.6315e-7 sqrt x. -/
theorem anchor_37 (x : ℝ) (hx : exp 37 < x) : 1.95 * log x ≤ 8.6315e-7 * √x := by
  apply log_le_of_anchor (s0 := exp 18.5) (L0 := 18.5) (exp_pos _) (by rw [log_exp])
    (by linarith [exp_18_5_ge]) (by linarith [exp_18_5_ge])
  rw [← sqrt_exp_37]
  exact Real.sqrt_le_sqrt hx.le

theorem exp40_lt_1e19 : exp 40 < (1e19 : ℝ) := by
  have h : exp ((40 : ℕ) : ℝ) = exp 1 ^ 40 := (Real.exp_one_pow 40).symm
  have h2 : exp 1 ^ 40 < (2.7182818286 : ℝ) ^ 40 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (exp_pos 1).le (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ 40 < 1e19 := by norm_num
  have h4 : exp (40 : ℝ) = exp ((40 : ℕ) : ℝ) := by norm_num
  rw [h4, h]; linarith

/-- The Buthe range: from 0 < x - theta x ≤ 1.95 sqrt x and 1.95 log x ≤ c sqrt x,
the k = 1 form |theta x - x| ≤ c x / log x. -/
theorem abs_le_of_sqrt_bounds (x c : ℝ) (hx : 1 < x) (hlow : 0 < x - Chebyshev.theta x)
    (hup : x - Chebyshev.theta x ≤ 1.95 * √x) (hlog : 1.95 * log x ≤ c * √x) :
    |Chebyshev.theta x - x| ≤ c * x / log x := by
  have hl : 0 < log x := log_pos hx
  have hx0 : 0 ≤ x := by linarith
  rw [abs_of_neg (by linarith), neg_sub, le_div_iff₀ hl]
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have h1 := mul_le_mul_of_nonneg_left hlog hs
  have h2 := mul_le_mul_of_nonneg_right hup hl.le
  have e1 : √x * (c * √x) = c * x := by
    rw [show √x * (c * √x) = c * (√x * √x) by ring, hss]
  have e2 : √x * (1.95 * log x) = 1.95 * √x * log x := by ring
  linarith

/-- A row bound with a smaller constant gives the row bound with a larger constant. -/
theorem abs_le_of_row (x a c : ℝ) (hx : 1 < x) (hac : a ≤ c)
    (h : |Chebyshev.theta x - x| < a * x / log x) :
    |Chebyshev.theta x - x| ≤ c * x / log x := by
  have hl : 0 < log x := log_pos hx
  refine h.le.trans (div_le_div_of_nonneg_right ?_ hl.le)
  exact mul_le_mul_of_nonneg_right hac (by linarith)

end LeanLab.BS2022GRH.ThetaLeavesS63

#print axioms LeanLab.BS2022GRH.ThetaLeavesS63.log_le_of_anchor
#print axioms LeanLab.BS2022GRH.ThetaLeavesS63.anchor_6e11
#print axioms LeanLab.BS2022GRH.ThetaLeavesS63.anchor_37
#print axioms LeanLab.BS2022GRH.ThetaLeavesS63.exp40_lt_1e19
#print axioms LeanLab.BS2022GRH.ThetaLeavesS63.abs_le_of_sqrt_bounds
#print axioms LeanLab.BS2022GRH.ThetaLeavesS63.abs_le_of_row
