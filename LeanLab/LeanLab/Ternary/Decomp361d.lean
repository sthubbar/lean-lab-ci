/-
Chen and Wang 1996, doi 10.12386/A1996sxxb0030, pages 172 to 174.
Elementary logarithmic cutoff checks used in the written proof.
These checks do not supply any major or minor arc estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.State1535
import LeanLab.Ternary.Decomp1535b

namespace LeanLab.Ternary.U1535.Task361

/-- A rational lower certificate for the exponential used in the cutoff checks.
Derived arithmetic for P0033 pages 172 and 173. -/
theorem exp_9_7_lower : (13700 : ℝ) ≤ Real.exp 9.7 := by
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.718) h1 9
  have heq : Real.exp 9.7 = Real.exp 1 ^ (9 : ℕ) * Real.exp 0.7 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  rw [heq]
  calc
    (13700 : ℝ) ≤ (2.718 : ℝ) ^ (9 : ℕ) * (0.7 + 1) := by norm_num
    _ ≤ Real.exp 1 ^ (9 : ℕ) * Real.exp 0.7 :=
      mul_le_mul hpow (Real.add_one_le_exp _) (by norm_num) (by positivity)

/-- The function y minus k log y is increasing for y at least a positive x
with k at most x. Derived logarithmic comparison for P0033 cutoff displays. -/
theorem sub_mul_log_mono {x y k : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hk : k ≤ x) :
    x - k * Real.log x ≤ y - k * Real.log y := by
  have hy : 0 < y := hx.trans_le hxy
  have hlog : 0 ≤ Real.log y - Real.log x :=
    sub_nonneg.mpr (Real.log_le_log hx hxy)
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have hprod : x * (Real.log y - Real.log x) ≤ y - x := by
    have hh := mul_le_mul_of_nonneg_left h hx.le
    have heq : x * (y / x - 1) = y - x := by field_simp <;> ring
    rwa [heq] at hh
  have hh := mul_le_mul_of_nonneg_right hk hlog
  linarith

/-- A logarithmic margin at the threshold propagates to every larger real N.
Derived helper for the two cutoff statements on P0033 pages 172 and 173. -/
theorem cutoff_of_log_margin {a b N : ℝ} (k : ℕ)
    (hk : (k : ℝ) ≤ Real.exp a)
    (hgap : Real.exp b ≤ Real.exp a - k * a)
    (hN : Real.exp (Real.exp a) ≤ N) :
    Real.exp (Real.exp b) ≤ N / Real.log N ^ k := by
  have hNpos : 0 < N := (Real.exp_pos _).trans_le hN
  have hlN : Real.exp a ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hN
  have hlpos : 0 < Real.log N := (Real.exp_pos _).trans_le hlN
  have hm := sub_mul_log_mono (Real.exp_pos a) hlN hk
  rw [Real.log_exp] at hm
  apply (Real.le_log_iff_exp_le (div_pos hNpos (pow_pos hlpos k))).mp
  rw [Real.log_div hNpos.ne' (pow_ne_zero k hlpos.ne'), Real.log_pow]
  exact hgap.trans hm

/-- The lower cutoff in Lemma 6 stays above the Lemma 5 threshold.
P0033 page 173, first sentence of the proof of Lemma 6, r equals log N. -/
theorem chenWang_cutoff_three {N : ℝ} (hN : Real.exp (Real.exp 9.715) ≤ N) :
    Real.exp (Real.exp 9.706) ≤ N / Real.log N ^ (3 : ℕ) := by
  have hlow : (13700 : ℝ) ≤ Real.exp 9.706 := exp_9_7_lower.trans
    (Real.exp_le_exp.mpr (by norm_num))
  have hstep : Real.exp 9.706 * (0.009 + 1) ≤ Real.exp 9.715 := by
    calc
      _ ≤ Real.exp 9.706 * Real.exp 0.009 :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; norm_num
  apply cutoff_of_log_margin 3 (by linarith [Real.exp_le_exp.mpr (by norm_num : (9.706 : ℝ) ≤ 9.715)])
    (by nlinarith) hN

/-- The major arc cutoff stays above the distribution estimate threshold.
P0033 page 172 below display 15, r equals log N. -/
theorem chenWang_cutoff_seven {N : ℝ} (hN : Real.exp (Real.exp 9.715) ≤ N) :
    Real.exp (Real.exp 9.71) ≤ N / Real.log N ^ (7 : ℕ) := by
  have hlow : (13700 : ℝ) ≤ Real.exp 9.71 := exp_9_7_lower.trans
    (Real.exp_le_exp.mpr (by norm_num))
  have hstep : Real.exp 9.71 * (0.005 + 1) ≤ Real.exp 9.715 := by
    calc
      _ ≤ Real.exp 9.71 * Real.exp 0.005 :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; norm_num
  apply cutoff_of_log_margin 7 (by linarith [Real.exp_le_exp.mpr (by norm_num : (9.71 : ℝ) ≤ 9.715)])
    (by nlinarith) hN

/-- The three printed arc budgets leave the exact positive margin 0.1539.
P0033 page 174, final display. The scale and all estimates remain hypotheses. -/
theorem chenWang_arc_margin {I I₁ I₂ I₃ scale : ℝ}
    (hs : 0 < scale) (hI : I = I₁ + I₂ + I₃)
    (h₁ : 0.6249 * scale ≤ I₁) (h₂ : |I₂| ≤ 0.138 * scale)
    (h₃ : |I₃| ≤ 0.333 * scale) :
    0.1539 * scale ≤ I ∧ 0 < I := by
  have h₂' := (abs_le.mp h₂).1
  have h₃' := (abs_le.mp h₃).1
  constructor <;> nlinarith

/-- The Chen and Wang threshold is strictly above the sealed Helfgott analytic threshold.
P0033 page 169 and P0001 arXiv 1312.7748, the analytic threshold in the introduction.
This records why an estimate available only above the former threshold does not cover the latter. -/
theorem chenWang_threshold_exceeds_helfgott :
    (10 : ℝ) ^ (27 : ℕ) < Real.exp (Real.exp 9.715) := by
  calc
    (10 : ℝ) ^ (27 : ℕ) < (10 : ℝ) ^ (7193 : ℕ) :=
      pow_lt_pow_right₀ (by norm_num) (by norm_num)
    _ ≤ Real.exp (Real.exp 9.715) := exp_exp_lower

end LeanLab.Ternary.U1535.Task361
