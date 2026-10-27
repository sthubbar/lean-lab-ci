/-
Tao 2012, P0007, unit U-0919, run 20261018T0602Z-9546. arXiv 1201.6656, Section 8,
Proposition 8.4, the L² estimate, and the weakly major arc step after it. Read in Claude in
Chrome, arxiv.org/html/1201.6656, 2026-10-18.
Numerical steps only; the analytic inputs, Proposition 4.10 and Corollary 4.8, stay cited.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Tao2012.Prop84

open Real

/-- `H = ⌊N₀/3⌋` with `N₀ = 4 × 10^14`. -/
def Hn : ℕ := 4 * 10 ^ 14 / 3

theorem Hn_eq : Hn = 133333333333333 := by norm_num [Hn]

noncomputable def H : ℝ := 133333333333333

theorem H_le : H ≤ 4e14 / 3 := by norm_num [H]

/-! ## Proposition 8.4: the bracket of Proposition 4.10 is at most 8.001 / 8 -/

theorem exp_one_gt : (2.7 : ℝ) < exp 1 := by
  have := Real.exp_one_gt_d9; linarith

theorem exp_one_lt : exp 1 < 3 := by
  have := Real.exp_one_lt_d9; linarith

/-- `log y < 54` whenever `0 < y ≤ 10^20`, from `e^54 > 2.7^54 > 10^20`. -/
theorem log_lt_54 {y : ℝ} (hy : 0 < y) (h : y ≤ 1e20) : log y < 54 := by
  rw [Real.log_lt_iff_lt_exp hy]
  have h1 : (2.7 : ℝ) ^ 54 < exp 1 ^ 54 := by
    exact pow_lt_pow_left₀ exp_one_gt (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at h1
  norm_num at h1
  have h2 : (1e20 : ℝ) < 2.7 ^ 54 := by norm_num
  linarith

/-- `3 < log y` whenever `27 ≤ y`, from `e^3 < 27`. -/
theorem log_gt_3 {y : ℝ} (h : 27 ≤ y) : 3 < log y := by
  have hy : 0 < y := by linarith
  rw [Real.lt_log_iff_exp_lt hy]
  have h1 : exp 1 ^ 3 < (3 : ℝ) ^ 3 := by
    exact pow_lt_pow_left₀ exp_one_lt (Real.exp_pos 1).le (by norm_num)
  rw [← Real.exp_nat_mul] at h1
  norm_num at h1
  linarith

theorem one_lt_log_three : 1 < log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact exp_one_lt

/-- The bracket of Proposition 4.10 at `H = ⌊N₀/3⌋` and `log x ≤ 3100`:
`8 (1 + 0.13 log x / H + (e^γ log log 2H + 2.507 / log log 2H) log 9H / 2H) ≤ 8.001`,
the paper's "brief computation". -/
theorem bracket_le {L : ℝ} (hL : L ≤ 3100) :
    8 * (1 + 0.13 * L / H +
      (exp eulerMascheroniConstant * log (log (2 * H)) + 2.507 / log (log (2 * H))) *
        log (9 * H) / (2 * H)) ≤ 8.001 := by
  have hH : (0 : ℝ) < H := by norm_num [H]
  have hl2 : 3 < log (2 * H) := log_gt_3 (by norm_num [H])
  have hl2' : log (2 * H) < 54 := log_lt_54 (by positivity) (by norm_num [H])
  have hl9 : log (9 * H) < 54 := log_lt_54 (by positivity) (by norm_num [H])
  have hl9' : 0 < log (9 * H) := Real.log_pos (by norm_num [H])
  have hll : 1 < log (log (2 * H)) := by
    calc (1 : ℝ) < log 3 := one_lt_log_three
      _ < log (log (2 * H)) := Real.log_lt_log (by norm_num) hl2
  have hll' : log (log (2 * H)) < 54 := by
    have := Real.log_le_sub_one_of_pos (show 0 < log (2 * H) by linarith)
    linarith
  have hg : exp eulerMascheroniConstant < 3 := by
    have h1 : eulerMascheroniConstant < 1 := by
      have := Real.eulerMascheroniConstant_lt_two_thirds; linarith
    calc exp eulerMascheroniConstant < exp 1 := Real.exp_lt_exp.mpr h1
      _ < 3 := exp_one_lt
  have hg0 : 0 < exp eulerMascheroniConstant := Real.exp_pos _
  have hdiv : 2.507 / log (log (2 * H)) < 2.507 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have hdiv0 : 0 < 2.507 / log (log (2 * H)) := by positivity
  have hA : exp eulerMascheroniConstant * log (log (2 * H)) + 2.507 / log (log (2 * H)) < 165 := by
    nlinarith
  have hA0 : 0 < exp eulerMascheroniConstant * log (log (2 * H)) + 2.507 / log (log (2 * H)) := by
    positivity
  have hB : (exp eulerMascheroniConstant * log (log (2 * H)) + 2.507 / log (log (2 * H))) *
      log (9 * H) < 165 * 54 := by
    have := mul_lt_mul'' hA hl9 hA0.le hl9'.le
    linarith
  have hT1 : 0.13 * L / H ≤ 0.13 * 3100 / H := by
    apply div_le_div_of_nonneg_right _ hH.le; linarith
  have hT2 : (exp eulerMascheroniConstant * log (log (2 * H)) + 2.507 / log (log (2 * H))) *
      log (9 * H) / (2 * H) ≤ 165 * 54 / (2 * H) := by
    apply div_le_div_of_nonneg_right hB.le (by positivity)
  have hnum : 8 * (1 + 0.13 * 3100 / H + 165 * 54 / (2 * H)) ≤ (8.001 : ℝ) := by
    norm_num [H]
  nlinarith

/-- The step `8 H² x ≤ 8 (N₀/3)² x` that lets the paper write `(N₀/3)²` for `H²`. -/
theorem H_sq_le : H ^ 2 ≤ (4e14 / 3) ^ 2 := by
  have h0 : (0 : ℝ) ≤ H := by norm_num [H]
  exact pow_le_pow_left₀ h0 H_le 2

/-- Subtracting, page 8.4's proof: `8.001 - 0.919 ≤ 7.09`. -/
theorem subtract : (8.001 : ℝ) - 0.919 ≤ 7.09 := by norm_num

/-! ## The weakly major arc step after (8.18) -/

noncomputable def η₀ (t : ℝ) : ℝ := 4 * max (log 2 - |log (2 * t)|) 0

/-- On `(1/4, 1/2)`, `η₀ t = 4 log (4 t)`, so `η₀' = 4 / t`. -/
theorem η₀_left {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 1 / 2) : η₀ t = 4 * log (4 * t) := by
  have ht : 0 < t := by linarith
  have hl : log (2 * t) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hl2 : -log 2 ≤ log (2 * t) := by
    have : log (1 / 2) ≤ log (2 * t) := Real.log_le_log (by norm_num) (by linarith)
    rwa [one_div, Real.log_inv] at this
  have h4 : log (4 * t) = log 2 + log (2 * t) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  unfold η₀
  rw [abs_of_nonpos hl, h4]
  rw [max_eq_left (by linarith)]
  ring

/-- On `(1/2, 1)`, `η₀ t = -4 log t`, so `η₀' = -4 / t`. -/
theorem η₀_right {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) : η₀ t = -4 * log t := by
  have ht : 0 < t := by linarith
  have hl : 0 ≤ log (2 * t) := Real.log_nonneg (by linarith)
  have h2t : log (2 * t) = log 2 + log t := Real.log_mul (by norm_num) (by positivity)
  have hlt : log t ≤ 0 := Real.log_nonpos ht.le h2
  unfold η₀
  rw [abs_of_nonneg hl, h2t, max_eq_left (by linarith)]
  ring

theorem hasDerivAt_left {t : ℝ} (h1 : 1 / 4 < t) (h2 : t < 1 / 2) :
    HasDerivAt η₀ (4 / t) t := by
  have ht : 0 < t := by linarith
  have hev : η₀ =ᶠ[nhds t] fun s => 4 * log (4 * s) := by
    filter_upwards [Ioo_mem_nhds h1 h2] with s hs
    exact η₀_left hs.1.le hs.2.le
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have := ((hasDerivAt_id t).const_mul 4).log (by simp; positivity)
  convert this.const_mul 4 using 1
  · funext s; simp
  · simp only [id]; field_simp

theorem hasDerivAt_right {t : ℝ} (h1 : 1 / 2 < t) (h2 : t < 1) :
    HasDerivAt η₀ (-4 / t) t := by
  have ht : 0 < t := by linarith
  have hev : η₀ =ᶠ[nhds t] fun s => -4 * log s := by
    filter_upwards [Ioo_mem_nhds h1 h2] with s hs
    exact η₀_right hs.1.le hs.2.le
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  convert (Real.hasDerivAt_log ht.ne').const_mul (-4) using 1
  field_simp

/-- `‖η₀'‖_{L¹} = 8 log 2`, the paper's (5.11): `|η₀'| = 4 / t` on both pieces. -/
theorem η₀'_L1 : (∫ t in (1 / 4 : ℝ)..(1 / 2), 4 / t) + (∫ t in (1 / 2 : ℝ)..1, 4 / t) =
    8 * log 2 := by
  have e1 : (∫ t in (1 / 4 : ℝ)..(1 / 2), 4 / t) = 4 * log 2 := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  have e2 : (∫ t in (1 / 2 : ℝ)..1, 4 / t) = 4 * log 2 := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  rw [e1, e2]; ring

/-- `‖η₀‖_{L^∞} = 4 log 2`, the paper's (5.10): attained at `1/2`, never exceeded. -/
theorem η₀_half : η₀ (1 / 2) = 4 * log 2 := by
  unfold η₀; norm_num; exact (Real.log_pos (by norm_num)).le

theorem η₀_le (t : ℝ) : η₀ t ≤ 4 * log 2 := by
  unfold η₀
  have h2 : 0 < log 2 := Real.log_pos (by norm_num)
  have := abs_nonneg (log (2 * t))
  have : max (log 2 - |log (2 * t)|) 0 ≤ log 2 := max_le (by linarith) h2.le
  linarith

noncomputable def T0 : ℝ := 3.29e9
noncomputable def K : ℝ := 1e3

/-- Lemma 3.3 with `k = 1` and `α ≥ T₀ / (3.6 π x)` gives `‖η₀'‖₁ · 3.6 π K / (2 π T₀)`;
with `‖η₀'‖₁ = 8 log 2` that is `14.4 K log 2 / T₀`, twice the printed `7.2 K log 2 / T₀`. -/
theorem lemma33_value :
    8 * log 2 * (3.6 * π * K) / (2 * π * T0) = 14.4 * K * log 2 / T0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold T0 K
  field_simp
  ring

/-- FINDING candidate: the printed bound is the value with `‖η₀‖_∞ = 4 log 2`, the paper's
(5.10), in place of `‖η₀'‖₁ = 8 log 2`, (5.11); the printed bound is too small by a factor 2. -/
theorem printed_bound_half :
    7.2 * K * log 2 / T0 < 8 * log 2 * (3.6 * π * K) / (2 * π * T0) := by
  rw [lemma33_value]
  have h2 : 0 < log 2 := Real.log_pos (by norm_num)
  unfold T0 K
  apply div_lt_div_of_pos_right _ (by norm_num)
  nlinarith

theorem printed_bound_with_η₀_sup :
    4 * log 2 * (3.6 * π * K) / (2 * π * T0) = 7.2 * K * log 2 / T0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold T0 K
  field_simp
  ring

/-- The step still holds "with plenty of room to spare": `14.4 K log 2 / T₀ ≤ 0.077`, and the
`O*(1.1 × 10⁻⁶)` error keeps the total within `0.078`. -/
theorem weak_major_ok : 14.4 * K * log 2 / T0 + 1.1e-6 ≤ 0.078 ∧ 14.4 * K * log 2 / T0 ≤ 0.077 := by
  have h2 : log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h0 : 0 < log 2 := Real.log_pos (by norm_num)
  unfold T0 K
  constructor
  · rw [div_add' _ _ _ (by norm_num), div_le_iff₀ (by norm_num)]; nlinarith
  · rw [div_le_iff₀ (by norm_num)]; nlinarith

end LeanLab.Tao2012.Prop84

#print axioms LeanLab.Tao2012.Prop84.bracket_le
#print axioms LeanLab.Tao2012.Prop84.H_sq_le
#print axioms LeanLab.Tao2012.Prop84.subtract
#print axioms LeanLab.Tao2012.Prop84.η₀_left
#print axioms LeanLab.Tao2012.Prop84.η₀_right
#print axioms LeanLab.Tao2012.Prop84.hasDerivAt_left
#print axioms LeanLab.Tao2012.Prop84.hasDerivAt_right
#print axioms LeanLab.Tao2012.Prop84.η₀'_L1
#print axioms LeanLab.Tao2012.Prop84.η₀_half
#print axioms LeanLab.Tao2012.Prop84.η₀_le
#print axioms LeanLab.Tao2012.Prop84.lemma33_value
#print axioms LeanLab.Tao2012.Prop84.printed_bound_half
#print axioms LeanLab.Tao2012.Prop84.printed_bound_with_η₀_sup
#print axioms LeanLab.Tao2012.Prop84.weak_major_ok
#print axioms LeanLab.Tao2012.Prop84.Hn_eq
