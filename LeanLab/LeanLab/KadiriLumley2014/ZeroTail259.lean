/-
P0059 arXiv 1407.7902v1 page 7 equations 2.47 to 2.49.
Convergence of the positive-ordinate tail families, without numerical zero estimates.
AI wrote this Lean code. CODEX task259. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroCounts259
import LeanLab.KadiriLumley2014.Kernel259

namespace LeanLab.KadiriLumley2014.Task259

open Real Set
open LeanLab.PNTPort.ExplicitPsi1

/-- In the open strip and above height one, the zero denominator is at most six times height squared. -/
theorem high_ordinate_norm_product_le
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1})
    {H : ℝ} (hH : 1 ≤ H) (hγ : H < (ρ : ℂ).im) :
    ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ ≤ 6 * (ρ : ℂ).im ^ 2 := by
  have hγ1 : 1 < (ρ : ℂ).im := hH.trans_lt hγ
  have hr := ρ.property.2
  have h1 : ‖(ρ : ℂ)‖ ≤ 2 * (ρ : ℂ).im := by
    have hn := Complex.norm_le_abs_re_add_abs_im (ρ : ℂ)
    rw [abs_of_pos hr.1, abs_of_pos (by linarith)] at hn
    linarith [hr.2]
  have h2 : ‖(ρ : ℂ) + 1‖ ≤ 3 * (ρ : ℂ).im := by
    have hn := Complex.norm_le_abs_re_add_abs_im ((ρ : ℂ) + 1)
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at hn
    rw [abs_of_pos (by linarith [hr.1]), abs_of_pos (by linarith)] at hn
    linarith [hr.2]
  rw [norm_mul]
  calc
    _ ≤ (2 * (ρ : ℂ).im) * (3 * (ρ : ℂ).im) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
    _ = _ := by ring

/-- Every reciprocal power tail of order at least two is summable with multiplicity. -/
theorem summable_high_ordinate_powers {m : ℕ} (hm : 1 ≤ m) {H : ℝ} (hH : 1 ≤ H) :
    Summable (fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} =>
      if H < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) /
        (ρ : ℂ).im ^ (m + 1) else 0) := by
  have hs := summable_hw
  rw [Zall_eq] at hs
  change Summable (fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} => hw ρ) at hs
  apply Summable.of_norm_bounded (hs.mul_left 6)
  intro ρ
  by_cases hγ : H < (ρ : ℂ).im
  · have hγ1 : 1 < (ρ : ℂ).im := hH.trans_lt hγ
    have hγ0 : 0 < (ρ : ℂ).im := by linarith
    have hp : 0 < (ρ : ℂ).im ^ (m + 1) := pow_pos hγ0 _
    have hden : 0 < ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := by
      apply norm_pos_iff.mpr
      apply mul_ne_zero
      · intro h
        have hh := congrArg Complex.im h
        simp only [Complex.zero_im] at hh
        linarith
      · intro h
        have hh := congrArg Complex.im h
        simp only [Complex.add_im, Complex.one_im, Complex.zero_im, add_zero] at hh
        linarith
    have hpow : (ρ : ℂ).im ^ 2 ≤ (ρ : ℂ).im ^ (m + 1) :=
      pow_le_pow_right₀ hγ1.le (by omega)
    have hd := (high_ordinate_norm_product_le ρ hH hγ).trans
      (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 6))
    rw [ite_eq_left hγ, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hp.le)]
    unfold hw
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hp hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt riemannZeta (ρ : ℂ)))]
  · simp only [ite_eq_right hγ, norm_zero]
    exact mul_nonneg (by norm_num) (hw_nonneg _)

/-- Any nonnegative multiplier at most one preserves convergence of the high-ordinate tail. -/
theorem summable_high_ordinate_weighted {m : ℕ} (hm : 1 ≤ m) {H : ℝ} (hH : 1 ≤ H)
    (w : ℂ → ℝ)
    (hw : ∀ ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
      H < (ρ : ℂ).im → 0 ≤ w ρ ∧ w ρ ≤ 1) :
    Summable (fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} =>
      if H < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * w ρ /
        (ρ : ℂ).im ^ (m + 1) else 0) := by
  apply Summable.of_nonneg_of_le _ _ (summable_high_ordinate_powers hm hH)
  · intro ρ
    split_ifs with hγ
    · have hγ0 : 0 < (ρ : ℂ).im := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hH.trans hγ.le)
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw ρ hγ).1) (pow_nonneg hγ0.le _)
    · rfl
  · intro ρ
    split_ifs with hγ
    · have hγ0 : 0 < (ρ : ℂ).im := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hH.trans hγ.le)
      apply div_le_div_of_nonneg_right _ (pow_nonneg hγ0.le _)
      simpa using mul_le_mul_of_nonneg_left (hw ρ hγ).2 (Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt riemannZeta (ρ : ℂ)))
    · rfl

/-- The zero-free power in equation 2.49 is a valid bounded multiplier for convergence. -/
theorem summable_zero_free_density_tail {m : ℕ} (hm : 1 ≤ m) {H X R0 σ : ℝ}
    (hH : 1 < H) (hX : 1 ≤ X) (hR0 : 0 < R0) :
    Summable (fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} =>
      if H < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (if σ < (ρ : ℂ).re then X ^ (-1 / (R0 * Real.log (ρ : ℂ).im)) else 0) /
          (ρ : ℂ).im ^ (m + 1) else 0) := by
  refine summable_high_ordinate_weighted hm hH.le
    (fun ρ : ℂ => if σ < ρ.re then X ^ (-1 / (R0 * Real.log ρ.im)) else 0) ?_
  intro ρ hγ
  split_ifs with hσ
  · have hlog : 0 < Real.log (ρ : ℂ).im := Real.log_pos (hH.trans hγ)
    constructor
    · exact Real.rpow_nonneg (by linarith) _
    · exact Real.rpow_le_one_of_one_le_of_nonpos hX
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) (mul_nonneg hR0.le hlog.le))
  · norm_num

end LeanLab.KadiriLumley2014.Task259
