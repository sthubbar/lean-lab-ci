import LeanLab.PNTPort.ExplicitPsi1.PsiOneRHSimple
import LeanLab.Dudek2014.SigmaHSW

/-!
# The explicit RH bounds for `ψ₁` on the corrected `N(T)` bound

P0100 line, unit U-6651, CLOUD 20261020T1717Z-cloud47. AI wrote this file. Known mathematics,
crude constants. `PNTPort/ExplicitPsi1/PsiOneRH.lean` and `PsiOneRHSimple.lean` with
`TrudgianN70` replaced by `SigmaH.HSWN70`, the Hasanalizade-Shen-Wong bound, through
`SigmaH.split_bound` at `T = 70`, `a = 4/3`, `b = 1`, where `b ≤ 1.1 a T²` holds trivially.
-/

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open LeanLab.Dudek2014.SigmaT (wgt wgt_le wgt_le_inv_sq ne_of_large log_70 Zr fz rhoF norm_fz_le')

/-- `Σ 1/|ρ(ρ+1)| ≤ 128` from the Hasanalizade-Shen-Wong `N(T)` bound. -/
lemma tsum_wgt_le_hsw {ι : Type*} {γ : ι → ℝ} (hN : LeanLab.Dudek2014.SigmaH.HSWN70 γ) :
    ∑' i, wgt γ i ≤ 128 := by
  have hb : ∀ s : Finset ι, ∑ i ∈ s, wgt γ i ≤
      70 * Real.log 70 / Real.pi * (4 / 3) + 1 * (Real.log 70 / (Real.pi * 70)) :=
    fun s => LeanLab.Dudek2014.SigmaH.split_bound hN (a := 4 / 3) (b := 1) (le_refl 70)
      (by norm_num) (by norm_num) (by norm_num) (wgt γ)
      (fun i _ => wgt_le γ i) (fun i hi => wgt_le_inv_sq γ (ne_of_large (le_refl 70) hi)) s
  refine ((LeanLab.Dudek2014.SigmaH.summable_wgt hN).tsum_le_of_sum_le hb).trans ?_
  have h1 := log_70
  have h0 : 0 ≤ Real.log 70 := Real.log_nonneg (by norm_num)
  have hp := Real.pi_gt_d2
  have e1 : 70 * Real.log 70 / Real.pi * (4 / 3) ≤ 70 * 4.3 / 3.14 * (4 / 3) := by
    gcongr
  have e2 : 1 * (Real.log 70 / (Real.pi * 70)) ≤ 4.3 / (3.14 * 70) := by
    rw [one_mul]; gcongr
  norm_num at e1 e2 ⊢
  linarith

/-- **`|ψ₁(y) - y²/2 + y log 2π| ≤ 128 y^{3/2} + 2.393` for `y > 1`**, under RH, CONDITIONAL ON
the Hasanalizade-Shen-Wong `N(T)` bound for the zeros. -/
theorem psi1_explicit_RH_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) {y : ℝ} (hy : 1 < y) :
    |LeanLab.Dudek2014.Section22.psi1 y - (y ^ 2 / 2 - y * Real.log (2 * Real.pi))| ≤
      128 * y ^ (3 / 2 : ℝ) + 2.393 := by
  have hy0 : 0 < y := by linarith
  have hZ : |Zreal y| ≤ 128 * y ^ (3 / 2 : ℝ) := by
    rw [← Zr_eq_Zreal hRH hy0]
    unfold Zr
    have hn : Summable (fun i => ‖fz (rhoF (gZ i)) y‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_fz_le' (gZ i) hy0)
        ((LeanLab.Dudek2014.SigmaH.summable_wgt hN).mul_left (y ^ (3 / 2 : ℝ)))
    calc |(∑' i, fz (rhoF (gZ i)) y).re| ≤ ‖∑' i, fz (rhoF (gZ i)) y‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' i, ‖fz (rhoF (gZ i)) y‖ := norm_tsum_le_tsum_norm hn
      _ ≤ ∑' i, y ^ (3 / 2 : ℝ) * wgt gZ i :=
          hn.tsum_le_tsum (fun i => norm_fz_le' (gZ i) hy0)
            ((LeanLab.Dudek2014.SigmaH.summable_wgt hN).mul_left _)
      _ = y ^ (3 / 2 : ℝ) * ∑' i, wgt gZ i := tsum_mul_left
      _ ≤ y ^ (3 / 2 : ℝ) * 128 := by
          gcongr; exact tsum_wgt_le_hsw hN
      _ = 128 * y ^ (3 / 2 : ℝ) := by ring
  have hE := error_bound hy
  rw [psi1_formula hy]
  have e : y ^ 2 / 2 - y * Real.log (2 * Real.pi) - Zreal y +
      (deriv riemannZeta (-1) / riemannZeta (-1)).re - y * ∑' n, tb y n -
      (y ^ 2 / 2 - y * Real.log (2 * Real.pi)) =
      -Zreal y + ((deriv riemannZeta (-1) / riemannZeta (-1)).re - y * ∑' n, tb y n) := by ring
  rw [e]
  calc _ ≤ |-Zreal y| + |(deriv riemannZeta (-1) / riemannZeta (-1)).re - y * ∑' n, tb y n| :=
        abs_add_le _ _
    _ ≤ _ := by rw [abs_neg]; linarith

/-- **`|ψ₁(y) - y²/2| ≤ 133 y^{3/2}` for `y > 1`**, under RH, CONDITIONAL ON the
Hasanalizade-Shen-Wong `N(T)` bound. -/
theorem psi1_RH_simple_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) {y : ℝ} (hy : 1 < y) :
    |LeanLab.Dudek2014.Section22.psi1 y - y ^ 2 / 2| ≤ 133 * y ^ (3 / 2 : ℝ) := by
  have h := psi1_explicit_RH_hsw hRH hN hy
  have hy0 : 0 ≤ y := by linarith
  have hl : Real.log (2 * Real.pi) ≤ 2 := LeanLab.PNTPort.ZetaZeros.log_two_pi_le
  have hl0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hp1 : y ≤ y ^ (3 / 2 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one y]
    exact Real.rpow_le_rpow_of_exponent_le hy.le (by norm_num)
  have hp0 : 1 ≤ y ^ (3 / 2 : ℝ) := Real.one_le_rpow hy.le (by norm_num)
  have e : LeanLab.Dudek2014.Section22.psi1 y - y ^ 2 / 2 =
      (LeanLab.Dudek2014.Section22.psi1 y - (y ^ 2 / 2 - y * Real.log (2 * Real.pi))) -
        y * Real.log (2 * Real.pi) := by ring
  rw [e]
  have hyl : y * Real.log (2 * Real.pi) ≤ 2 * y ^ (3 / 2 : ℝ) := by nlinarith
  have hyl0 : 0 ≤ y * Real.log (2 * Real.pi) := mul_nonneg hy0 hl0
  calc _ ≤ |LeanLab.Dudek2014.Section22.psi1 y - (y ^ 2 / 2 - y * Real.log (2 * Real.pi))| +
        |y * Real.log (2 * Real.pi)| := abs_sub _ _
    _ ≤ (128 * y ^ (3 / 2 : ℝ) + 2.393) + 2 * y ^ (3 / 2 : ℝ) := by
        rw [abs_of_nonneg hyl0]; linarith
    _ ≤ 133 * y ^ (3 / 2 : ℝ) := by linarith

end LeanLab.PNTPort.ExplicitPsi1.Trivial
