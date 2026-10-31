import LeanLab.PNTPort.ExplicitPsi1.PsiUnsmooth
import LeanLab.Dudek2014.PsiOneHSW

/-!
# Sharper explicit RH bounds for `ψ₁` and `ψ`, on the corrected `N(T)` bound

I-5240, unit U-6654, CLOUD 20261020T1717Z-cloud47. AI wrote this file. Known mathematics.

* `tsum_wgt_sharp`: `Σ 1/|ρ(ρ+1)| ≤ 1/3` over any ordinate family satisfying `HSWN70`, the
  Hasanalizade-Shen-Wong `N(T)` bound, with every ordinate `|γ| ≥ 14`; the head `|γ| ≤ 70`
  counted by `SigmaH.head_count`, each term at most `1/196`, the tail by `SigmaH.tail_inv_sq`.
  The true sum is about `0.046`; cloud45's bound without the first ordinate was `128`.
* `psi1_explicit_RH_sharp`: `|ψ₁(y) - y²/2 + y log 2π| ≤ y^{3/2}/3 + 2.393` for `y > 1`;
* `psi_RH_34_sharp`: `|ψ(x) - x| ≤ 1.23 x^{3/4}` for `x ≥ 10^4`, by `psi1_diff_bounds` with
  `h = 1.22 x^{3/4}`; cloud46's `psi_RH_34` has `32 x^{3/4}` for `x ≥ 64⁴`.
All under RH, CONDITIONAL ON `HSWN70` and `Ordinates14` for the zeros, the second the cited
computation that no nontrivial zero has `|γ| < 14`. The exponent `3/4` is the trivial one from a
single unsmoothing; Schoenfeld's `√x log² x/8π` needs the truncated formula for `ψ` itself.
Binary Goldbach is OPEN.
-/

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Real Finset
open LeanLab.Dudek2014.Section22
open LeanLab.Dudek2014.SigmaT (wgt wgt_le_inv_sq log_70 Zr fz rhoF norm_fz_le')

/-- `Σ 1/|ρ(ρ+1)| ≤ 1/3` from `HSWN70` and every `|γ| ≥ 14`. -/
lemma tsum_wgt_sharp {ι : Type*} {γ : ι → ℝ} (hN : LeanLab.Dudek2014.SigmaH.HSWN70 γ)
    (h14 : ∀ i, 14 ≤ |γ i|) : ∑' i, wgt γ i ≤ 1 / 3 := by
  have hl := log_70
  have hl0 : 0 ≤ Real.log 70 := Real.log_nonneg (by norm_num)
  have hp := Real.pi_gt_d2
  have hb : ∀ s : Finset ι, ∑ i ∈ s, wgt γ i ≤ 1 / 3 := by
    intro s
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i => |γ i| ≤ 70)]
    have hne : ∀ i, γ i ≠ 0 := fun i h0 => by have := h14 i; rw [h0, abs_zero] at this; linarith
    have hsq : ∀ i, 1 / γ i ^ 2 ≤ 1 / 196 := fun i => by
      apply one_div_le_one_div_of_le (by norm_num)
      have := h14 i
      have h2 : (14 : ℝ) ^ 2 ≤ |γ i| ^ 2 := by gcongr
      rw [sq_abs] at h2; linarith
    have h1 : ∑ i ∈ s.filter (fun i => |γ i| ≤ 70), wgt γ i ≤
        ((s.filter (fun i => |γ i| ≤ 70)).card : ℝ) * (1 / 196) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun i _ => (wgt_le_inv_sq γ (hne i)).trans (hsq i)
    have hc := LeanLab.Dudek2014.SigmaH.head_count hN (le_refl 70) s
    have h2 : ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ 70), wgt γ i ≤
        ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ 70), 1 / γ i ^ 2 :=
      Finset.sum_le_sum fun i _ => wgt_le_inv_sq γ (hne i)
    have ht := LeanLab.Dudek2014.SigmaH.tail_inv_sq hN (le_refl 70) s
    have e1 : 70 * Real.log 70 / π ≤ 70 * 4.3 / 3.14 := by gcongr
    have e2 : Real.log 70 / (π * 70) ≤ 4.3 / (3.14 * 70) := by gcongr
    have hE : (1.004 * Real.log 70 + 41.26 - 0.25 * 70) / (70 : ℝ) ^ 2 ≤ 0.006 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    have e3 : (70 * 4.3 / 3.14 : ℝ) ≤ 95.9 := by norm_num
    have e4 : (4.3 / (3.14 * 70) : ℝ) ≤ 0.0196 := by norm_num
    linarith
  exact (LeanLab.Dudek2014.SigmaH.summable_wgt hN).tsum_le_of_sum_le hb

/-- **`|ψ₁(y) - y²/2 + y log 2π| ≤ y^{3/2}/3 + 2.393` for `y > 1`**, under RH, CONDITIONAL ON
`HSWN70` and `Ordinates14` for the zeros. -/
theorem psi1_explicit_RH_sharp (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) {y : ℝ} (hy : 1 < y) :
    |psi1 y - (y ^ 2 / 2 - y * Real.log (2 * Real.pi))| ≤ 1 / 3 * y ^ (3 / 2 : ℝ) + 2.393 := by
  have hy0 : 0 < y := by linarith
  have hZ : |Zreal y| ≤ 1 / 3 * y ^ (3 / 2 : ℝ) := by
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
      _ ≤ y ^ (3 / 2 : ℝ) * (1 / 3) := by
          gcongr; exact tsum_wgt_sharp hN h14
      _ = 1 / 3 * y ^ (3 / 2 : ℝ) := by ring
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

/-- `y^{3/2} ≤ y B` when `y ≤ B²`. -/
lemma rpow32_le_mul {y B : ℝ} (hy : 0 ≤ y) (hB : 0 ≤ B) (h : y ≤ B ^ 2) :
    y ^ (3 / 2 : ℝ) ≤ y * B := by
  have e : y ^ (3 / 2 : ℝ) = y * √y := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hy (by norm_num), Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hy
  rw [Real.sqrt_le_left hB]; exact h

/-- The arithmetic of the lower bound, in plain real variables. -/
lemma lower_arith {x h c A B Ψ Q V3 V6 : ℝ} (u2 : A - B ≤ h * Ψ)
    (b0 : -(1 / 3 * V6 + 2.393) ≤ A - (x ^ 2 / 2 - x * c))
    (bm : B - ((x - h) ^ 2 / 2 - (x - h) * c) ≤ 1 / 3 * Q + 2.393) (pm : Q ≤ V6)
    (hh2 : h ^ 2 = 1.4884 * V6) (hc3 : h * c ≤ 2 * h) (hh4 : 2 * h = 2.44 * V3)
    (hv : 2440 * V3 ≤ 2.44 * V6) (hV3 : 1000 ≤ V3) (hhv : h * V3 = 1.22 * V6) :
    h * (x - 1.23 * V3) ≤ h * Ψ := by
  have em : (x - h) ^ 2 / 2 = x ^ 2 / 2 - x * h + h ^ 2 / 2 := by ring
  have emc : (x - h) * c = x * c - h * c := by ring
  have hm1 : h * (x - 1.23 * V3) = x * h - 1.23 * (h * V3) := by ring
  linarith

/-- The arithmetic of the upper bound, in plain real variables. -/
lemma upper_arith {x h c A C Ψ R V6 : ℝ} (u1 : h * Ψ ≤ C - A)
    (b0 : -(1 / 3 * V6 + 2.393) ≤ A - (x ^ 2 / 2 - x * c))
    (b1 : C - ((x + h) ^ 2 / 2 - (x + h) * c) ≤ 1 / 3 * R + 2.393) (p1 : R ≤ 1.25 * V6)
    (hh2 : h ^ 2 = 1.4884 * V6) (hc0 : 1.8 * h ≤ h * c) (hh3 : 1220 ≤ h) {V3 : ℝ}
    (hhv : h * V3 = 1.22 * V6) (hV6 : 0 ≤ V6) :
    h * Ψ ≤ h * (x + 1.23 * V3) := by
  have ep : (x + h) ^ 2 / 2 = x ^ 2 / 2 + x * h + h ^ 2 / 2 := by ring
  have epc : (x + h) * c = x * c + h * c := by ring
  have hm1 : h * (x + 1.23 * V3) = x * h + 1.23 * (h * V3) := by ring
  linarith

/-- **`|ψ(x) - x| ≤ 1.23 x^{3/4}` for `x ≥ 10^4`**, under RH, CONDITIONAL ON `HSWN70` and
`Ordinates14` for the zeros. -/
theorem psi_RH_34_sharp (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) {x : ℝ} (hx : 10 ^ 4 ≤ x) :
    |psiF x - x| ≤ 1.23 * x ^ (3 / 4 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  set v := x ^ (1 / 4 : ℝ) with hv
  have hv0 : 0 ≤ v := Real.rpow_nonneg hx0 _
  have hxv : x = v ^ 4 := rpow1_of hx0
  have hv10 : 10 ≤ v := by
    by_contra hlt
    push Not at hlt
    have : v ^ 4 < 10 ^ 4 := pow_lt_pow_left₀ hlt hv0 (by norm_num)
    linarith
  have hv3 : 1000 ≤ v ^ 3 := by
    have : (10 : ℝ) ^ 3 ≤ v ^ 3 := by gcongr
    linarith
  set h := 1.22 * v ^ 3 with hhdef
  have hh0 : 0 < h := by positivity
  have hhx : h ≤ 0.122 * x := by rw [hxv, hhdef]; nlinarith
  have h34 : x ^ (3 / 4 : ℝ) = v ^ 3 := rpow34_of hx0
  have h32 : x ^ (3 / 2 : ℝ) = v ^ 6 := rpow32_of hx0
  set c := Real.log (2 * Real.pi) with hc
  have hc1 : 1.8 ≤ c := LeanLab.ChirreHagen2025.Lemma26H.c_lower
  have hc2 : c ≤ 2 := LeanLab.ChirreHagen2025.Lemma26H.c_upper
  have bound := fun y (hy : 1 < y) => abs_le.1 (psi1_explicit_RH_sharp hRH hN h14 hy)
  have b1 := bound (x + h) (by linarith)
  have b0 := bound x (by linarith)
  have bm := bound (x - h) (by linarith)
  have hv6 : v ^ 6 = v ^ 3 * v ^ 3 := by ring
  have hv2 : 0 ≤ v ^ 2 := by positivity
  have p1 : (x + h) ^ (3 / 2 : ℝ) ≤ 1.25 * v ^ 6 := by
    have hle : x + h ≤ (1.0593 * v ^ 2) ^ 2 := by rw [hxv]; nlinarith
    have := rpow32_le_mul (by linarith) (by positivity) hle
    have : (x + h) * (1.0593 * v ^ 2) ≤ 1.122 * v ^ 4 * (1.0593 * v ^ 2) :=
      mul_le_mul_of_nonneg_right (by rw [hxv] at hhx ⊢; linarith) (by positivity)
    nlinarith
  have pm : (x - h) ^ (3 / 2 : ℝ) ≤ v ^ 6 := by
    have hle : x - h ≤ (v ^ 2) ^ 2 := by rw [hxv]; nlinarith
    have := rpow32_le_mul (by linarith) hv2 hle
    have : (x - h) * v ^ 2 ≤ v ^ 4 * v ^ 2 :=
      mul_le_mul_of_nonneg_right (by rw [hxv] at hhx ⊢; linarith) hv2
    nlinarith
  rw [h32] at b0
  obtain ⟨u1, -⟩ := psi1_diff_bounds hx0 hh0
  obtain ⟨-, u2⟩ := psi1_diff_bounds (show 0 ≤ x - h by linarith) hh0
  rw [sub_add_cancel] at u2
  rw [h34, abs_le]
  have hhv : h * v ^ 3 = 1.22 * v ^ 6 := by rw [hhdef, hv6]; ring
  have hh2 : h ^ 2 = 1.4884 * v ^ 6 := by rw [hhdef, hv6]; ring
  have em : (x - h) ^ 2 / 2 = x ^ 2 / 2 - x * h + h ^ 2 / 2 := by ring
  have ep : (x + h) ^ 2 / 2 = x ^ 2 / 2 + x * h + h ^ 2 / 2 := by ring
  have emc : (x - h) * c = x * c - h * c := by ring
  have epc : (x + h) * c = x * c + h * c := by ring
  have hc0 : 1.8 * h ≤ h * c := by
    have := mul_le_mul_of_nonneg_left hc1 hh0.le; linarith
  have hh3 : 1220 ≤ h := by rw [hhdef]; linarith
  constructor
  · -- lower: h ψ(x) ≥ ψ₁(x) - ψ₁(x - h)
    have hm1 : h * (x - 1.23 * v ^ 3) = h * x - 1.23 * (h * v ^ 3) := by ring
    have hc3 : h * c ≤ 2 * h := by
      have := mul_le_mul_of_nonneg_left hc2 hh0.le; linarith
    have hv6' : 2440 * v ^ 3 ≤ 2.44 * v ^ 6 := by
      have := mul_le_mul_of_nonneg_left hv3 (by positivity : (0 : ℝ) ≤ v ^ 3); rw [hv6]; linarith
    have hh4 : 2 * h = 2.44 * v ^ 3 := by rw [hhdef]; ring
    have key : h * (x - 1.23 * v ^ 3) ≤ h * psiF x := by
      have hxh : x * h = h * x := by ring
      exact lower_arith u2 b0.1 bm.2 pm hh2 hc3 hh4 hv6' hv3 hhv
    have := le_of_mul_le_mul_left key hh0
    linarith only [this]
  · -- upper: h ψ(x) ≤ ψ₁(x + h) - ψ₁(x)
    have hm1 : h * (x + 1.23 * v ^ 3) = h * x + 1.23 * (h * v ^ 3) := by ring
    have key : h * psiF x ≤ h * (x + 1.23 * v ^ 3) := by
      have hxh : x * h = h * x := by ring
      exact upper_arith u1 b0.1 b1.2 p1 hh2 hc0 hh3 hhv (by positivity)
    have := le_of_mul_le_mul_left key hh0
    rw [sub_le_iff_le_add']; exact this

end LeanLab.PNTPort.ExplicitPsi1.Trivial
