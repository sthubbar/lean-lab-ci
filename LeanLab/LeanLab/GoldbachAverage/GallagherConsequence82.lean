import LeanLab.GoldbachAverage.Variance82
import LeanLab.GoldbachAverage.ThetaLemma1Full

/-!
Elementary consequences of the variance input in P0051 Theorem 2.
Source: arXiv 2110.14250v2 page 20, the final step of Theorem 6.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp82
open MeasureTheory Complex Finset Filter
open GSInputs ThetaLayers

/-- The sixth geometric moment controls the tails in Theorem 2 eq. 19, page 4. -/
theorem sixth_geometric_moment :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * ((j : ℝ) + 1) ^ 6) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 6
    (r := (1 / 2 : ℝ)) (by norm_num)
  have ht := (summable_nat_add_iff 1).mpr hs
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using ht

/-- A dilation contributes at most its sixth power to the logarithmic variance weight.
Source: the geometric tail substitution at the end of the proof on page 20. -/
theorem dilated_power_log {a x j : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (hx : 2 ≤ x) (hj : 1 ≤ j) :
    (j * x) ^ a * Real.log (j * x) ^ 4 ≤
      j ^ 6 * (x ^ a * (1 + Real.log x) ^ 4) := by
  have hx0 : 0 < x := by linarith
  have hj0 : 0 < j := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogj : 0 ≤ Real.log j := Real.log_nonneg hj
  have hl : Real.log (j * x) ≤ j * (1 + Real.log x) := by
    rw [Real.log_mul (ne_of_gt hj0) (ne_of_gt hx0)]
    have h1 := Real.log_le_self hj0.le
    have h2 := mul_le_mul_of_nonneg_right hj hlogx
    nlinarith
  have hp : j ^ a ≤ j ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hj ha2
  rw [Real.rpow_two] at hp
  have hl0 : 0 ≤ Real.log (j * x) := Real.log_nonneg (by nlinarith)
  rw [Real.mul_rpow hj0.le hx0.le]
  calc j ^ a * x ^ a * Real.log (j * x) ^ 4
      ≤ j ^ 2 * x ^ a * (j * (1 + Real.log x)) ^ 4 := by gcongr
    _ = j ^ 6 * (x ^ a * (1 + Real.log x) ^ 4) := by ring

/-- The norm square of the positive index Fourier series is even.
Source: P0051 page 8, the symmetric form used in Theorem 2. -/
theorem psi_error_norm_even (r α : ℝ) :
    ‖PsiGen r (-α) - IGen r (-α)‖ = ‖PsiGen r α - IGen r α‖ := by
  have he (u : ℝ) : eAdd (-u) = (starRingEnd ℂ) (eAdd u) := by
    simpa only [eAdd_eq_e] using LeanLab.PNTPort.LargeSieve.e_neg u
  have hp : PsiGen r (-α) = (starRingEnd ℂ) (PsiGen r α) := by
    simp only [PsiGen, Complex.conj_tsum]
    apply tsum_congr
    intro n
    rw [neg_mul, he]
    simp
  have hi : IGen r (-α) = (starRingEnd ℂ) (IGen r α) := by
    simp only [IGen, Complex.conj_tsum]
    apply tsum_congr
    intro n
    split_ifs <;> simp_all [neg_mul, he]
  rw [hp, hi, ← map_sub, norm_conj]

/-- The local symmetric integral is twice W, at the reciprocal half width.
Source: P0051 eq. 19 page 4 and the symmetry on page 8. -/
theorem symmetric_integral_eq_W (N : ℕ) (hN : 2 ≤ N) (ξ : ℝ) (hξ : 0 < ξ) :
    (∫ α in (-ξ)..ξ,
      ‖PsiGen (Real.exp (-(1 / (N : ℝ)))) α -
        IGen (Real.exp (-(1 / (N : ℝ)))) α‖ ^ 2) = 2 * W N (1 / (2 * ξ)) := by
  set r := Real.exp (-(1 / (N : ℝ)))
  set f : ℝ → ℝ := fun α => ‖PsiGen r α - IGen r α‖ ^ 2
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [Real.exp_lt_one_iff]
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hp := one_div_pos.mpr hNr
    linarith
  have hf : Continuous f := (continuous_psi_sub_I hr0 hr1).norm.pow 2
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-ξ) 0) (hf.intervalIntegrable (μ := volume) 0 ξ)
  have he : (∫ α in (-ξ)..0, f α) = ∫ α in (0 : ℝ)..ξ, f α := by
    have hh := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := ξ)
    simp only [neg_zero] at hh
    rw [← hh]
    apply intervalIntegral.integral_congr
    intro α _
    dsimp [f]
    rw [psi_error_norm_even]
  change (∫ α in (-ξ)..ξ, f α) = _
  rw [← hs, he]
  dsimp [W]
  have hwidth : 1 / (2 * (1 / (2 * ξ))) = ξ := by field_simp
  rw [hwidth]
  dsimp [f, r]
  ring

/-- Theorem 2 local W control implies the mean square input used by the layer proof.
Source: P0051 page 20, last step of the proof of Theorem 6. -/
theorem local_of_W {a : ℝ} (ha : 0 ≤ a)
    (hW : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 1 ≤ h → h ≤ N →
      W N h ≤ K * (N : ℝ) ^ a * (1 + Real.log N) ^ 4 / h) :
    ThetaLemma1Full (a / 2) := by
  obtain ⟨K, hK, hb⟩ := hW
  refine ⟨8 * K + 324, by positivity, fun N hN ξ hξlo hξhi => ?_⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξlo
  have hh1 : 1 ≤ 1 / (2 * ξ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hhN : 1 / (2 * ξ) ≤ (N : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)).mp hξlo
    nlinarith
  have hw := hb N hN (1 / (2 * ξ)) hh1 hhN
  have hs := symmetric_integral_eq_W N hN ξ hξ0
  have hp : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow (by linarith) ha
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL : 1 ≤ (1 + Real.log N) ^ 4 := one_le_pow₀ (by linarith)
  have hNr1 : 1 ≤ N := by omega
  have hr0 : 0 < Real.exp (-(1 / (N : ℝ))) := Real.exp_pos _
  have hr1 : Real.exp (-(1 / (N : ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hp := one_div_pos.mpr hN0
    linarith
  have hc1 := ((continuous_psi_sub_I hr0 hr1).norm.pow 2).intervalIntegrable
    (μ := volume) (-ξ) ξ
  have hc2 := (LeanLab.LZCesaroShort.continuous_St_sub hNr1).intervalIntegrable
    (μ := volume) (-ξ) ξ
  have hpt : ∀ α ∈ Set.Icc (-ξ) ξ,
      ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2 ≤
        2 * ‖PsiGen (Real.exp (-(1 / (N : ℝ)))) α -
          IGen (Real.exp (-(1 / (N : ℝ)))) α‖ ^ 2 + 162 := by
    intro α hα
    have hαabs : |α| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hα.1], by linarith [hα.2]⟩
    have hI := norm_iGen_sub_le hNr1 hαabs
    have htri := norm_add_le
      (PsiGen (Real.exp (-(1 / (N : ℝ)))) α - IGen (Real.exp (-(1 / (N : ℝ)))) α)
      (IGen (Real.exp (-(1 / (N : ℝ)))) α - 1 / LeanLab.LZCesaroShort.zz N α)
    rw [sub_add_sub_cancel] at htri
    have hid : PsiGen (Real.exp (-(1 / (N : ℝ)))) α - 1 / LeanLab.LZCesaroShort.zz N α =
        LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α := by rw [psiGen_eq_St]
    rw [hid] at htri
    have hnn := norm_nonneg (IGen (Real.exp (-(1 / (N : ℝ)))) α -
      1 / LeanLab.LZCesaroShort.zz N α)
    have hnorm : ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ≤
        ‖PsiGen (Real.exp (-(1 / (N : ℝ)))) α -
          IGen (Real.exp (-(1 / (N : ℝ)))) α‖ + 9 := by linarith
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (‖PsiGen (Real.exp (-(1 / (N : ℝ)))) α -
      IGen (Real.exp (-(1 / (N : ℝ)))) α‖ - 9)]
  have hm := intervalIntegral.integral_mono_on (show -ξ ≤ ξ by linarith)
    hc2 ((hc1.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add (hc1.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul] at hm
  change (∫ α in (-ξ)..ξ, ‖LeanLab.LZCesaroShort.St N α - 1 / LeanLab.LZCesaroShort.zz N α‖ ^ 2) ≤
    2 * (∫ α in (-ξ)..ξ, ‖PsiGen (Real.exp (-(1 / (N : ℝ)))) α - IGen (Real.exp (-(1 / (N : ℝ)))) α‖ ^ 2) + (ξ - -ξ) * 162 at hm
  rw [hs] at hm
  have hw' : W N (1 / (2 * ξ)) ≤ 2 * K * (N : ℝ) ^ a * ξ * (1 + Real.log N) ^ 4 := by
    convert hw using 1 <;> simp only [div_div_eq_mul_div, div_one] <;> ring
  have hprod : 1 ≤ (N : ℝ) ^ a * (1 + Real.log N) ^ 4 := one_le_mul_of_one_le_of_one_le hp hL
  have hconst := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 324 * ξ by positivity)
  rw [show 2 * (a / 2) = a by ring]
  nlinarith

end LeanLab.GoldbachAverage.Decomp82

namespace LeanLab.GoldbachAverage.Decomp82
open MeasureTheory Complex Finset Filter
open GSInputs ThetaLayers

/-- Substituting H and J into Theorem 2 eq. 19, P0051 page 20.
CONDITIONAL ON the exact cited inputs. -/
theorem W_from_variances (hG : GrosswaldPsiTheta) (hJ : GSFullVariance)
    (hW : GSGallagherVarianceBound) (hlo : 1 / 2 < Theta) (hhi : Theta < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 1 ≤ h → h ≤ N →
      W N h ≤ K * (N : ℝ) ^ (2 * Theta) * (1 + Real.log N) ^ 4 / h := by
  obtain ⟨CH, hCH, hH⟩ := H_of_grosswald hG hlo hhi
  obtain ⟨CJ, hCJ, hJb⟩ := hJ hlo hhi
  obtain ⟨CW, hCW, hWb⟩ := hW
  set a := 2 * Theta with ha
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have ha2 : a ≤ 2 := by dsimp [a]; linarith
  set KH := CH * (2 : ℝ) ^ (a + 1) with hKHdef
  have hKH : 0 ≤ KH := by dsimp [KH]; positivity
  have hCHKH : CH ≤ KH := by
    have hp : 1 ≤ (2 : ℝ) ^ (a + 1) := Real.one_le_rpow (by norm_num) (by linarith)
    exact le_mul_of_one_le_right hCH hp
  have hHone : ∀ x : ℝ, 1 ≤ x → InghamTheta.H x ≤ KH * x ^ (a + 1) := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith
    by_cases hx2 : 2 ≤ x
    · exact (hH x hx2).trans (mul_le_mul_of_nonneg_right hCHKH (by positivity))
    · have hm := intervalIntegral.integral_mono_interval (μ := volume)
        (le_refl (0 : ℝ)) hx0 (show x ≤ 2 by linarith)
        (Filter.Eventually.of_forall fun t : ℝ => sq_nonneg (Chebyshev.psi t - t))
        (psi_error_square_integrable (x := 2) (by norm_num))
      change InghamTheta.H x ≤ InghamTheta.H 2 at hm
      have hh := hH 2 (by norm_num)
      have hp : 1 ≤ x ^ (a + 1) := Real.one_le_rpow hx (by linarith)
      exact (hm.trans hh).trans (le_mul_of_one_le_right hKH hp)
  set S := ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * ((j : ℝ) + 1) ^ 6 with hSdef
  have hS : 0 ≤ S := tsum_nonneg (fun _ => by positivity)
  refine ⟨CW * (KH + KH * S + CJ * S + 1), by positivity, fun N hN h hh hhN => ?_⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hh0 : 0 < h := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  set P := (N : ℝ) ^ a with hPdef
  set L := (1 + Real.log N) ^ 4 with hLdef
  have hP : 0 ≤ P := by positivity
  have hL : 1 ≤ L := one_le_pow₀ (by linarith)
  have hL0 : 0 ≤ L := by positivity
  have hNP : (N : ℝ) ≤ P := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ N) ha1)
  obtain ⟨hsH, hsJ, hw⟩ := hWb N hN h hh hhN
  have hsumH : (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * InghamTheta.H (((j : ℝ) + 1) * N)) ≤
      KH * (P * N) * S := by
    have hm := hsH.tsum_le_tsum (g := fun j : ℕ =>
      (KH * (P * N)) * ((1 / 2 : ℝ) ^ (j + 1) * ((j : ℝ) + 1) ^ 6))
      (fun j => ?_) (sixth_geometric_moment.mul_left (KH * (P * N)))
    · simpa only [tsum_mul_left, ← hSdef] using hm
    · have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
      have harg : 1 ≤ ((j : ℝ) + 1) * N := by nlinarith
      have hp : ((j : ℝ) + 1) ^ (a + 1) ≤ ((j : ℝ) + 1) ^ (6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hj (by linarith)
      norm_num at hp
      have he : (((j : ℝ) + 1) * N) ^ (a + 1) =
          ((j : ℝ) + 1) ^ (a + 1) * (P * N) := by
        rw [Real.mul_rpow (by positivity) hN0.le, Real.rpow_add hN0, Real.rpow_one]
      calc (1 / 2 : ℝ) ^ (j + 1) * InghamTheta.H (((j : ℝ) + 1) * N)
          ≤ (1 / 2 : ℝ) ^ (j + 1) * (KH * ((((j : ℝ) + 1) * N) ^ (a + 1))) := by
            gcongr
            exact hHone _ harg
        _ ≤ (1 / 2 : ℝ) ^ (j + 1) * (KH * (((j : ℝ) + 1) ^ 6 * (P * N))) := by
          rw [he]
          gcongr
        _ = _ := by ring
  have hsumJ : (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * GSInputs.J (((j : ℝ) + 1) * N) h) ≤
      CJ * h * (P * L) * S := by
    have hm := hsJ.tsum_le_tsum (g := fun j : ℕ =>
      (CJ * h * (P * L)) * ((1 / 2 : ℝ) ^ (j + 1) * ((j : ℝ) + 1) ^ 6))
      (fun j => ?_) (sixth_geometric_moment.mul_left (CJ * h * (P * L)))
    · simpa only [tsum_mul_left, ← hSdef] using hm
    · have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
      have harg : 2 ≤ ((j : ℝ) + 1) * N := by nlinarith
      have hharg : h ≤ ((j : ℝ) + 1) * N := by nlinarith
      have hd := dilated_power_log (by linarith : 0 ≤ a) ha2 hNr hj
      calc (1 / 2 : ℝ) ^ (j + 1) * GSInputs.J (((j : ℝ) + 1) * N) h
          ≤ (1 / 2 : ℝ) ^ (j + 1) *
            (CJ * h * ((((j : ℝ) + 1) * N) ^ a * Real.log (((j : ℝ) + 1) * N) ^ 4)) := by
            have hjb := hJb (((j : ℝ) + 1) * N) h harg hh hharg
            have := mul_le_mul_of_nonneg_left hjb (show 0 ≤ (1 / 2 : ℝ) ^ (j + 1) by positivity)
            convert this using 1 <;> ring
        _ ≤ (1 / 2 : ℝ) ^ (j + 1) * (CJ * h * (((j : ℝ) + 1) ^ 6 * (P * L))) := by
          gcongr
        _ = _ := by ring
  have hHh : InghamTheta.H h / h ^ 2 ≤ KH * P * L / h := by
    have hhP : h ^ a ≤ P := Real.rpow_le_rpow hh0.le hhN (by linarith)
    have h1 := hHone h hh
    rw [Real.rpow_add hh0, Real.rpow_one] at h1
    have h2 : InghamTheta.H h ≤ KH * P * h := by
      calc InghamTheta.H h ≤ KH * (h ^ a * h) := h1
        _ ≤ KH * (P * h) := by gcongr
        _ = _ := by ring
    have h3 : KH * P * h ≤ KH * P * L * h :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg hKH hP) hL) hh0.le
    apply (div_le_iff₀ (by positivity : 0 < h ^ 2)).mpr
    have he : KH * P * L / h * h ^ 2 = KH * P * L * h := by field_simp
    rw [he]
    exact h2.trans h3
  have hHs : (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * InghamTheta.H (((j : ℝ) + 1) * N)) /
      (N : ℝ) ^ 2 ≤ KH * S * P * L / h := by
    have ht : KH * (P * N) * S * h ≤ KH * S * P * L * (N : ℝ) ^ 2 := by
      have hb : h ≤ L * N := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ KH * S * P * N by positivity)
      nlinarith
    apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) ^ 2)).mpr
    rw [div_mul_eq_mul_div]
    have hb := mul_le_mul_of_nonneg_right hsumH hh0.le
    exact (le_div_iff₀ hh0).mpr (hb.trans ht)
  have hJs : (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * GSInputs.J (((j : ℝ) + 1) * N) h) / h ^ 2 ≤
      CJ * S * P * L / h := by
    apply (div_le_iff₀ (by positivity : 0 < h ^ 2)).mpr
    have he : CJ * S * P * L / h * h ^ 2 = CJ * h * (P * L) * S := by field_simp
    rw [he]
    exact hsumJ
  have hNh : (N : ℝ) / h ^ 2 ≤ P * L / h := by
    apply (div_le_iff₀ (by positivity : 0 < h ^ 2)).mpr
    have he : P * L / h * h ^ 2 = P * L * h := by field_simp
    rw [he]
    have hPL : P ≤ P * L := le_mul_of_one_le_right hP hL
    have hPLh : P * L ≤ P * L * h := le_mul_of_one_le_right (by positivity) hh
    exact hNP.trans (hPL.trans hPLh)
  have hb := add_le_add (add_le_add (add_le_add hHh hHs) hJs) hNh
  have hm := mul_le_mul_of_nonneg_left hb hCW
  refine hw.trans (hm.trans (le_of_eq ?_))
  dsimp [P, L]
  ring

/-- Theorem 6 norm error from its H, GSInputs.J and Gallagher inputs, P0051 page 20.
CONDITIONAL ON the three named inputs. -/
theorem error_of_variance_inputs (hG : GrosswaldPsiTheta) (hJ : GSFullVariance)
    (hW : GSGallagherVarianceBound) : GSCor2.BHMSTheorem6E := by
  intro hlo hhi
  have hl := local_of_W (a := 2 * Theta) (by linarith)
    (W_from_variances hG hJ hW hlo hhi)
  have hf : ThetaLemma1Full Theta := by
    convert hl using 1 <;> ring
  exact bhms_of_full hf hlo hhi

end LeanLab.GoldbachAverage.Decomp82
