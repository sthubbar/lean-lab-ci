/-
P0076 analytic leaves for the four main theorem assemblies.
Every declaration in this file is unresolved and CONDITIONAL.
No leaf is certified by its cited source or by compilation with sorryAx.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.BinaryBridge
import LeanLab.Teravainen2016.ProgressionLifting
import LeanLab.Teravainen2016.DyadicApproximation

namespace LeanLab.Teravainen2016

section Teravainen2016_chiExists

open Finset
open scoped Classical

/-! ## The character `eC` -/

private theorem eC_norm_one (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

private theorem eC_add' (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem eC_conj' (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem eC_nat_mul' (k : ℕ) (x : ℝ) : eC ((k : ℝ) * x) = (eC x) ^ k := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem eC_int_one (m : ℤ) : eC ((m : ℝ)) = 1 := by
  rw [show eC ((m : ℝ)) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) from rfl]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) =
    (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

private theorem eC_add_int (y : ℝ) (m : ℤ) : eC (y + (m : ℝ)) = eC y := by
  rw [eC_add', eC_int_one, mul_one]


private theorem Kf_nonneg (J : ℕ) (x : ℝ) : 0 ≤ ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2) := by
  have h : (0 : ℝ) ≤ ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2 := sq_nonneg _
  positivity

private theorem continuous_eC_mul (c : ℝ) : Continuous fun x : ℝ => eC (c * x) := by
  have h1 : Continuous fun x : ℝ => ((c * x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)
  exact Complex.continuous_exp.comp (continuous_const.mul h1)

private theorem continuous_Kf (J : ℕ) : Continuous ((fun x : ℝ => ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2))) := by
  have hsum : Continuous fun x : ℝ => ∑ k : Fin J, eC ((k : ℝ) * x) := by
    have h := continuous_finsetSum (M := ℂ) (X := ℝ)
      (f := fun k : Fin J => fun x : ℝ => eC ((k : ℝ) * x)) Finset.univ
      (fun k _ => continuous_eC_mul ((k : ℝ)))
    simpa using h
  exact continuous_const.mul (hsum.norm.pow 2)

private theorem Kf_periodic (J : ℕ) (x : ℝ) : ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * (x + 1)))‖ ^ 2) = ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2) := by
  have h : ∀ k : Fin J, eC ((k : ℝ) * (x + 1)) = eC ((k : ℝ) * x) := by
    intro k
    rw [show ((k : ℝ) * (x + 1)) = ((k : ℝ) * x + ((k : ℤ) : ℝ)) by push_cast; ring,
      eC_add_int]
  simp only [h]

private theorem Kf_even (J : ℕ) (x : ℝ) : ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * (-x)))‖ ^ 2) = ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2) := by
  have h : (∑ k : Fin J, eC ((k : ℝ) * (-x))) =
      (starRingEnd ℂ) (∑ k : Fin J, eC ((k : ℝ) * x)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [eC_conj']
    congr 1
    ring
  rw [h, Complex.norm_conj]

/-! ## Formulas for the two characters -/

private theorem eC_exp_form (m : ℤ) (u : ℝ) :
    eC ((m : ℝ) * u) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * (u : ℂ)) := by
  unfold eC
  congr 1
  push_cast
  ring

private theorem eC_coef_ne (m : ℤ) (hm : m ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  exact mul_ne_zero h1 (by exact_mod_cast (Int.cast_ne_zero.mpr hm))

/-- The integral of a character over a symmetric interval about `x`. -/
private theorem integral_eC (m : ℤ) (x a : ℝ) :
    ∫ u in (x - a)..(x + a), eC ((m : ℝ) * u) =
      eC ((m : ℝ) * x) *
        (if m = 0 then (2 * a : ℂ)
         else (eC ((m : ℝ) * a) - eC (-((m : ℝ) * a))) /
           (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [if_pos rfl]
    have hzero : ∀ u : ℝ, eC (((0 : ℤ) : ℝ) * u) = 1 := by
      intro u; simp [eC]
    simp only [hzero, intervalIntegral.integral_const, one_mul]
    rw [show (x + a - (x - a) : ℝ) = 2 * a by ring, Complex.real_smul]
    push_cast
    ring
  · rw [if_neg hm]
    have heq : (fun u : ℝ => eC ((m : ℝ) * u)) =
        (fun u : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * (u : ℂ))) :=
      funext (eC_exp_form m)
    rw [heq, integral_exp_mul_complex (eC_coef_ne m hm)]
    have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * ((x + a : ℝ) : ℂ)) =
        eC ((m : ℝ) * (x + a)) := (eC_exp_form m (x + a)).symm
    have h2 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * ((x - a : ℝ) : ℂ)) =
        eC ((m : ℝ) * (x - a)) := (eC_exp_form m (x - a)).symm
    rw [h1, h2, show (m : ℝ) * (x + a) = (m : ℝ) * x + (m : ℝ) * a by ring,
      show (m : ℝ) * (x - a) = (m : ℝ) * x + (-((m : ℝ) * a)) by ring, eC_add', eC_add']
    ring

/-- The integral of a character over a full period. -/
private theorem integral_eC_unit (m : ℤ) :
    ∫ u in (0 : ℝ)..1, eC ((m : ℝ) * u) = if m = 0 then 1 else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [if_pos rfl]
    have hzero : ∀ u : ℝ, eC (((0 : ℤ) : ℝ) * u) = 1 := by
      intro u; simp [eC]
    simp only [hzero, intervalIntegral.integral_const]
    norm_num
  · rw [if_neg hm]
    have heq : (fun u : ℝ => eC ((m : ℝ) * u)) =
        (fun u : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * (u : ℂ))) :=
      funext (eC_exp_form m)
    rw [heq, integral_exp_mul_complex (eC_coef_ne m hm)]
    have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← eC_exp_form m 1, show (m : ℝ) * (1 : ℝ) = (m : ℝ) by ring, eC_int_one]
    have h0 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * ((0 : ℝ) : ℂ)) = 1 := by
      simp
    rw [h1, h0, sub_self, zero_div]

/-! ## The Dirichlet bound and the Fejér tail
(copied verbatim from `results/Teravainen2016-MainInputs-wip-flattop.lean`, session 20261105T2014Z) -/

private theorem eC_re_w (t : ℝ) : (eC t).re = Real.cos (2 * Real.pi * t) := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re]

private theorem eC_im_w (t : ℝ) : (eC t).im = Real.sin (2 * Real.pi * t) := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_im]

private theorem norm_one_sub_eC (t : ℝ) : ‖1 - eC t‖ = 2 * |Real.sin (Real.pi * t)| := by
  have hsq : ‖1 - eC t‖ ^ 2 = (2 * |Real.sin (Real.pi * t)|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : (1 - eC t).re = 1 - Real.cos (2 * Real.pi * t) := by
      simp [eC_re_w]
    have h2 : (1 - eC t).im = -Real.sin (2 * Real.pi * t) := by
      simp [eC_im_w]
    rw [h1, h2]
    have hc := Real.cos_two_mul' (Real.pi * t)
    have hs := Real.sin_two_mul (Real.pi * t)
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * t)
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring]
    have hsq1 : (2 * |Real.sin (Real.pi * t)|) ^ 2 = 4 * Real.sin (Real.pi * t) ^ 2 := by
      rw [mul_pow, sq_abs]
      norm_num
    have h1c : 1 - Real.cos (2 * (Real.pi * t)) = 2 * Real.sin (Real.pi * t) ^ 2 := by
      linarith [hc, hsc]
    rw [h1c, hsq1, hs]
    nlinarith [hsc]
  have h1 : 0 ≤ ‖1 - eC t‖ := norm_nonneg _
  have h2 : 0 ≤ 2 * |Real.sin (Real.pi * t)| := by positivity
  nlinarith [hsq, h1, h2]

private theorem norm_dirichlet_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (J : ℕ) :
    ‖∑ k ∈ range J, eC ((k : ℝ) * x)‖ ≤ 1 / |Real.sin (Real.pi * x)| := by
  have hne_norm : ‖(1 : ℂ) - eC x‖ = 2 * |Real.sin (Real.pi * x)| := norm_one_sub_eC x
  have hpos : 0 < 2 * |Real.sin (Real.pi * x)| := by
    have : |Real.sin (Real.pi * x)| ≠ 0 := abs_ne_zero.mpr hx
    positivity
  have hne : (1 : ℂ) - eC x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hne_norm
    linarith
  have h1e : eC x ≠ 1 := by
    intro h0
    exact hne (by rw [h0, sub_self])
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ range J) => eC_nat_mul' k x)]
  rw [geom_sum_eq h1e]
  have hden : ‖eC x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
    rw [← norm_neg, neg_sub, hne_norm]
  rw [norm_div, hden]
  have hnum : ‖(eC x) ^ J - 1‖ ≤ 2 := by
    calc ‖(eC x) ^ J - 1‖ ≤ ‖(eC x) ^ J‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, eC_norm_one, norm_one]; norm_num
  calc ‖(eC x) ^ J - 1‖ / (2 * |Real.sin (Real.pi * x)|)
      ≤ 2 / (2 * |Real.sin (Real.pi * x)|) :=
        div_le_div_of_nonneg_right hnum hpos.le
    _ = 1 / |Real.sin (Real.pi * x)| := by
        field_simp

private theorem two_mul_distInt_le_abs_sin (x : ℝ) (hx : distInt x ≤ 1 / 2) :
    2 * distInt x ≤ |Real.sin (Real.pi * x)| := by
  set s := distInt x with hs
  have hs0 : 0 ≤ s := by
    rw [hs]; exact abs_nonneg _
  have hs1 : s ≤ 1 / 2 := by rw [hs]; exact hx
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * s) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · nlinarith [Real.pi_pos, hs1]
  have hval : |Real.sin (Real.pi * x)| = Real.sin (Real.pi * s) := by
    have hround : |x - (round x : ℝ)| = s := by rw [hs]; rfl
    have hpi : Real.pi * x = Real.pi * (x - (round x : ℝ)) + (round x : ℝ) * Real.pi := by ring
    have hsign : |Real.sin (Real.pi * x)|
        = |Real.sin (Real.pi * (x - (round x : ℝ)))| := by
      rw [hpi, Real.sin_add_int_mul_pi, abs_mul]
      have h1 : |((-1 : ℝ) ^ (round x))| = 1 := by
        rw [abs_zpow, abs_neg, abs_one, one_zpow]
      rw [h1, one_mul]
    rw [hsign]
    rcases (abs_eq hs0).mp hround with h | h
    · rw [h, abs_of_nonneg hsin_nonneg]
    · rw [h, mul_neg, Real.sin_neg, abs_neg, abs_of_nonneg hsin_nonneg]
  have hle : Real.pi * s ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos, hx, hs0]
  have h0 : 0 ≤ Real.pi * s := by positivity
  have hmul := Real.mul_le_sin h0 hle
  have hpi := Real.pi_pos
  have : 2 / Real.pi * (Real.pi * s) = 2 * s := by field_simp
  linarith [hmul, this.le, this.ge]

private theorem distInt_pos_of_sin_ne {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) : 0 < distInt x := by
  rcases lt_or_eq_of_le (abs_nonneg (x - (round x : ℝ))) with h | h
  · simpa [distInt] using h
  · exfalso
    apply hx
    have hxr : x = (round x : ℝ) := by
      have h0 : |x - (round x : ℝ)| = 0 := h.symm
      have h1 := abs_eq_zero.mp h0
      linarith
    rw [hxr]
    have hpi : Real.pi * (round x : ℝ) = ((round x : ℤ) : ℝ) * Real.pi := by ring
    rw [hpi, Real.sin_int_mul_pi]

private theorem sin_ne_of_distInt_pos {x : ℝ} (hx : 0 < distInt x) : Real.sin (Real.pi * x) ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h0
  have hxr : x = (n : ℝ) := by
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp at hn
    linarith
  have : distInt x = 0 := by
    rw [hxr]
    unfold distInt
    rw [show round ((n : ℝ)) = n by simp]
    simp
  linarith

private theorem fejer_tail_w {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (hx' : distInt x ≤ 1 / 2)
    (J : ℕ) (hJ : 1 ≤ J) :
    (1 / (J : ℝ)) * ‖∑ k ∈ range J, eC ((k : ℝ) * x)‖ ^ 2
      ≤ 1 / ((J : ℝ) * (2 * distInt x) ^ 2) := by
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hs : 0 < 2 * distInt x := by
    have h := distInt_pos_of_sin_ne hx
    linarith
  have hD := norm_dirichlet_le hx J
  have hsin := two_mul_distInt_le_abs_sin x hx'
  have hinv : 1 / |Real.sin (Real.pi * x)| ≤ 1 / (2 * distInt x) :=
    one_div_le_one_div_of_le hs hsin
  have hle : ‖∑ k ∈ range J, eC ((k : ℝ) * x)‖ ≤ 1 / (2 * distInt x) := le_trans hD hinv
  have hsq : ‖∑ k ∈ range J, eC ((k : ℝ) * x)‖ ^ 2 ≤ (1 / (2 * distInt x)) ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg _) hle
    simpa [pow_two] using h
  calc (1 / (J : ℝ)) * ‖∑ k ∈ range J, eC ((k : ℝ) * x)‖ ^ 2
      ≤ (1 / (J : ℝ)) * (1 / (2 * distInt x)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / ((J : ℝ) * (2 * distInt x) ^ 2) := by
        field_simp

/-! ## `Kf` as a range sum, and its total mass -/


private theorem Kf_tail {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (hx' : distInt x ≤ 1 / 2)
    (J : ℕ) (hJ : 1 ≤ J) :
    ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2) ≤ 1 / ((J : ℝ) * (2 * distInt x) ^ 2) := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => eC ((k : ℝ) * x)) J]
  exact fejer_tail_w hx hx' J hJ

private theorem Kf_expand (J : ℕ) (x : ℝ) :
    ((((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2) : ℝ) : ℂ) =
      (1 / (J : ℂ)) * ∑ p : Fin J × Fin J, eC (((p.2 : ℝ) - (p.1 : ℝ)) * x) := by
  have hsq : (((‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ : ℝ) : ℂ)) ^ 2 = (starRingEnd ℂ) ((∑ k : Fin J, eC ((k : ℝ) * x))) * (∑ k : Fin J, eC ((k : ℝ) * x)) := by
    rw [← Complex.ofReal_pow, Complex.sq_norm]
    exact Complex.normSq_eq_conj_mul_self
  have hconj : (starRingEnd ℂ) ((∑ k : Fin J, eC ((k : ℝ) * x))) = ∑ k : Fin J, eC (((k : ℝ) * (-x))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [eC_conj']
    congr 1
    ring
  push_cast
  rw [hsq, hconj]
  rw [Finset.sum_mul_sum]
  have hterm : ∀ k k' : Fin J,
      eC (((k : ℝ) * (-x))) * eC (((k' : ℝ) * x)) =
        eC (((k' : ℝ) - (k : ℝ)) * x) := by
    intro k k'
    rw [← eC_add']
    congr 1
    ring
  simp only [hterm]
  rw [Fintype.sum_prod_type]

private theorem sum_ite_diag (J : ℕ) :
    ∑ p : Fin J × Fin J, (if p.1 = p.2 then (1 : ℂ) else 0) = (J : ℂ) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  have hinner : ∀ a : Fin J, ∑ b : Fin J, (if a = b then (1 : ℂ) else 0) = 1 := by
    intro a
    rw [Finset.sum_ite_eq]
    simp
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

private theorem Kf_mass (J : ℕ) (hJ : 1 ≤ J) : ∫ u in (0 : ℝ)..1, ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) = 1 := by
  have hcomplex : ((∫ u in (0 : ℝ)..1, ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) : ℝ) : ℂ) = 1 := by
    rw [← intervalIntegral.integral_ofReal]
    have hexp : ∀ u : ℝ, ((((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) : ℝ) : ℂ) =
        (1 / (J : ℂ)) * ∑ p : Fin J × Fin J, eC (((p.2 : ℝ) - (p.1 : ℝ)) * u) :=
      Kf_expand J
    simp only [hexp]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum]
    · have hinner : ∀ p : Fin J × Fin J,
          (∫ u in (0 : ℝ)..1, eC (((p.2 : ℝ) - (p.1 : ℝ)) * u)) =
            if p.1 = p.2 then 1 else 0 := by
        intro p
        have hcoe : ((p.2 : ℝ) - (p.1 : ℝ)) = (((p.2 : ℤ) - (p.1 : ℤ) : ℤ) : ℝ) := by
          push_cast; ring
        rw [hcoe, integral_eC_unit]
        by_cases h : p.1 = p.2
        · rw [if_pos h]
          have hm : ((p.2 : ℤ) - (p.1 : ℤ)) = 0 := by rw [h]; simp
          rw [if_pos hm]
        · rw [if_neg h]
          have hm : ((p.2 : ℤ) - (p.1 : ℤ)) ≠ 0 := by
            intro h0
            apply h
            have h1 : (p.2 : ℤ) = (p.1 : ℤ) := by omega
            exact Fin.ext (by omega)
          rw [if_neg hm]
      rw [Finset.sum_congr rfl (fun p _ => hinner p), sum_ite_diag]
      have hJne : (J : ℂ) ≠ 0 := by
        have : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
        exact_mod_cast (ne_of_gt this)
      field_simp
    · intro p _
      exact Continuous.intervalIntegrable (by unfold eC; fun_prop) 0 1
  exact Complex.ofReal_injective hcomplex

/-! ## The interval integral of a periodic function -/

private theorem Kf_periodic_fn (J : ℕ) : Function.Periodic ((fun x : ℝ => ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2))) 1 := fun x => Kf_periodic J x

private theorem integral_shift_one (J : ℕ) (c d : ℝ) :
    ∫ u in (c + 1)..(d + 1), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) = ∫ u in c..d, ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) := by
  have h := intervalIntegral.integral_comp_add_left (f := fun u => ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) 1 (a := c) (b := d)
  rw [show (1 + c : ℝ) = c + 1 by ring, show (1 + d : ℝ) = d + 1 by ring] at h
  rw [← h]
  have hper : ∀ y : ℝ, ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * (1 + y)))‖ ^ 2) = ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * y))‖ ^ 2) := by
    intro y
    rw [add_comm]
    exact Kf_periodic J y
  simp only [hper]

private theorem Kf_interval_one (J : ℕ) (hJ : 1 ≤ J) (c : ℝ) :
    ∫ u in c..c + 1, ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) = 1 := by
  have h := (Kf_periodic_fn J).intervalIntegral_add_eq c 0
  rw [show ((0 : ℝ) + 1) = 1 by norm_num, Kf_mass J hJ] at h
  exact h

/-- The pointwise bound off the set of integers: `Kf` is `O(1/(J r²))` at distance `r`. -/
private theorem Kf_le_of_away (J : ℕ) (hJ : 1 ≤ J) {u r : ℝ} (hr : 0 < r) (h : r ≤ distInt u) :
    ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) ≤ 1 / ((J : ℝ) * (2 * r) ^ 2) := by
  have hd0 : 0 < distInt u := lt_of_lt_of_le hr h
  have hsin : Real.sin (Real.pi * u) ≠ 0 := sin_ne_of_distInt_pos hd0
  have hhalf : distInt u ≤ 1 / 2 := abs_sub_round u
  refine (Kf_tail hsin hhalf J hJ).trans ?_
  have hpos : 0 < (J : ℝ) * (2 * r) ^ 2 := by
    have : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
    positivity
  have hle : (2 * r) ^ 2 ≤ (2 * distInt u) ^ 2 := by
    have h2r : (0:ℝ) ≤ 2 * r := by linarith
    exact pow_le_pow_left₀ h2r (by linarith) 2
  have h2 : (J : ℝ) * (2 * r) ^ 2 ≤ (J : ℝ) * (2 * distInt u) ^ 2 := by
    apply mul_le_mul_of_nonneg_left hle (by positivity)
  exact one_div_le_one_div_of_le hpos h2


/-! ## The bump `g(x) = ∫_{x-a}^{x+a} Kf` -/

/-- Distance to the nearest integer is 1-Lipschitz. -/
private theorem distInt_le_distInt_add_abs (x y : ℝ) : distInt y ≤ distInt x + |y - x| := by
  have h1 : distInt y ≤ |y - ((round x : ℤ) : ℝ)| := by
    unfold distInt
    exact round_le y (round x)
  have h2 : |y - ((round x : ℤ) : ℝ)| ≤ |y - x| + |x - ((round x : ℤ) : ℝ)| := by
    have h3 : y - ((round x : ℤ) : ℝ) = (y - x) + (x - ((round x : ℤ) : ℝ)) := by ring
    rw [h3]
    exact abs_add_le _ _
  have h3 : |x - ((round x : ℤ) : ℝ)| = distInt x := rfl
  rw [h3] at h2
  linarith


private theorem bump_nonneg (J : ℕ) (a x : ℝ) (ha : 0 ≤ a) : 0 ≤ (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro u _
  exact Kf_nonneg J u

private theorem bump_int' (J : ℕ) (a x : ℝ) : IntervalIntegrable ((fun x : ℝ => ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2))) MeasureTheory.volume (x - a) (x + a) :=
  (continuous_Kf J).intervalIntegrable _ _

private theorem bump_le_one (J : ℕ) (hJ : 1 ≤ J) {a : ℝ} (ha : 0 ≤ a) (h2a : 2 * a ≤ 1) (x : ℝ) :
    (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) ≤ 1 := by
  have hmono : (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) ≤ ∫ u in (x - a)..(x - a + 1), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) := by
    refine intervalIntegral.integral_mono_interval le_rfl (by linarith)
      (show x + a ≤ x - a + 1 by linarith)
      (Filter.Eventually.of_forall (fun u => Kf_nonneg J u)) ?_
    exact (continuous_Kf J).intervalIntegrable _ _
  refine hmono.trans ?_
  rw [show (x - a + 1 : ℝ) = (x - a) + 1 by ring]
  exact le_of_eq (Kf_interval_one J hJ (x - a))

private theorem bump_even (J : ℕ) (a x : ℝ) : (∫ u in ((-x) - a)..((-x) + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) = (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) := by
  have h := intervalIntegral.integral_comp_neg (f := fun u => ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) (a := x - a) (b := x + a)
  rw [show (-(x + a) : ℝ) = -x - a by ring, show (-(x - a) : ℝ) = -x + a by ring] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  exact Kf_even J u

private theorem bump_periodic (J : ℕ) (a x : ℝ) : (∫ u in ((x + 1) - a)..((x + 1) + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) = (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) := by
  have h := integral_shift_one J (x - a) (x + a)
  rw [show (x - a + 1 : ℝ) = x + 1 - a by ring,
    show (x + a + 1 : ℝ) = x + 1 + a by ring] at h
  exact h

/-- `distInt` is invariant under integer translation. -/
private theorem distInt_intCast_add (t : ℝ) (n : ℤ) : distInt ((n : ℝ) + t) = distInt t := by
  have h : ((n : ℝ) + t) = t + (n : ℝ) := by ring
  rw [h, distInt, round_add_intCast]
  push_cast
  rw [show t + (n : ℝ) - ((round t : ℝ) + (n : ℝ)) = t - (round t : ℝ) by ring]
  rfl

/-- On `[0, 1]` the distance to the nearest integer is `min t (1 - t)`. -/
private theorem distInt_eq_min {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : distInt t = min t (1 - t) := by
  unfold distInt
  rw [abs_sub_round_eq_min]
  have hlt : t < 1 ∨ t = 1 := lt_or_eq_of_le h1
  rcases hlt with hlt | rfl
  · have hf : Int.fract t = t := by
      rw [Int.fract_eq_self]
      exact ⟨h0, hlt⟩
    rw [hf]
  · have hf1 : Int.fract (1 : ℝ) = 0 := by simp
    rw [hf1]
    norm_num

/-- A point at distance at least `a - η` from `x`, with `x` within `η` of an integer, is at
distance at least `a - η` from the integers. -/
private theorem distInt_ge_of_near_int {x u η a : ℝ} (hx : distInt x ≤ η) (haη : η < a)
    (ha : a ≤ 1 / 2 + η) (hu1 : x + a ≤ u) (hu2 : u ≤ x - a + 1) : a - η ≤ distInt u := by
  set n : ℤ := round x with hn
  have hxn : |x - (n : ℝ)| ≤ η := hx
  have hxn1 : x - (n : ℝ) ≤ η := (abs_le.mp hxn).2
  have hxn2 : -(η) ≤ x - (n : ℝ) := (abs_le.mp hxn).1
  set t : ℝ := u - (n : ℝ) with ht
  have ht0 : a - η ≤ t := by
    have : x + a - (n : ℝ) ≤ u - (n : ℝ) := by linarith
    linarith
  have ht1 : t ≤ 1 - (a - η) := by
    have : u - (n : ℝ) ≤ x - a + 1 - (n : ℝ) := by linarith
    linarith
  have hδ0 : 0 < a - η := by linarith
  have hδ : a - η ≤ 1 / 2 := by linarith
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le_one : t ≤ 1 := by linarith
  have hkey : distInt u = distInt t := by
    rw [show u = (n : ℝ) + t by rw [ht]; ring]
    exact distInt_intCast_add t n
  rw [hkey, distInt_eq_min ht_nonneg ht_le_one]
  exact le_min ht0 (by linarith)

/-- In the `2η`-separated regime the bump is at most `2a/(J η²)`. -/
private theorem bump_far {J : ℕ} (hJ : 1 ≤ J) {a η x : ℝ} (ha : 0 < a) (hη : 0 < η)
    (ha2 : a ≤ 2 * η) (ha3 : a ≤ 3 * η / 2) (h2η : 2 * η < distInt x) :
    (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) ≤ 2 * a / ((J : ℝ) * η ^ 2) := by
  set C : ℝ := 1 / ((J : ℝ) * η ^ 2) with hC
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hηC : 0 < (J : ℝ) * η ^ 2 := by positivity
  have hpt : ∀ u ∈ Set.Icc (x - a) (x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) ≤ C := by
    intro u hu
    have h1 : |u - x| ≤ a := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [hu.2]
      · linarith [hu.1]
    have h2 : 2 * η - a ≤ distInt u := by
      have h3 := distInt_le_distInt_add_abs u x
      have h4 : |x - u| = |u - x| := abs_sub_comm x u
      linarith
    have h4 : η / 2 ≤ distInt u := by linarith
    have h5 := Kf_le_of_away J hJ (u := u) (r := η / 2) (by linarith) (by linarith)
    rw [hC]
    refine h5.trans (le_of_eq ?_)
    congr 2
    ring
  have hmono : (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) ≤ ∫ _u in (x - a)..(x + a), C := by
    exact intervalIntegral.integral_mono_on (by linarith) (bump_int' J a x)
      intervalIntegrable_const (μ := MeasureTheory.volume) hpt
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]
  have hlen : x + a - (x - a) = 2 * a := by ring
  rw [hlen, hC]
  field_simp

/-- In the `η`-regime the bump is at least `1 - 1/(J η²)`. -/
private theorem bump_near_one {J : ℕ} (hJ : 1 ≤ J) {a η x : ℝ} (ha : 0 < a) (hη : 0 < η)
    (h2a : 2 * a ≤ 1) (h3η2 : 3 * η / 2 ≤ a) (hx : distInt x ≤ η) :
    1 - 1 / ((J : ℝ) * η ^ 2) ≤ (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) := by
  set C : ℝ := 1 / ((J : ℝ) * η ^ 2) with hC
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hηC : 0 < (J : ℝ) * η ^ 2 := by positivity
  have hηa : η < a := by linarith
  have ha12 : a ≤ 1 / 2 + η := by linarith
  have hpt : ∀ u ∈ Set.Icc (x + a) (x - a + 1), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) ≤ C := by
    intro u hu
    have h1 : a - η ≤ distInt u :=
      distInt_ge_of_near_int hx hηa ha12 hu.1 hu.2
    have h4 : η / 2 ≤ distInt u := by linarith
    have h5 := Kf_le_of_away J hJ (u := u) (r := η / 2) (by linarith) (by linarith)
    rw [hC]
    refine h5.trans (le_of_eq ?_)
    congr 2
    ring
  have htail : ∫ u in (x + a)..(x - a + 1), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) ≤ (1 - 2 * a) * C := by
    have hmono : ∫ u in (x + a)..(x - a + 1), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) ≤ ∫ _u in (x + a)..(x - a + 1), C :=
      intervalIntegral.integral_mono_on (by linarith)
        ((continuous_Kf J).intervalIntegrable _ _) intervalIntegrable_const (μ := MeasureTheory.volume) hpt
    refine hmono.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have : x - a + 1 - (x + a) = 1 - 2 * a := by ring
    rw [this]
  have hsplit : (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) + ∫ u in (x + a)..(x - a + 1), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) = 1 := by
    have hint : ∀ p q : ℝ, IntervalIntegrable ((fun x : ℝ => ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * x))‖ ^ 2))) MeasureTheory.volume p q :=
      fun p q => (continuous_Kf J).intervalIntegrable p q
    have h := intervalIntegral.integral_add_adjacent_intervals (a := x - a) (b := x + a)
      (c := x - a + 1) (hint _ _) (hint _ _)
    have hm : (∫ u in (x - a)..(x - a + 1), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) = 1 := by
      have h2 := Kf_interval_one J hJ (x - a)
      rw [show (x - a + 1 : ℝ) = (x - a) + 1 from by ring] at h2
      exact h2
    rw [hm] at h
    rw [show (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) = ∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) from rfl]
    linarith
  have hC1 : (1 - 2 * a) * C ≤ C := by
    apply mul_le_of_le_one_left (by rw [hC]; positivity)
    linarith
  nlinarith [hsplit, htail, hC1]


/-! ## The bump as an exponential sum -/

/-- The Fourier coefficient of the bump at the integer frequency `m`. -/
private theorem bump_coeff_int (J : ℕ) {a x : ℝ} (c : ℝ) :
    (∫ u in (x - a)..(x + a), eC (c * u)) =
      eC (c * x) * (∫ y in (-a)..a, eC (c * y)) := by
  have h := intervalIntegral.integral_comp_add_left (f := fun u => eC (c * u)) x
    (a := -a) (b := a)
  rw [show (x + -a : ℝ) = x - a by ring, show (x + a : ℝ) = x + a by ring] at h
  rw [← h]
  have hpt : ∀ y : ℝ, eC (c * (x + y)) = eC (c * x) * eC (c * y) := by
    intro y
    rw [← eC_add']
    congr 1
    ring
  simp only [hpt]
  rw [intervalIntegral.integral_const_mul]

private theorem bump_expand (J : ℕ) (a x : ℝ) :
    (((∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) : ℝ) : ℂ) = ∑ p : Fin J × Fin J,
      ((1 / (J : ℂ)) * (∫ y in (-a)..a, eC (((p.2 : ℝ) - (p.1 : ℝ)) * y))) *
        eC (((p.2 : ℝ) - (p.1 : ℝ)) * x) := by
  have hint : ∀ p : Fin J × Fin J,
      IntervalIntegrable (fun u : ℝ => eC (((p.2 : ℝ) - (p.1 : ℝ)) * u))
        MeasureTheory.volume (x - a) (x + a) :=
    fun p => Continuous.intervalIntegrable
      (continuous_eC_mul ((p.2 : ℝ) - (p.1 : ℝ))) _ _
  rw [← intervalIntegral.integral_ofReal]
  have hexp : ∀ u : ℝ, ((((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2) : ℝ) : ℂ) =
      (1 / (J : ℂ)) * ∑ p : Fin J × Fin J, eC (((p.2 : ℝ) - (p.1 : ℝ)) * u) :=
    Kf_expand J
  simp only [hexp, Finset.sum_apply]
  rw [intervalIntegral.integral_const_mul (𝕜 := ℂ) (r := (1 / (J : ℂ)))]
  have hsum : (∫ u in (x - a)..(x + a),
        ∑ p : Fin J × Fin J, eC (((p.2 : ℝ) - (p.1 : ℝ)) * u))
      = ∑ p : Fin J × Fin J, ∫ u in (x - a)..(x + a), eC (((p.2 : ℝ) - (p.1 : ℝ)) * u) :=
    intervalIntegral.integral_finsetSum (fun p _ => hint p)
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [bump_coeff_int J ((p.2 : ℝ) - (p.1 : ℝ))]
  ring

/-- The coefficients of the bump expansion have norm at most one. -/
private theorem bump_coeff_norm_le (J : ℕ) (hJ : 1 ≤ J) {a : ℝ} (ha0 : 0 ≤ a) (haJ : 2 * a ≤ J)
    (c : ℝ) :
    ‖(1 / (J : ℂ)) * (∫ y in (-a)..a, eC (c * y))‖ ≤ 1 := by
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hnorm : ‖∫ y in (-a)..a, eC (c * y)‖ ≤ 2 * a := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y : ℝ => eC (c * y)) (a := -a) (b := a)
      (C := 1) (fun y _ => le_of_eq (eC_norm_one (c * y)))
    refine h.trans (le_of_eq ?_)
    rw [one_mul, show |a - -a| = 2 * a from by
      rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]; ring]
  have h1 : ‖(1 / (J : ℂ))‖ = 1 / (J : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [norm_mul, h1]
  have h2 : 1 / (J : ℝ) * (2 * a) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    linarith
  calc 1 / (J : ℝ) * ‖∫ y in (-a)..a, eC (c * y)‖ ≤ 1 / (J : ℝ) * (2 * a) := by
        apply mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ 1 := h2


/-! ## The flat top

The bump at `a = 3η/2` with `J` chosen from `k, η` is a flat-top trigonometric polynomial
with threshold `(η ^ 2 / 16) ^ k`.  Note the quantifier order: **one** bump per `(k, η)`,
carrying the threshold `(η ^ 2 / 16) ^ k` fixed by `k` and `η`.  Asking for one set of
coefficients that works for every `θ > 0` at once is not satisfiable for `η < 1/4`:
the far set `{x | 2η < distInt x}` is then a nonempty open set, `∀ θ > 0` forces the bump
to vanish on it, and a trigonometric polynomial vanishing on an open set is identically
zero, contradicting `1/2 ≤ g` near the origin. -/

private theorem flat_top_exists (k : ℕ) (η : ℝ) (hη : 0 < η) (hη4 : η < 1 / 4) :
    ∃ (Cc : ℕ) (c : Fin Cc → ℂ) (α : Fin Cc → ℝ), (∀ j, ‖c j‖ ≤ (Cc : ℝ)) ∧
      ∃ g : ℝ → ℝ, (∀ x, (g x : ℂ) = ∑ j, c j * eC (α j * x)) ∧
        (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧
        (∀ x, g (-x) = g x) ∧ (∀ x, g (x + 1) = g x) ∧
        (∀ x, distInt x ≤ η → 1 / 2 ≤ g x) ∧
        (∀ x, 2 * η < distInt x → g x ≤ (η ^ 2 / 16) ^ k) := by
  set θ : ℝ := (η ^ 2 / 16) ^ k with hθ_eq
  have hθ0 : 0 < θ := by
    rw [hθ_eq]
    have : 0 < η ^ 2 / 16 := by positivity
    positivity
  have hηθ : 0 < η * θ := mul_pos hη hθ0
  have hη2 : 0 < η ^ 2 := by positivity
  -- choose `J` with `J η ^ 2 ≥ 2` and `3 ≤ J η θ` and `1 ≤ J`
  obtain ⟨J, hJ⟩ := exists_nat_gt (max (2 / η ^ 2) (max (3 / (η * θ)) 1))
  have hJ1 : 1 ≤ J := by
    have h1 : (1 : ℝ) < J := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hJ
    exact le_of_lt (by exact_mod_cast h1)
  have hJa : 2 ≤ (J : ℝ) * η ^ 2 := by
    have h1 : 2 / η ^ 2 < (J : ℝ) := lt_of_le_of_lt (le_max_left _ _) hJ
    rw [div_lt_iff₀ hη2] at h1
    linarith
  have hJb : 3 ≤ (J : ℝ) * η * θ := by
    have h1 : 3 / (η * θ) < (J : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hJ
    rw [div_lt_iff₀ hηθ] at h1
    linarith
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
  set a : ℝ := 3 * η / 2 with ha_eq
  have ha0 : 0 < a := by rw [ha_eq]; positivity
  have ha_nn : 0 ≤ a := le_of_lt ha0
  have h2a : 2 * a ≤ 1 := by rw [ha_eq]; linarith
  have ha_le : a ≤ 3 * η / 2 := le_rfl
  have ha2 : a ≤ 2 * η := by rw [ha_eq]; linarith
  have haJ : 2 * a ≤ (J : ℝ) := by
    have : 2 * a = 3 * η := by rw [ha_eq]; ring
    rw [this]
    nlinarith
  -- the Fourier data
  refine ⟨J * J,
    fun j => (1 / (J : ℂ)) *
      (∫ y in (-a)..a, eC (((((finProdFinEquiv (m := J) (n := J)).symm j).2 : ℝ) -
        (((finProdFinEquiv (m := J) (n := J)).symm j).1 : ℝ)) * y)),
    fun j => (((finProdFinEquiv (m := J) (n := J)).symm j).2 : ℝ) -
      (((finProdFinEquiv (m := J) (n := J)).symm j).1 : ℝ), ?_, (fun x : ℝ => (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2))), ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
  · -- coefficient bound
    intro j
    set p : Fin J × Fin J := (finProdFinEquiv (m := J) (n := J)).symm j with hp
    have h := bump_coeff_norm_le J hJ1 ha_nn haJ ((p.2 : ℝ) - (p.1 : ℝ))
    have hle : (1 : ℝ) ≤ ((J * J : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ J * J := by nlinarith
      exact_mod_cast this
    refine h.trans ?_
    exact_mod_cast hle
  · -- exponential sum identity
    intro x
    have hexp := bump_expand J a x
    rw [hexp]
    rw [← Equiv.sum_comp (finProdFinEquiv (m := J) (n := J)).symm]
  · intro x
    exact bump_nonneg J a x ha_nn
  · intro x
    exact bump_le_one J hJ1 ha_nn h2a x
  · intro x
    exact bump_even J a x
  · intro x
    exact bump_periodic J a x
  · -- the good range
    intro x hx
    have h3 : 3 * η / 2 ≤ a := by rw [ha_eq]
    have h := bump_near_one (J := J) hJ1 ha0 hη h2a h3 hx
    have h1 : 1 / ((J : ℝ) * η ^ 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hJa
    linarith
  · -- the far range
    intro x hx
    have h := bump_far (J := J) hJ1 ha0 hη ha2 ha_le hx
    have heq : 2 * a / ((J : ℝ) * η ^ 2) = 3 / ((J : ℝ) * η) := by
      rw [ha_eq]
      field_simp
    have hfin : 3 / ((J : ℝ) * η) ≤ (η ^ 2 / 16) ^ k := by
      have h2 : 3 / ((J : ℝ) * η) ≤ θ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hJb]
      rw [← hθ_eq]
      exact h2
    calc (∫ u in (x - a)..(x + a), ((1 / (J : ℝ)) * ‖(∑ k : Fin J, eC ((k : ℝ) * u))‖ ^ 2)) ≤ 2 * a / ((J : ℝ) * η ^ 2) := h
      _ = 3 / ((J : ℝ) * η) := heq
      _ ≤ (η ^ 2 / 16) ^ k := hfin


/-! ## The product cut-off `χ n = ∏ ξ ∈ Ω, 2 g (ξ n / N)`

The product of the bump over the frequencies of `Ω`, scaled by `2`, is nonnegative, even,
`N`-periodic, at least `1` on the Bohr set `B(Ω, η)` and at most `(η²/8)^|Ω|` off `B(Ω, 2η)`.
The mean clause of `ChiProps` is the one place where the size of the Bohr set enters, so it is
carried as a hypothesis. -/

private theorem prod_le_one_of {ι : Type*} (s : Finset ι) {f : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have ha0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
      have ha1 : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have hs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      exact mul_le_one₀ ha1 (Finset.prod_nonneg hs0) (ih hs0 hs1)

private theorem prod_ge_const {ι : Type*} (s : Finset ι) {f : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, C ≤ f i) : C ^ s.card ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      have ha' : C ≤ f a := h a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, C ≤ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have ih' : C ^ s.card ≤ ∏ i ∈ s, f i := ih hs
      exact mul_le_mul ha' ih' (pow_nonneg hC _) (le_trans hC ha')

private theorem prod_le_of_mem_le {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℝ} {θ : ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) {a : ι} (ha : a ∈ s) (hθ : 0 ≤ θ)
    (hfa : f a ≤ θ) : ∏ i ∈ s, f i ≤ θ := by
  classical
  have h0' : ∀ i ∈ s.erase a, 0 ≤ f i := fun i hi => h0 i (Finset.mem_of_mem_erase hi)
  have h1' : ∀ i ∈ s.erase a, f i ≤ 1 := fun i hi => h1 i (Finset.mem_of_mem_erase hi)
  have hprod : ∏ i ∈ s.erase a, f i ≤ 1 := prod_le_one_of _ h0' h1'
  have hnn : 0 ≤ ∏ i ∈ s.erase a, f i := Finset.prod_nonneg h0'
  rw [← Finset.mul_prod_erase s f ha]
  calc f a * ∏ i ∈ s.erase a, f i ≤ θ * 1 := mul_le_mul hfa hprod hnn hθ
    _ = θ := by ring

/-- A `1`-periodic function is periodic with any natural period. -/
private theorem g_add_nat {g : ℝ → ℝ} (h : ∀ x, g (x + 1) = g x) :
    ∀ (m : ℕ) (x : ℝ), g (x + m) = g x := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih =>
      intro x
      rw [show x + ((m + 1 : ℕ) : ℝ) = (x + m) + 1 by push_cast; ring, h, ih]

private theorem prod_nonneg_of_bump {Ω : Finset ℕ} {N : ℕ} {g : ℝ → ℝ} (h0 : ∀ x, 0 ≤ g x)
    (n : ℤ) : 0 ≤ ∏ ξ ∈ Ω, 2 * g ((ξ : ℝ) * (n : ℝ) / (N : ℝ)) :=
  Finset.prod_nonneg (fun ξ _ => by
    have h := h0 ((ξ : ℝ) * (n : ℝ) / (N : ℝ)); linarith)

private theorem prod_ge_one_of_bohr {Ω : Finset ℕ} {N : ℕ} {η : ℝ} {g : ℝ → ℝ}
    (hgood : ∀ x, distInt x ≤ η → 1 / 2 ≤ g x) {n : ℤ}
    (hnB : ∀ ξ ∈ Ω, distInt ((ξ : ℝ) * (n : ℝ) / (N : ℝ)) ≤ η) :
    1 ≤ ∏ ξ ∈ Ω, 2 * g ((ξ : ℝ) * (n : ℝ) / (N : ℝ)) := by
  have h1 : ∀ ξ ∈ Ω, (1 : ℝ) ≤ 2 * g ((ξ : ℝ) * (n : ℝ) / (N : ℝ)) := by
    intro ξ hξ
    have h := hgood _ (hnB ξ hξ)
    linarith
  have := prod_ge_const Ω (zero_le_one : (0 : ℝ) ≤ 1) h1
  simpa using this

private theorem prod_far_le {Ω : Finset ℕ} {N : ℕ} {η θ : ℝ} {g : ℝ → ℝ} (h0 : ∀ x, 0 ≤ g x)
    (h1 : ∀ x, g x ≤ 1) (hfar : ∀ x, 2 * η < distInt x → g x ≤ θ) (hθ0 : 0 ≤ θ)
    {n : ℤ} (hbad : ∃ ξ ∈ Ω, 2 * η < distInt ((ξ : ℝ) * (n : ℝ) / (N : ℝ))) :
    ∏ ξ ∈ Ω, 2 * g ((ξ : ℝ) * (n : ℝ) / (N : ℝ)) ≤ (2 : ℝ) ^ Ω.card * θ := by
  obtain ⟨ξ₀, hξ₀, hfar₀⟩ := hbad
  have hsplit : ∏ ξ ∈ Ω, 2 * g ((ξ : ℝ) * (n : ℝ) / (N : ℝ))
      = (2 : ℝ) ^ Ω.card * ∏ ξ ∈ Ω, g ((ξ : ℝ) * (n : ℝ) / (N : ℝ)) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    simp
  have hfa : g ((ξ₀ : ℝ) * (n : ℝ) / (N : ℝ)) ≤ θ := hfar _ hfar₀
  have hgood : ∏ ξ ∈ Ω, g ((ξ : ℝ) * (n : ℝ) / (N : ℝ)) ≤ θ :=
    prod_le_of_mem_le Ω (fun ξ _ => h0 _) (fun ξ _ => h1 _) hξ₀ hθ0 hfa
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hgood (by positivity)

/-- **`ChiProps` for the product cut-off**, from the properties of the bump and the size of the Bohr set. -/
private theorem chiProps_prod {N : ℕ} (hN : 0 < N) {Ω : Finset ℕ} {η : ℝ} {g : ℝ → ℝ}
    (hgnonneg : ∀ x, 0 ≤ g x) (hgle1 : ∀ x, g x ≤ 1) (hgeven : ∀ x, g (-x) = g x)
    (hgper : ∀ x, g (x + 1) = g x) (hggood : ∀ x, distInt x ≤ η → 1 / 2 ≤ g x)
    {θ : ℝ} (hθ0 : 0 < θ) (hgbad : ∀ x, 2 * η < distInt x → g x ≤ θ)
    (hθ : (2 : ℝ) ^ Ω.card * θ ≤ (η ^ 2 / 8) ^ Ω.card)
    (hmean : (η / 2) ^ Ω.card
      ≤ (((range N).filter (fun n => n ∈ Bohr N Ω η)).card : ℝ) / ((N : ℕ) : ℝ)) :
    ChiProps N Ω η (fun n => ∏ ξ ∈ Ω, (2 * g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ)))) := by
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hN
  have hNne : ((N : ℝ)) ≠ 0 := hNpos.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact prod_nonneg_of_bump hgnonneg n
  · intro n
    refine Finset.prod_congr rfl (fun ξ _ => ?_)
    rw [show (ξ : ℝ) * ((-n : ℤ) : ℝ) / ((N : ℕ) : ℝ)
        = -((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ)) by push_cast; ring, hgeven]
  · intro n
    refine Finset.prod_congr rfl (fun ξ _ => ?_)
    have harg : (ξ : ℝ) * ((n + (N : ℤ) : ℤ) : ℝ) / ((N : ℕ) : ℝ)
        = ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ)) + (ξ : ℝ) := by
      push_cast
      field_simp
    rw [harg, g_add_nat hgper ξ ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ))]
  · intro n _ hnB
    exact prod_ge_one_of_bohr hggood (fun ξ hξ => hnB ξ hξ)
  · intro n _ hnB
    have hnB' : ∃ ξ ∈ Ω, 2 * η < distInt ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ)) := by
      by_contra hcon
      push Not at hcon
      exact hnB (by simpa [Bohr] using hcon)
    refine (prod_far_le hgnonneg hgle1 hgbad hθ0.le hnB').trans hθ
  · -- the mean clause
    have hstep : ∀ n ∈ (range N).filter (fun n => n ∈ Bohr N Ω η),
        (1 : ℝ) ≤ ∏ ξ ∈ Ω, (2 * g ((ξ : ℝ) * ((n : ℕ) : ℝ) / ((N : ℕ) : ℝ))) := by
      intro n hn
      have hnB : n ∈ Bohr N Ω η := (Finset.mem_filter.mp hn).2
      exact prod_ge_one_of_bohr hggood (fun ξ hξ => hnB ξ hξ)
    have hnn : ∀ n ∈ range N,
        (0 : ℝ) ≤ ∏ ξ ∈ Ω, (2 * g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ))) :=
      fun n _ => prod_nonneg_of_bump hgnonneg (n : ℤ)
    unfold chiNorm
    simp only [Int.cast_natCast]
    have h1 : (((range N).filter (fun n => n ∈ Bohr N Ω η)).card : ℝ)
        ≤ ∑ n ∈ range N, ∏ ξ ∈ Ω, (2 * g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ))) := by
      have hsum1 : (((range N).filter (fun n => n ∈ Bohr N Ω η)).card : ℝ)
          = ∑ n ∈ (range N).filter (fun n => n ∈ Bohr N Ω η), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hsum1]
      refine le_trans (Finset.sum_le_sum (fun n hn => hstep n hn)) ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => hnn n ‹n ∈ range N›)
    have h3 : (((range N).filter (fun n => n ∈ Bohr N Ω η)).card : ℝ) / ((N : ℕ) : ℝ)
        ≤ ((N : ℝ))⁻¹ * ∑ n ∈ range N,
          ∏ ξ ∈ Ω, (2 * g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ))) := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith

/-! ## Fourier complexity of the product cut-off

The following seven lemmas are copied from `results/Teravainen2016-MainInputs-wip-prior-20261105.lean`
(session 20261105T1044Z), unchanged apart from the line wrapping of this file: a product of
exponential sums is an exponential sum, the term count multiplies, and padding `Fin m` to
`Fin M` finishes `FourierComplexityLE`. -/

private theorem prod_eC {ι : Type*} [Fintype ι] (z : ι → ℝ) : ∏ i, eC (z i) = eC (∑ i, z i) := by
  classical
  simp only [eC]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- **A product of exponential sums is an exponential sum.**  With one factor per `i : ι`,
`d` terms per factor, frequencies `α i j` scaled by `β i`, the product expands over the
`d ^ |ι|`-fold index set `ι → Fin d`; the linear term of the product is the sum of the
individual linear terms. -/

private theorem prod_expSum {ι : Type*} [Fintype ι] {d : ℕ}
    (c : ι → Fin d → ℂ) (α : ι → Fin d → ℝ) (β : ι → ℝ) (x : ℝ) :
    ∏ i, (∑ j, c i j * eC (α i j * (β i * x)))
      = ∑ t : (ι → Fin d), (∏ i, c i (t i)) * eC ((∑ i, α i (t i) * β i) * x) := by
  classical
  rw [show (∏ i, ∑ j : Fin d, c i j * eC (α i j * (β i * x)))
      = ∏ i, ∑ j ∈ (univ : Finset (Fin d)), c i j * eC (α i j * (β i * x)) from rfl]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have harg : (∑ i, α i (t i) * (β i * x)) = (∑ i, α i (t i) * β i) * x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.prod_mul_distrib, prod_eC, harg]

/-- The product of exponential sums in the shape `FourierComplexityLE` asks for: the index
set `ι → Fin d` reindexed as `Fin (d ^ |ι|)`, coefficients of norm at most the number of
terms. -/

private theorem exists_expSum_prod {ι : Type*} [Fintype ι] {d : ℕ} (hd : 1 ≤ d)
    (c : ι → Fin d → ℂ) (α : ι → Fin d → ℝ) (β : ι → ℝ) (hc : ∀ i j, ‖c i j‖ ≤ 1) :
    ∃ (C : Fin (d ^ Fintype.card ι) → ℂ) (A : Fin (d ^ Fintype.card ι) → ℝ),
      (∀ j, ‖C j‖ ≤ ((d ^ Fintype.card ι : ℕ) : ℝ)) ∧
      ∀ x : ℝ,
        ∏ i, (∑ j, c i j * eC (α i j * (β i * x))) = ∑ j, C j * eC (A j * x) := by
  classical
  have hcard : Fintype.card (ι → Fin d) = d ^ Fintype.card ι := by
    rw [Fintype.card_pi]
    simp
  let e : (ι → Fin d) ≃ Fin (d ^ Fintype.card ι) :=
    (Fintype.equivFin (ι → Fin d)).trans (finCongr hcard)
  refine ⟨fun j => ∏ i, c i ((e.symm j) i),
    fun j => ∑ i, α i ((e.symm j) i) * β i, ?_, ?_⟩
  · intro j
    have h1 : ‖∏ i, c i ((e.symm j) i)‖ ≤ 1 :=
      le_trans (Finset.norm_prod_le _ _)
        (prod_le_one_of Finset.univ (fun i _ => norm_nonneg _) (fun i _ => hc i _))
    have h2 : (1 : ℝ) ≤ ((d ^ Fintype.card ι : ℕ) : ℝ) := by
      have h3 : (1 : ℝ) ≤ ((d : ℕ) : ℝ) := by exact_mod_cast hd
      have h4 : (1 : ℝ) ^ Fintype.card ι ≤ ((d : ℕ) : ℝ) ^ Fintype.card ι :=
        pow_le_pow_left₀ (by norm_num) h3 _
      simpa using h4
    linarith
  · intro x
    rw [prod_expSum]
    refine Fintype.sum_equiv e _ _ (fun t => ?_)
    simp only [Equiv.symm_apply_apply]

private theorem prod_le_const {ι : Type*} (s : Finset ι) {f : ι → ℝ} {C : ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ C) (hC : 0 ≤ C) : ∏ i ∈ s, f i ≤ C ^ s.card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      have h0a : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
      have h1a : f a ≤ C := h1 a (Finset.mem_insert_self a s)
      have h0s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1s : ∀ i ∈ s, f i ≤ C := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have ih' : ∏ i ∈ s, f i ≤ C ^ s.card := ih h0s h1s
      exact mul_le_mul h1a ih' (Finset.prod_nonneg h0s) hC

/-- One small factor makes the whole product small. -/

private theorem exists_expSum_prod_le {ι : Type*} [Fintype ι] {d : ℕ} (_hd : 1 ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (c : ι → Fin d → ℂ) (α : ι → Fin d → ℝ) (β : ι → ℝ) (hc : ∀ i j, ‖c i j‖ ≤ C) :
    ∃ (C' : Fin (d ^ Fintype.card ι) → ℂ) (A : Fin (d ^ Fintype.card ι) → ℝ),
      (∀ j, ‖C' j‖ ≤ C ^ Fintype.card ι) ∧
      ∀ x : ℝ,
        ∏ i, (∑ j, c i j * eC (α i j * (β i * x))) = ∑ j, C' j * eC (A j * x) := by
  classical
  have hcard : Fintype.card (ι → Fin d) = d ^ Fintype.card ι := by
    rw [Fintype.card_pi]
    simp
  let e : (ι → Fin d) ≃ Fin (d ^ Fintype.card ι) :=
    (Fintype.equivFin (ι → Fin d)).trans (finCongr hcard)
  refine ⟨fun j => ∏ i, c i ((e.symm j) i),
    fun j => ∑ i, α i ((e.symm j) i) * β i, ?_, ?_⟩
  · intro j
    calc ‖∏ i, c i ((e.symm j) i)‖ ≤ ∏ i, ‖c i ((e.symm j) i)‖ := Finset.norm_prod_le _ _
      _ ≤ C ^ Fintype.card ι := by
          have h := prod_le_const Finset.univ (f := fun i => ‖c i ((e.symm j) i)‖) (C := C)
            (fun i _ => norm_nonneg _) (fun i _ => hc i _) hC
          simpa using h
  · intro x
    rw [prod_expSum]
    refine Fintype.sum_equiv e _ _ (fun t => ?_)
    simp only [Equiv.symm_apply_apply]

/-- Pad an exponential sum to a larger number of terms by adding zero coefficients. -/

private theorem fourierComplexityLE_of_fin_le {χ : ℤ → ℝ} {m M : ℕ} (h : m ≤ M) (c : Fin m → ℂ)
    (α : Fin m → ℝ) (hc : ∀ j, ‖c j‖ ≤ (M : ℝ))
    (hsum : ∀ n : ℤ, (χ n : ℂ) = ∑ j, c j * eC (α j * (n : ℝ))) :
    FourierComplexityLE χ M := by
  classical
  have key : ∀ n : ℤ,
      (∑ j : Fin M, (if hj : (j : ℕ) < m then c ⟨(j : ℕ), hj⟩ else 0)
          * eC ((if hj : (j : ℕ) < m then α ⟨(j : ℕ), hj⟩ else 0) * (n : ℝ)))
        = ∑ i : Fin m, c i * eC (α i * (n : ℝ)) := by
    intro n
    set F : ℕ → ℂ := fun j =>
      (if hj : j < m then c ⟨j, hj⟩ else 0) * eC ((if hj : j < m then α ⟨j, hj⟩ else 0) * (n : ℝ))
      with hF
    have h1 : (∑ j : Fin M, (if hj : (j : ℕ) < m then c ⟨(j : ℕ), hj⟩ else 0)
          * eC ((if hj : (j : ℕ) < m then α ⟨(j : ℕ), hj⟩ else 0) * (n : ℝ)))
        = ∑ j ∈ Finset.range M, F j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => F j) M]
    have h2 : (∑ i : Fin m, c i * eC (α i * (n : ℝ))) = ∑ j ∈ Finset.range m, F j := by
      have e1 : (∑ i : Fin m, c i * eC (α i * (n : ℝ))) = ∑ i : Fin m, F (i : ℕ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hi : (i : ℕ) < m := i.isLt
        simp only [hF, dif_pos hi]
      rw [e1, Fin.sum_univ_eq_sum_range (fun j => F j) m]
    have h3 : (∑ j ∈ Finset.range M, F j) = ∑ j ∈ Finset.range m, F j := by
      refine Eq.symm ?_
      refine Finset.sum_subset (Finset.range_subset_range.mpr h) ?_
      intro j _ hj'
      have hj'' : ¬ j < m := by simpa using hj'
      simp only [hF, dif_neg hj'', zero_mul]
    rw [h1, h3, h2]
  refine ⟨fun j => if hj : (j : ℕ) < m then c ⟨(j : ℕ), hj⟩ else 0,
    fun j => if hj : (j : ℕ) < m then α ⟨(j : ℕ), hj⟩ else 0, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases hj : (j : ℕ) < m
    · rw [dif_pos hj]
      exact hc _
    · rw [dif_neg hj]
      simp
  · intro n
    rw [hsum]
    exact (key n).symm

/-- A product of terms each at least `C ≥ 0` is at least `C ^ card`. -/

private theorem fourierComplexityLE_chi {k d : ℕ} (hd : 1 ≤ d) (c : Fin d → ℂ) (α : Fin d → ℝ)
    (hc : ∀ j, ‖c j‖ ≤ (d : ℝ)) {g : ℝ → ℝ}
    (hg : ∀ x, (g x : ℂ) = ∑ j, c j * eC (α j * x))
    {Ω : Finset ℕ} (hΩ : Ω.card ≤ k) (N : ℕ) :
    FourierComplexityLE
      (fun n => ∏ ξ ∈ Ω, (2 * g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ)))) ((2 * d) ^ k) := by
  classical
  have hcardι : Fintype.card {x // x ∈ Ω} = Ω.card := by simp
  obtain ⟨C', A, hC', hsum⟩ := exists_expSum_prod_le (ι := {x // x ∈ Ω}) (d := d) hd
    (C := 2 * (d : ℝ)) (by positivity)
    (fun (i : {x // x ∈ Ω}) j => 2 * c j) (fun (i : {x // x ∈ Ω}) j => α j)
    (fun (i : {x // x ∈ Ω}) => (i.1 : ℝ) / ((N : ℕ) : ℝ))
    (fun i j => by
      rw [norm_mul]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      nlinarith [hc j])
  have hkey : ∀ n : ℤ,
      (((∏ ξ ∈ Ω, (2 * g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ)))) : ℝ) : ℂ)
        = ∑ j : Fin (d ^ Fintype.card {x // x ∈ Ω}), C' j * eC (A j * (n : ℝ)) := by
    intro n
    have h0 : (((∏ ξ ∈ Ω, (2 * g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ)))) : ℝ) : ℂ)
        = ∏ ξ ∈ Ω, ((2 : ℂ) * ((g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ))) : ℂ)) := by
      push_cast
      ring
    have h1 : (∏ ξ ∈ Ω, ((2 : ℂ) * ((g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ))) : ℂ)))
        = ∏ i : {x // x ∈ Ω},
            (∑ j, (2 * c j) * eC (α j * (((i.1 : ℝ) / ((N : ℕ) : ℝ)) * (n : ℝ)))) := by
      rw [← Finset.prod_attach Ω
        (f := fun ξ => (2 : ℂ) * ((g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ))) : ℂ))]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hg, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have harg : α j * ((i.1 : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ))
          = α j * (((i.1 : ℝ) / ((N : ℕ) : ℝ)) * (n : ℝ)) := by ring
      rw [harg]
      ring
    rw [h0, h1]
    exact hsum ((n : ℤ) : ℝ)
  -- the term count: `d ^ Ω.card ≤ (2 * d) ^ k`
  have hle : d ^ Fintype.card {x // x ∈ Ω} ≤ (2 * d) ^ k := by
    rw [hcardι]
    have hnat : d ^ Ω.card ≤ (2 * d) ^ k := by
      have h1 : d ^ Ω.card ≤ d ^ k := Nat.pow_le_pow_right hd hΩ
      have h2 : d ^ k ≤ (2 * d) ^ k := Nat.pow_le_pow_left (by omega) k
      exact le_trans h1 h2
    exact hnat
  refine fourierComplexityLE_of_fin_le (m := d ^ Fintype.card {x // x ∈ Ω}) (M := (2 * d) ^ k)
    hle C' A (fun j => ?_) hkey
  -- coefficient bound
  refine le_trans (hC' j) ?_
  rw [hcardι]
  have hnat : (2 * d) ^ Ω.card ≤ (2 * d) ^ k := by
    have h1 : (2 * d) ^ Ω.card ≤ (2 * d) ^ k := Nat.pow_le_pow_right (by omega) hΩ
    exact h1
  have hcast : (((2 * d) ^ Ω.card : ℕ) : ℝ) ≤ (((2 * d) ^ k : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa [Nat.cast_pow] using hcast


/-! ## Leaf 1 from the two inputs

`ChiExists` follows from (a) the flat top of `flat_top_exists` -- in the `θ`-fixed form, one
bump per `(k, η)` with threshold `(η ^ 2 / 16) ^ k` -- and (b) the size of the Bohr set, which
is the only analytic input left.  For `η ≥ 1 / 4` the constant `1` is a cut-off, because every
point is within `1/2` of an integer, so the smallness clause of `ChiProps` is vacuous. -/

private theorem fourierComplexity_one_one : FourierComplexityLE (fun _ : ℤ => (1 : ℝ)) 1 := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => ?_, fun n => ?_⟩
  · simp
  · simp [eC]

/-- `ChiProps` for the constant `1` when `2 η ≥ 1 / 2`: the smallness clause is vacuous. -/
private theorem chiProps_one_of_quarter (N : ℕ) (hN : 0 < N) (Ω : Finset ℕ) {η : ℝ} (_hη : 0 < η)
    (_hηq : 1 / 4 ≤ η) (hcard : (η / 2) ^ Ω.card ≤ 1) : ChiProps N Ω η (fun _ => 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun _ => zero_le_one, fun _ => rfl, fun _ => rfl, fun _ _ _ => le_rfl, ?_, ?_⟩
  · intro n _ hnb
    exfalso
    apply hnb
    intro ξ _
    have h := distInt_le_half (((ξ : ℝ) * (n : ℝ)) / ((N : ℕ) : ℝ))
    linarith
  · unfold chiNorm
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ hN0.ne']
    exact hcard

/-- **Leaf 1 from a flat top and the Bohr-set count.** -/
private theorem chiExists_of_flatTop_and_bohr
    (hflat : ∀ (k : ℕ) (η : ℝ), 0 < η → η < 1 / 4 →
      ∃ (d : ℕ) (c : Fin d → ℂ) (α : Fin d → ℝ) (g : ℝ → ℝ),
        1 ≤ d ∧ (∀ j, ‖c j‖ ≤ (d : ℝ)) ∧
        (∀ x, (g x : ℂ) = ∑ j, c j * eC (α j * x)) ∧
        (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧
        (∀ x, g (-x) = g x) ∧ (∀ x, g (x + 1) = g x) ∧
        (∀ x, distInt x ≤ η → 1 / 2 ≤ g x) ∧
        (∀ x, 2 * η < distInt x → g x ≤ (η ^ 2 / 16) ^ k))
    (hbohr : ∀ (N : ℕ) (Ω : Finset ℕ) (η : ℝ), 1 ≤ N → 0 < η → η ≤ 1 / 2 →
      (∀ ξ ∈ Ω, ξ < N) →
      (η / 2) ^ Ω.card * (N : ℝ) ≤ (((range N).filter (fun n => n ∈ Bohr N Ω η)).card : ℝ)) :
    ChiExists := by
  intro k η hη hη'
  rcases lt_or_ge η (1 / 4) with hsmall | hbig
  · -- the flat-top regime
    obtain ⟨d, c, α, g, hd, hc, hg, hg0, hg1, hgsym, hgper, hggood, hgbad⟩ := hflat k η hη hsmall
    refine ⟨(2 * d) ^ k, fun N hN Ω hΩ hk => ?_⟩
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hNle : 1 ≤ N := hN
    have hηpos : 0 < η := hη
    have hηhalf : η ≤ 1 / 2 := le_of_lt hη'
    have hbohr' := hbohr N Ω η hNle hηpos hηhalf (fun ξ hξ => by
      have := hΩ hξ
      simpa using this)
    have hmean : (η / 2) ^ Ω.card
        ≤ (((range N).filter (fun n => n ∈ Bohr N Ω η)).card : ℝ) / ((N : ℕ) : ℝ) := by
      rw [le_div_iff₀ hN0]
      linarith [hbohr']
    have hθ0 : 0 < (η ^ 2 / 16) ^ k := by
      have : 0 < η ^ 2 / 16 := by positivity
      positivity
    have hθ : (2 : ℝ) ^ Ω.card * (η ^ 2 / 16) ^ k ≤ (η ^ 2 / 8) ^ Ω.card := by
      have hsq : η ^ 2 ≤ 1 / 16 := by nlinarith [hη, hsmall]
      have hbase1 : η ^ 2 / 8 ≤ 1 := by linarith
      have hstep1 : (2 : ℝ) ^ Ω.card * (η ^ 2 / 16) ^ k
          ≤ (2 : ℝ) ^ k * (η ^ 2 / 16) ^ k :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) (by positivity)
      have hstep2 : (2 : ℝ) ^ k * (η ^ 2 / 16) ^ k = (η ^ 2 / 8) ^ k := by
        rw [← mul_pow]
        congr 1
        ring
      have hstep3 : (η ^ 2 / 8) ^ k ≤ (η ^ 2 / 8) ^ Ω.card :=
        pow_le_pow_of_le_one (by positivity : (0 : ℝ) ≤ η ^ 2 / 8) hbase1 hk
      calc (2 : ℝ) ^ Ω.card * (η ^ 2 / 16) ^ k
          ≤ (2 : ℝ) ^ k * (η ^ 2 / 16) ^ k := hstep1
        _ = (η ^ 2 / 8) ^ k := hstep2
        _ ≤ (η ^ 2 / 8) ^ Ω.card := hstep3
    refine ⟨fun n => ∏ ξ ∈ Ω, (2 * g ((ξ : ℝ) * (n : ℝ) / ((N : ℕ) : ℝ))),
      chiProps_prod hN hg0 hg1 hgsym hgper hggood hθ0 hgbad hθ hmean, ?_⟩
    exact fourierComplexityLE_chi hd c α hc hg hk N
  · -- the vacuous regime `η ≥ 1 / 4`
    refine ⟨1, fun N hN Ω hΩ hk => ?_⟩
    have hcard : (η / 2) ^ Ω.card ≤ 1 := by
      have h0 : (0 : ℝ) ≤ η / 2 := by linarith
      have h1 : η / 2 ≤ 1 := by linarith
      simpa using pow_le_pow_left₀ h0 h1 Ω.card
    exact ⟨fun _ => 1, chiProps_one_of_quarter N hN Ω hη hbig hcard,
      fourierComplexity_one_one⟩


/-- **Leaf 1 reduces to the size of the Bohr set alone.**  With the flat top proved above, the
only input left for `paper_smooth_cutoff_input : ChiExists` is the count
`(η / 2) ^ |Ω| * N ≤ |B(Ω, η)|`. -/
private theorem chiExists_of_bohr
    (hbohr : ∀ (N : ℕ) (Ω : Finset ℕ) (η : ℝ), 1 ≤ N → 0 < η → η ≤ 1 / 2 →
      (∀ ξ ∈ Ω, ξ < N) →
      (η / 2) ^ Ω.card * (N : ℝ) ≤ (((range N).filter (fun n => n ∈ Bohr N Ω η)).card : ℝ)) :
    ChiExists := by
  refine chiExists_of_flatTop_and_bohr ?_ hbohr
  intro k η hη hη4
  obtain ⟨d, c, α, hc, g, hg, hg0, hg1, hgsym, hgper, hggood, hgbad⟩ :=
    flat_top_exists k η hη hη4
  have hd : 1 ≤ d := by
    rcases Nat.eq_or_lt_of_le (Nat.zero_le d) with h | h
    · subst h
      have h1 : (g 0 : ℂ) = 0 := by
        rw [hg 0]
        simp
      have h2 : g 0 = 0 := by exact_mod_cast h1
      have h3 : (1 : ℝ) / 2 ≤ g 0 := hggood 0 (by rw [distInt]; simp; linarith)
      linarith
    · omega
  exact ⟨d, c, α, g, hd, hc, hg, hg0, hg1, hgsym, hgper, hggood, hgbad⟩

/-! ## The size of the Bohr set

Ported from `results/Teravainen2016-MainInputs-wip-prior-20261105.lean` (session 20261105T1044Z),
where it is `bohr_card_lower`: Tao-Vu, *Additive Combinatorics*, Lemma 4.20 (Matomaki-Shao
[15, Lemma 3.1(i)]), by pigeon-holing the torus into `m = floor (1/eta) + 1` boxes per
coordinate.  It introduces no new declaration, so it goes into the lab file unchanged. -/

private theorem distInt_add_int_b (x : ℝ) (k : ℤ) : distInt (x + (k : ℝ)) = distInt x := by
  unfold distInt
  rw [round_add_intCast]
  congr 1
  push_cast
  ring

private theorem distInt_le_self_b {x : ℝ} (hx : 0 ≤ x) : distInt x ≤ x := by
  rcases lt_or_ge x (1 / 2) with h | h
  · have h0 : round x = 0 := by
      rw [round_eq_zero_iff]
      exact ⟨by linarith, h⟩
    unfold distInt
    rw [h0]
    simp only [Int.cast_zero, sub_zero, abs_of_nonneg hx]
    exact le_rfl
  · exact (abs_sub_round x).trans h

private theorem distInt_le_abs_b (x : ℝ) : distInt x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · exact (distInt_le_self_b h).trans (le_abs_self x)
  · rw [← distInt_neg x, ← abs_neg x]
    exact (distInt_le_self_b (by linarith)).trans (le_abs_self _)

private theorem lt_div_succ_mul {x k : ℕ} (hk : 0 < k) : x < (x / k + 1) * k := by
  have h1 : x % k < k := Nat.mod_lt _ hk
  calc x = k * (x / k) + x % k := (Nat.div_add_mod x k).symm
    _ < k * (x / k) + k := by omega
    _ = (x / k + 1) * k := by ring

private theorem abs_sub_mul_lt_of_div_eq {N m a b : ℕ} (hN : 0 < N) (hm : 0 < m)
    (h : a * m / N = b * m / N) : |(a : ℤ) - (b : ℤ)| * (m : ℤ) < (N : ℤ) := by
  set t := a * m / N with ht
  have hh : b * m / N = t := h.symm
  have h1 : t * N ≤ a * m := by rw [ht]; exact Nat.div_mul_le_self _ _
  have h2 : t * N ≤ b * m := by rw [← hh]; exact Nat.div_mul_le_self _ _
  have h3 : a * m < (t + 1) * N := by rw [ht]; exact lt_div_succ_mul hN
  have h4 : b * m < (t + 1) * N := by rw [← hh]; exact lt_div_succ_mul hN
  have i1 : ((t * N : ℕ) : ℤ) ≤ ((a * m : ℕ) : ℤ) := by exact_mod_cast h1
  have i2 : ((t * N : ℕ) : ℤ) ≤ ((b * m : ℕ) : ℤ) := by exact_mod_cast h2
  have i3 : ((a * m : ℕ) : ℤ) < (((t + 1) * N : ℕ) : ℤ) := by exact_mod_cast h3
  have i4 : ((b * m : ℕ) : ℤ) < (((t + 1) * N : ℕ) : ℤ) := by exact_mod_cast h4
  push_cast at i1 i2 i3 i4
  have key : |(a : ℤ) * (m : ℤ) - (b : ℤ) * (m : ℤ)| < (N : ℤ) := by
    rw [abs_lt]
    constructor <;> [skip; skip] <;> nlinarith
  rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (m : ℤ))] at key
  exact key


/-- **Tao–Vu, Additive Combinatorics, Lemma 4.20** (Matomäki–Shao, [15, Lemma 3.1(i)]):
the size of the Bohr set.  Pure pigeon-holing: split the torus into `m = ⌊1/η⌋ + 1` boxes per
coordinate, two multiples of the frequency vector in one box differ by a point of the Bohr set,
and each box difference gives an injection into `Bohr`. -/
private theorem bohr_card_lower (N : ℕ) (Ω : Finset ℕ) (η : ℝ) (hN : 1 ≤ N) (hη : 0 < η)
    (hη' : η ≤ 1 / 2) :
    (η / 2) ^ Ω.card * (N : ℝ) ≤
      ((((range N).filter (fun n => n ∈ Bohr N Ω η)).card : ℕ) : ℝ) := by
  classical
  have hNpos : 0 < N := by omega
  set m : ℕ := ⌊1 / η⌋₊ + 1 with hm_eq
  have hm1 : 1 ≤ m := Nat.le_add_left 1 _
  have hmpos : 0 < m := hm1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hfloor : 1 / η < (m : ℝ) := by
    have h := Nat.lt_floor_add_one (1 / η)
    simpa [hm_eq] using h
  have hm_le : (m : ℝ) ≤ 2 / η := by
    have h1 : ((⌊1 / η⌋₊ : ℕ) : ℝ) ≤ 1 / η := Nat.floor_le (by positivity)
    have h2 : (1 : ℝ) ≤ 1 / η := by
      rw [le_div_iff₀ hη]; linarith
    have he : (m : ℝ) = ((⌊1 / η⌋₊ : ℕ) : ℝ) + 1 := by simp [hm_eq]
    have h3 : 2 / η = 1 / η + 1 / η := by ring
    rw [he, h3]; linarith
  have hinv : 1 / (m : ℝ) ≤ η := by
    rw [div_le_iff₀ hmR]
    have h : 1 < η * (m : ℝ) := by
      have h' := hfloor
      rw [div_lt_iff₀ hη] at h'
      linarith
    linarith
  -- the box index of the pair (frequency, n)
  set box : ℕ → ℕ → ℕ := fun ξ n => ξ * n % N * m / N with hbox_eq
  have hbox_lt : ∀ ξ n, box ξ n < m := by
    intro ξ n
    have hlt : ξ * n % N < N := Nat.mod_lt _ hNpos
    simp only [hbox_eq]
    rw [Nat.div_lt_iff_lt_mul hNpos]
    calc ξ * n % N * m < N * m := (Nat.mul_lt_mul_right hmpos).mpr hlt
      _ = m * N := by ring
  let key : ℕ → (↥Ω → Fin m) := fun n ξ => ⟨box ξ.1 n, hbox_lt ξ.1 n⟩
  -- pigeon-hole
  have huniv : (Finset.univ : Finset (↥Ω → Fin m)).Nonempty :=
    ⟨fun _ => ⟨0, hmpos⟩, Finset.mem_univ _⟩
  obtain ⟨k0, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (↥Ω → Fin m))
    (fun k => ((range N).filter (fun n => key n = k)).card) huniv
  set F : Finset ℕ := (range N).filter (fun n => key n = k0) with hF_eq
  have hFsub : F ⊆ range N := fun n hn => (Finset.mem_filter.mp hn).1
  have hFmem : ∀ n, n ∈ F ↔ n ∈ range N ∧ key n = k0 := fun n => Finset.mem_filter
  have hNsum : N = ∑ k : (↥Ω → Fin m), ((range N).filter (fun n => key n = k)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := range N)
      (t := (Finset.univ : Finset (↥Ω → Fin m))) (f := key) (fun n _ => Finset.mem_univ _)
    rw [Finset.card_range] at h
    exact h
  have hsum : (N : ℝ) =
      ∑ k : (↥Ω → Fin m), (((range N).filter (fun n => key n = k)).card : ℝ) := by
    conv_lhs => rw [hNsum]
    push_cast
    rfl
  have hbound : (N : ℝ) ≤ ((m : ℝ) ^ Ω.card) * (F.card : ℝ) := by
    rw [hsum]
    calc ∑ k : (↥Ω → Fin m), (((range N).filter (fun n => key n = k)).card : ℝ)
        ≤ ∑ _k : (↥Ω → Fin m), (F.card : ℝ) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact_mod_cast hmax k (Finset.mem_univ k)
      _ = (Fintype.card (↥Ω → Fin m) : ℝ) * (F.card : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ((m : ℝ) ^ Ω.card) * (F.card : ℝ) := by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
          push_cast
          rfl
  have hFbound : (η / 2) ^ Ω.card * (N : ℝ) ≤ (F.card : ℝ) := by
    have hdiv : (N : ℝ) / ((m : ℝ) ^ Ω.card) ≤ (F.card : ℝ) := by
      rw [div_le_iff₀ (pow_pos hmR _), mul_comm]
      exact hbound
    refine le_trans ?_ hdiv
    have hbase : η / 2 ≤ 1 / (m : ℝ) := by
      have hmul : η * (m : ℝ) ≤ 2 := by
        have := mul_le_mul_of_nonneg_left hm_le (le_of_lt hη)
        have hsub : η * (2 / η) = 2 := by field_simp
        linarith
      rw [le_div_iff₀ hmR]
      linarith
    have hp : (η / 2) ^ Ω.card ≤ (1 / (m : ℝ)) ^ Ω.card :=
      pow_le_pow_left₀ (by positivity) hbase _
    calc (η / 2) ^ Ω.card * (N : ℝ) ≤ (1 / (m : ℝ)) ^ Ω.card * N :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (N : ℝ) / ((m : ℝ) ^ Ω.card) := by
          rw [div_pow, one_pow]; ring
  refine hFbound.trans ?_
  -- the injection `n ↦ (n + (N - n0)) % N` from the maximal fibre into the Bohr set
  have hpos : 0 < F.card := by
    have h0 : (0 : ℕ) ∈ range N := Finset.mem_range.mpr hNpos
    have hle : ((range N).filter (fun n => key n = key 0)).card ≤ F.card :=
      hmax (key 0) (Finset.mem_univ _)
    have h1 : 0 < ((range N).filter (fun n => key n = key 0)).card :=
      Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨h0, rfl⟩⟩
    omega
  obtain ⟨n0, hn0⟩ := Finset.card_pos.mp hpos
  have hn0lt : n0 < N := Finset.mem_range.mp (hFsub hn0)
  have hk0 : key n0 = k0 := ((hFmem n0).mp hn0).2
  have hexp : ∀ n ∈ F, n < N ∧ key n = key n0 := by
    intro n hn
    obtain ⟨hr, hk⟩ := (hFmem n).mp hn
    exact ⟨Finset.mem_range.mp hr, by rw [hk, hk0]⟩
  have hFBnat : F.card ≤ ((range N).filter (fun n => n ∈ Bohr N Ω η)).card := by
    refine Finset.card_le_card_of_injOn (fun n => (n + (N - n0)) % N) ?_ ?_
    · intro n hn
      obtain ⟨hnlt, hkey⟩ := hexp n hn
      have hplt : (n + (N - n0)) % N < N := Nat.mod_lt _ hNpos
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hplt, ?_⟩
      intro ξ hξ
      -- the two residues of `ξ * n` and `ξ * n0` lie in the same box
      have hboxeq : box ξ n = box ξ n0 := by
        have hcon := congrFun hkey ⟨ξ, hξ⟩
        have hval := congrArg Fin.val hcon
        simpa [key] using hval
      have hclose : |((ξ * n % N : ℕ) : ℤ) - ((ξ * n0 % N : ℕ) : ℤ)| * (m : ℤ) < (N : ℤ) :=
        abs_sub_mul_lt_of_div_eq hNpos hmpos hboxeq
      -- write `ξ p / N = (a - b) / N + an integer`, with `a = ξ n % N`, `b = ξ n0 % N`, `p` the residue
      set p : ℕ := (n + (N - n0)) % N with hp_eq
      set a : ℕ := ξ * n % N with ha_eq
      set b : ℕ := ξ * n0 % N with hb_eq
      have hpn : ∃ t : ℤ, ((p : ℕ) : ℤ) = ((n : ℕ) : ℤ) - ((n0 : ℕ) : ℤ) + t * (N : ℤ) := by
        set q : ℕ := (n + (N - n0)) / N with hq_eq
        have hdm : N * q + p = n + (N - n0) := by
          rw [hp_eq, hq_eq]
          exact Nat.div_add_mod _ _
        have hcast : ((n + (N - n0) : ℕ) : ℤ) = (n : ℤ) + ((N : ℤ) - (n0 : ℤ)) := by
          have hsub : ((N - n0 : ℕ) : ℤ) = (N : ℤ) - (n0 : ℤ) :=
            Nat.cast_sub (by omega : n0 ≤ N)
          push_cast
          rw [hsub]
        have hdmZ : (N : ℤ) * (q : ℤ) + (p : ℤ) = (n : ℤ) + ((N : ℤ) - (n0 : ℤ)) := by
          rw [← hcast]; exact_mod_cast hdm
        refine ⟨1 - (q : ℤ), ?_⟩
        linear_combination hdmZ
      obtain ⟨t, ht⟩ := hpn
      have han : (ξ : ℤ) * (n : ℤ) = (N : ℤ) * ((ξ * n / N : ℕ) : ℤ) + (a : ℤ) := by
        have hdm : N * (ξ * n / N) + ξ * n % N = ξ * n := Nat.div_add_mod _ _
        have hd2 : ((N * (ξ * n / N) + ξ * n % N : ℕ) : ℤ) = ((ξ * n : ℕ) : ℤ) := by rw [hdm]
        have expand : ((N * (ξ * n / N) + ξ * n % N : ℕ) : ℤ)
            = (N : ℤ) * ((ξ * n / N : ℕ) : ℤ) + ((ξ * n % N : ℕ) : ℤ) := by
          simp only [Nat.cast_add, Nat.cast_mul]
        rw [expand, ← ha_eq] at hd2
        have hc : ((ξ * n : ℕ) : ℤ) = (ξ : ℤ) * (n : ℤ) := by simp only [Nat.cast_mul]
        rw [hc] at hd2
        linarith
      have hbn : (ξ : ℤ) * (n0 : ℤ) = (N : ℤ) * ((ξ * n0 / N : ℕ) : ℤ) + (b : ℤ) := by
        have hdm : N * (ξ * n0 / N) + ξ * n0 % N = ξ * n0 := Nat.div_add_mod _ _
        have hd2 : ((N * (ξ * n0 / N) + ξ * n0 % N : ℕ) : ℤ) = ((ξ * n0 : ℕ) : ℤ) := by rw [hdm]
        have expand : ((N * (ξ * n0 / N) + ξ * n0 % N : ℕ) : ℤ)
            = (N : ℤ) * ((ξ * n0 / N : ℕ) : ℤ) + ((ξ * n0 % N : ℕ) : ℤ) := by
          simp only [Nat.cast_add, Nat.cast_mul]
        rw [expand, ← hb_eq] at hd2
        have hc : ((ξ * n0 : ℕ) : ℤ) = (ξ : ℤ) * (n0 : ℤ) := by simp only [Nat.cast_mul]
        rw [hc] at hd2
        linarith
      -- the integer `t'` with `ξ p / N = (a - b) / N + t'`
      have hkey2 : ∃ t' : ℤ, (ξ : ℝ) * (p : ℝ) / (N : ℝ)
          = ((a : ℝ) - (b : ℝ)) / (N : ℝ) + (t' : ℝ) := by
        refine ⟨(ξ : ℤ) * t + ((ξ * n / N : ℕ) : ℤ) - ((ξ * n0 / N : ℕ) : ℤ), ?_⟩
        have hN0 : (N : ℝ) ≠ 0 := by positivity
        field_simp
        -- reduce to an ℤ identity
        have : (ξ : ℤ) * (p : ℤ) = ((a : ℤ) - (b : ℤ)) +
            (N : ℤ) * ((ξ : ℤ) * t + ((ξ * n / N : ℕ) : ℤ) - ((ξ * n0 / N : ℕ) : ℤ)) := by
          linear_combination (ξ : ℤ) * ht + han - hbn
        have hcast2 := congrArg (fun z : ℤ => (z : ℝ)) this
        push_cast at hcast2 ⊢
        linarith
      obtain ⟨t', ht'⟩ := hkey2
      rw [ht']
      have hdist : distInt (((a : ℝ) - (b : ℝ)) / (N : ℝ) + (t' : ℝ))
          = distInt (((a : ℝ) - (b : ℝ)) / (N : ℝ)) := distInt_add_int_b _ _
      rw [hdist]
      have hNa : (0 : ℝ) < (N : ℝ) := by positivity
      refine le_trans (distInt_le_abs_b _) ?_
      rw [abs_div, abs_of_pos hNa, div_le_iff₀ hNa]
      have habs : |((a : ℝ) - (b : ℝ))| * (m : ℝ) < (N : ℝ) := by
        have h2 : ((|(a : ℤ) - (b : ℤ)| * (m : ℤ) : ℤ) : ℝ) < ((N : ℤ) : ℝ) := by
          exact_mod_cast hclose
        push_cast at h2
        exact h2
      have hlt : |((a : ℝ) - (b : ℝ))| * (m : ℝ) / (m : ℝ) < (N : ℝ) / (m : ℝ) := by
        rw [div_lt_div_iff_of_pos_right hmR]
        exact habs
      have heq : |((a : ℝ) - (b : ℝ))| * (m : ℝ) / (m : ℝ) = |((a : ℝ) - (b : ℝ))| := by
        field_simp
      have hle : (N : ℝ) / (m : ℝ) ≤ (N : ℝ) * η := by
        have h1 : (1 : ℝ) ≤ η * (m : ℝ) := by
          have h' := mul_le_mul_of_nonneg_right hinv (le_of_lt hmR)
          rw [one_div] at h'
          rwa [inv_mul_cancel₀ (ne_of_gt hmR)] at h'
        rw [div_le_iff₀ hmR]
        nlinarith [h1, show (0 : ℝ) < (N : ℝ) by positivity]
      calc |((a : ℝ) - (b : ℝ))| = |((a : ℝ) - (b : ℝ))| * (m : ℝ) / (m : ℝ) := heq.symm
        _ ≤ (N : ℝ) / (m : ℝ) := le_of_lt hlt
        _ ≤ (N : ℝ) * η := hle
        _ = η * N := by ring
    · intro a1 ha1 b1 hb1 hab
      have ha1' : a1 < N := (hexp a1 ha1).1
      have hb1' : b1 < N := (hexp b1 hb1).1
      have hN0 : 0 < N := hNpos
      -- both are congruent mod N and lie in `[0, 2N)`
      have hma : (a1 + (N - n0)) % N = (b1 + (N - n0)) % N := hab
      have ha2 : a1 + (N - n0) < 2 * N := by omega
      have hb2 : b1 + (N - n0) < 2 * N := by omega
      have hca := Nat.mod_eq_of_lt ha2
      have hcb := Nat.mod_eq_of_lt hb2
      -- `x % N = y % N` for `x, y < 2N` implies `x = y`
      have hmod : (a1 + (N - n0)) ≡ (b1 + (N - n0)) [MOD N] := by
        rw [Nat.ModEq, hma]
      have := Nat.ModEq.add_right_cancel' (N - n0) hmod
      exact Nat.ModEq.eq_of_lt_of_lt this ha1' hb1'

  exact_mod_cast hFBnat

/-- **Leaf 1**: `paper_smooth_cutoff_input`, with the Bohr count supplied. -/
private theorem chiExists_proved : ChiExists :=
  chiExists_of_bohr (fun N Ω η hN hη hη' _ => bohr_card_lower N Ω η hN hη hη')

end Teravainen2016_chiExists

/-- LEAF. Page 6, the cutoff existence quoted from Matomaki and Shao Lemma 3.1.
CONDITIONAL ON that published cutoff construction. -/
theorem paper_smooth_cutoff_input : ChiExists := chiExists_proved

/-- LEAF. Page 9, Proposition 3.2, with the bounded shift reading in Transference.lean.
CONDITIONAL ON the weighted prime distribution estimate proved in Sections 5 through 10. -/
theorem paper_weighted_prime_input : Prop32 := by sorry

/-- LEAF. Page 11, the half interval refinement of Proposition 3.2.
CONDITIONAL ON this weighted prime distribution refinement.
This refinement is not the printed dyadic Proposition 3.2. -/
theorem paper_half_interval_input : Prop32Half := by sorry

/-- LEAF. Page 9, Proposition 3.3, and pages 13 to 17, its restriction argument.
CONDITIONAL ON the reconstructed bounded shift and changed scale restriction input.
This avoids assuming unrestricted uniformity in all integer shifts. -/
theorem paper_cross_scale_restriction_input : Prop33Cross := by sorry

/-- LEAF. Pages 9 to 12, the ternary deduction in Remark 3.6.
CONDITIONAL ON the cited Matomaki and Shao Theorem 2.3. -/
theorem paper_ternary_transference_input : MSThm23 := by sorry

/-- LEAF. Page 17, the Section 4 dense model and Green Tao transference argument.
CONDITIONAL ON that analytic modular progression output.
This is its modular output before the elementary lifting step. -/
theorem paper_dense_modular_progressions_input (A : Set ℕ)
    (hA : A ⊆ PStar) (hδ : PosUpperDensityIn A PStar) :
    ∀ X : ℕ, ∃ N a b c : ℕ, X ≤ N ∧
      a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
      N < 3 * a ∧ 3 * a < 2 * N ∧
      N < 3 * b ∧ 3 * b < 2 * N ∧
      N < 3 * c ∧ 3 * c < 2 * N ∧
      a ≠ b ∧ (a : ZMod N) + c = 2 * b := by sorry

/-- LEAF. Pages 44 to 47, the Section 11 prime approximation estimate.
CONDITIONAL ON that prime approximation estimate.
The positive frequency and small positive exponent reading precedes display 11.1. -/
theorem paper_dyadic_approximation_input (ξ : ℝ) (hξ : Irrational ξ) (hξ0 : 0 < ξ)
    (κ θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 80) :
    ∀ X : ℕ, ∃ N p : ℕ, max 1 X ≤ N ∧ N ≤ p ∧ p ≤ 2 * N ∧
      InP p ∧ distInt (ξ * p + κ) ≤ (N : ℝ) ^ (-θ) / 2 := by sorry

#print axioms paper_smooth_cutoff_input

end LeanLab.Teravainen2016
