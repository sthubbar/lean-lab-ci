import LeanLab.GoldbachAverage.GSCorollary2

/-!
Ingham's psi bound for the theta route in P0051.
Source route: arXiv 2110.14250v2 page 20, as transcribed in PROGRESS.md.
This proof generalizes the lab's von Koch proof and uses the proved psi1 formula.
Source pages 6, 19 and 20 were read from the arXiv PDF in this run.
AI wrote this Lean code. Goldbach is open.
-/

open Finset Complex
open scoped ArithmeticFunction.vonMangoldt Chebyshev
noncomputable section
namespace LeanLab.GoldbachAverage.InghamTheta
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.LZCesaroShort

/-- Zero sum differences under a bound on the real parts. -/
theorem dW_theta (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hzeros : ∀ ρ : Zall, ρ.1.re ≤ theta) : ∃ D1 D2 : ℝ, 0 ≤ D1 ∧ 0 ≤ D2 ∧
    ∀ x : ℝ, 6 ≤ x → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 2 * x →
    ‖Wf b - Wf a‖ ≤ (b - a) * (2 * x) ^ theta * (D1 * (Real.log x + 1) ^ 2) +
      (2 * x) ^ (theta + 1) * (2 * D2 * (Real.log x + 1) / x) := by
  obtain ⟨C1, hC1, hZ1⟩ := zero_sum_inv_bound
  obtain ⟨C2, hC2, hZ2⟩ := tail_count
  refine ⟨C1, C2, hC1, hC2, fun x hx a b ha hab hb => ?_⟩
  have hx0 : 0 < x := by linarith
  have hB1 : (1 : ℝ) ≤ 2 * x := by linarith
  set g : Zall → ℂ := fun ρ => wterm b ρ.1 - wterm a ρ.1 with hg
  have hsa : Summable (fun ρ : Zall => wterm a ρ.1) :=
    Summable.of_norm_bounded (summable_hw.mul_left ((2 * x + 1) ^ 2))
      (fun ρ => norm_wterm_le ha (by linarith) ρ.2)
  have hsb : Summable (fun ρ : Zall => wterm b ρ.1) :=
    Summable.of_norm_bounded (summable_hw.mul_left ((2 * x + 1) ^ 2))
      (fun ρ => norm_wterm_le (by linarith) hb ρ.2)
  have hW : Wf b - Wf a = ∑' ρ : Zall, g ρ := by
    rw [Wf, Wf, ← hsb.tsum_sub hsa]
  have hre0 : ∀ ρ : Zall, 0 < ρ.1.re := by
    intro ρ
    have hz := (Set.ext_iff.mp Zall_eq (ρ : ℂ)).mp ρ.2
    exact hz.2.1
  have hρ0 : ∀ ρ : Zall, ρ.1 ≠ 0 := fun ρ h => by
    have := hre0 ρ; rw [h] at this; simp at this
  have hρ1 : ∀ ρ : Zall, ρ.1 + 1 ≠ 0 := fun ρ h => by
    have := congr_arg re h
    simp only [add_re, one_re, zero_re] at this
    linarith [hre0 ρ]
  -- bound A per zero
  have hA : ∀ ρ : Zall, ‖g ρ‖ ≤ (b - a) * (2 * x) ^ theta *
      ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖) := by
    intro ρ
    have e : g ρ = (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        ((∫ y in a..b, (y : ℂ) ^ ρ.1) / ρ.1) := by
      simp only [hg, wterm]
      rw [integral_cpow (Or.inl (by linarith [hre0 ρ]))]
      have := hρ0 ρ; have := hρ1 ρ
      field_simp
    rw [e, norm_mul, norm_div, Complex.norm_natCast]
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := (2 * x) ^ theta) (f := fun y : ℝ => (y : ℂ) ^ ρ.1) (fun y hy => by
        rw [Set.uIoc_of_le hab] at hy
        exact norm_cpow_le_of_le (by linarith [hy.1]) (by linarith [hy.2]) hB1
          (by linarith [hre0 ρ]) (hzeros ρ))
    rw [abs_of_nonneg (by linarith)] at hint
    have hn : 0 < ‖ρ.1‖ := norm_pos_iff.mpr (hρ0 ρ)
    calc (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (‖∫ y in a..b, (y : ℂ) ^ ρ.1‖ / ‖ρ.1‖)
        ≤ (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * ((2 * x) ^ theta * (b - a) / ‖ρ.1‖) := by
          gcongr
      _ = _ := by ring
  -- bound B per zero
  have hBz : ∀ ρ : Zall, ‖g ρ‖ ≤ 2 * (2 * x) ^ (theta + 1) *
      ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) := by
    intro ρ
    have hr0 : 0 < (ρ.1 + 1).re := by simp only [add_re, one_re]; linarith [hre0 ρ]
    have hr : (ρ.1 + 1).re ≤ theta + 1 := by simp only [add_re, one_re]; linarith [hzeros ρ]
    have b1 := norm_cpow_le_of_le (y := b) (by linarith) hb hB1 (r := ρ.1 + 1) hr0 hr
    have b2 := norm_cpow_le_of_le (y := a) ha (by linarith) hB1 (r := ρ.1 + 1) hr0 hr
    have hden : ‖ρ.1‖ ^ 2 ≤ ‖ρ.1 * (ρ.1 + 1)‖ := by
      rw [norm_mul, sq]
      have := norm_le_norm_add (ρ := ρ.1) (by linarith [hre0 ρ]) (k := 1) zero_le_one
      push_cast at this
      gcongr
    have hn : 0 < ‖ρ.1‖ ^ 2 := by have := norm_pos_iff.mpr (hρ0 ρ); positivity
    simp only [hg, wterm]
    rw [← mul_sub, ← sub_div, norm_mul, norm_div, Complex.norm_natCast]
    have hnum : ‖(b : ℂ) ^ (ρ.1 + 1) - (a : ℂ) ^ (ρ.1 + 1)‖ ≤ 2 * (2 * x) ^ (theta + 1) := by
      have := norm_sub_le ((b : ℂ) ^ (ρ.1 + 1)) ((a : ℂ) ^ (ρ.1 + 1)); linarith
    calc (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
          (‖(b : ℂ) ^ (ρ.1 + 1) - (a : ℂ) ^ (ρ.1 + 1)‖ / ‖ρ.1 * (ρ.1 + 1)‖)
        ≤ (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (2 * (2 * x) ^ (theta + 1) / ‖ρ.1‖ ^ 2) := by
          gcongr
      _ = _ := by ring
  have hgs : Summable (fun ρ : Zall => ‖g ρ‖) := by
    refine Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) (fun ρ => ?_)
      ((summable_hw.mul_left ((2 * x + 1) ^ 2)).add (summable_hw.mul_left ((2 * x + 1) ^ 2)))
    exact (norm_sub_le _ _).trans (add_le_add (norm_wterm_le (by linarith) hb ρ.2)
      (norm_wterm_le ha (by linarith) ρ.2))
  rw [hW]
  refine (norm_tsum_le_tsum_norm hgs).trans (Real.tsum_le_of_sum_le (fun ρ => norm_nonneg _) ?_)
  intro u
  rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.1‖ ≤ x)]
  apply add_le_add
  · calc ∑ ρ ∈ u.filter (fun ρ => ‖ρ.1‖ ≤ x), ‖g ρ‖
        ≤ ∑ ρ ∈ u.filter (fun ρ => ‖ρ.1‖ ≤ x), (b - a) * (2 * x) ^ theta *
            ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖) := sum_le_sum fun ρ _ => hA ρ
      _ = (b - a) * (2 * x) ^ theta * ∑ ρ ∈ (u.filter (fun ρ => ‖ρ.1‖ ≤ x)).map
            (Function.Embedding.subtype _), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
          rw [Finset.sum_map, Finset.mul_sum]; rfl
      _ ≤ (b - a) * (2 * x) ^ theta * ∑ ρ ∈ (zeros_rect_finite 2 x).toFinset,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
          have : 0 ≤ (b - a) * (2 * x) ^ theta := by
            have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * x by linarith) theta
            nlinarith
          gcongr
          intro ρ hρ
          rw [Finset.mem_map] at hρ
          obtain ⟨⟨ρ', hρ'Z⟩, hρ'u, rfl⟩ := hρ
          rw [Finset.mem_filter] at hρ'u
          rw [Set.Finite.mem_toFinset]
          have hre1 := Zall_re_lt hρ'Z
          have him : |ρ'.im| ≤ x := le_trans (abs_im_le_norm _) hρ'u.2
          refine ⟨(mem_rect (by norm_num) (by linarith)).mpr
            ⟨⟨hρ'Z.2, by simp; linarith⟩, abs_le.mp ?_⟩, hρ'Z.1⟩
          simpa using him
      _ ≤ (b - a) * (2 * x) ^ theta * (C1 * (Real.log x + 1) ^ 2) := by
          have : 0 ≤ (b - a) * (2 * x) ^ theta := by
            have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * x by linarith) theta
            nlinarith
          gcongr; exact hZ1 x (by linarith)
  · calc ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ x), ‖g ρ‖
        ≤ ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ x), 2 * (2 * x) ^ (theta + 1) *
            ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) := sum_le_sum fun ρ _ => hBz ρ
      _ = 2 * (2 * x) ^ (theta + 1) * ∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ x)).map
            (Function.Embedding.subtype _), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 := by
          rw [Finset.sum_map, Finset.mul_sum]; rfl
      _ ≤ 2 * (2 * x) ^ (theta + 1) * (C2 * (Real.log x + 1) / x) := by
          gcongr
          apply hZ2 x hx
          intro ρ hρ
          rw [Finset.mem_map] at hρ
          obtain ⟨⟨ρ', hρ'Z⟩, hρ'u, rfl⟩ := hρ
          rw [Finset.mem_filter] at hρ'u
          have h := hρ'Z
          rw [Zall_eq] at h
          exact ⟨h.1, h.2.1, h.2.2, lt_of_not_ge hρ'u.2⟩
      _ = (2 * x) ^ (theta + 1) * (2 * C2 * (Real.log x + 1) / x) := by ring


/-- Ingham bound from a uniform bound on the real parts of the zeros. -/
theorem ingham_of_zero_bound (theta : ℝ) (htheta : 1 / 2 ≤ theta) (htheta1 : theta < 1)
    (hzeros : ∀ ρ : Zall, ρ.1.re ≤ theta) :
    ∃ C : ℝ, ∀ x : ℝ, 6 ≤ x → |ψ x - x| ≤ C * x ^ theta * Real.log x ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := psi1_sqrt
  obtain ⟨D1, D2, hD1, hD2, hW⟩ := dW_theta theta (by linarith) hzeros
  set d0 : ℂ := deriv riemannZeta 0 / riemannZeta 0 with hd0
  refine ⟨1 / 2 + ‖d0‖ + 8 * D1 + 16 * D2 + 4 * K, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set h := x ^ theta with hh
  have hh0 : 0 < h := Real.rpow_pos_of_pos hx0 _
  have hsqrth : Real.sqrt x ≤ h := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) htheta
  have hh1 : 2 ≤ h := by
    have hs : (2 : ℝ) ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by linarith)
    linarith
  have hhxlt : h < x := by
    calc h < x ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) htheta1
      _ = x := Real.rpow_one _
  have hhx : h ≤ x := hhxlt.le
  set M := ⌈2 * x⌉₊ with hM
  have h2xM : 2 * x ≤ M := Nat.le_ceil _
  set L := Real.log x with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9; linarith
  -- the general difference bound
  have G : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * x →
      |Rg M b - Rg M a - (b ^ 2 - a ^ 2) / 2| ≤ (b - a) * ‖d0‖ + ‖Wf b - Wf a‖ +
        K * (b ^ (1 / 2 : ℝ) + a ^ (1 / 2 : ℝ)) := by
    intro a b ha hab hb
    have ea := hK M a ha (by linarith)
    have eb := hK M b (by linarith) (by linarith)
    set Ea := ((Rg M a : ℝ) : ℂ) - ((((a ^ 2 / 2 : ℝ)) : ℂ) - a * d0 - Wf a)
    set Eb := ((Rg M b : ℝ) : ℂ) - ((((b ^ 2 / 2 : ℝ)) : ℂ) - b * d0 - Wf b)
    have e : (((Rg M b - Rg M a - (b ^ 2 - a ^ 2) / 2 : ℝ)) : ℂ) =
        -(((b - a : ℝ) : ℂ) * d0) - (Wf b - Wf a) + (Eb - Ea) := by
      simp only [Ea, Eb]; push_cast; ring
    have habs : |Rg M b - Rg M a - (b ^ 2 - a ^ 2) / 2| =
        ‖(((Rg M b - Rg M a - (b ^ 2 - a ^ 2) / 2 : ℝ)) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [habs, e]
    have n1 : ‖((b - a : ℝ) : ℂ) * d0‖ = (b - a) * ‖d0‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    calc ‖-(((b - a : ℝ) : ℂ) * d0) - (Wf b - Wf a) + (Eb - Ea)‖
        ≤ ‖-(((b - a : ℝ) : ℂ) * d0)‖ + ‖Wf b - Wf a‖ + (‖Eb‖ + ‖Ea‖) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _)) (norm_sub_le _ _))
      _ ≤ (b - a) * ‖d0‖ + ‖Wf b - Wf a‖ + K * (b ^ (1 / 2 : ℝ) + a ^ (1 / 2 : ℝ)) := by
          rw [norm_neg, n1]
          have : K * a ^ (1 / 2 : ℝ) + K * b ^ (1 / 2 : ℝ) =
              K * (b ^ (1 / 2 : ℝ) + a ^ (1 / 2 : ℝ)) := by ring
          linarith
  -- common size of the error
  have hs2 : (2 * x) ^ (1 / 2 : ℝ) ≤ 2 * h := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    calc Real.sqrt 2 * Real.sqrt x ≤ 2 * Real.sqrt x := by gcongr
      _ ≤ 2 * h := by gcongr
  have hstheta : (2 * x) ^ theta ≤ 2 * h := by
    rw [Real.mul_rpow (by norm_num) hx0.le]
    have : (2 : ℝ) ^ theta ≤ 2 := by
      calc (2 : ℝ) ^ theta ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) htheta1.le
        _ = 2 := Real.rpow_one _
    exact mul_le_mul_of_nonneg_right this hh0.le
  have hs32 : (2 * x) ^ (theta + 1) ≤ 4 * x * h := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_right hstheta (by positivity : 0 ≤ 2 * x)]
  have hrp : ∀ y : ℝ, 0 ≤ y → y ≤ 2 * x → y ^ (1 / 2 : ℝ) ≤ 2 * h := fun y hy hyx =>
    (Real.rpow_le_rpow hy hyx (by norm_num)).trans hs2
  -- the zero sum difference over a step `h`
  have hWb : ∀ a b : ℝ, 0 ≤ a → b = a + h → b ≤ 2 * x →
      ‖Wf b - Wf a‖ ≤ h * (2 * h) * (D1 * (L + 1) ^ 2) + 4 * x * h * (2 * D2 * (L + 1) / x) := by
    intro a b ha hb hbx
    refine (hW x hx a b ha (by linarith) hbx).trans ?_
    rw [show b - a = h by linarith]
    have : 0 ≤ D1 * (L + 1) ^ 2 := by positivity
    have : 0 ≤ 2 * D2 * (L + 1) / x := by have : 0 ≤ L := by linarith
                                          positivity
    gcongr
  set Err := h * ‖d0‖ + (h * (2 * h) * (D1 * (L + 1) ^ 2) + 4 * x * h * (2 * D2 * (L + 1) / x)) +
    K * (2 * h + 2 * h) with hErr
  -- upper bound
  have hup : h * ψ x ≤ h * x + h * h / 2 + Err := by
    have g1 := Rg_sub_ge (M := M) (a := x) (b := x + h) hx0.le (by linarith) (by linarith)
    have g2 := G x (x + h) hx0 (by linarith) (by linarith)
    have g3 := hWb x (x + h) hx0.le rfl (by linarith)
    have r1 := hrp (x + h) (by linarith) (by linarith)
    have r2 := hrp x hx0.le (by linarith)
    rw [show x + h - x = h by ring] at g1 g2
    have habs := (abs_le.mp g2).2
    have : K * ((x + h) ^ (1 / 2 : ℝ) + x ^ (1 / 2 : ℝ)) ≤ K * (2 * h + 2 * h) := by gcongr
    have e : ((x + h) ^ 2 - x ^ 2) / 2 = h * x + h * h / 2 := by ring
    rw [e] at habs
    linarith
  -- lower bound
  have hlo : h * x - h * h / 2 - Err ≤ h * ψ x := by
    have g1 := Rg_sub_le (M := M) (a := x - h) (b := x) (by linarith) (by linarith) (by linarith)
    have g2 := G (x - h) x (by nlinarith) (by linarith) (by linarith)
    have g3 := hWb (x - h) x (by linarith) (by ring) (by linarith)
    have r1 := hrp x hx0.le (by linarith)
    have r2 := hrp (x - h) (by linarith) (by linarith)
    rw [show x - (x - h) = h by ring] at g1 g2
    have habs := (abs_le.mp g2).1
    have : K * (x ^ (1 / 2 : ℝ) + (x - h) ^ (1 / 2 : ℝ)) ≤ K * (2 * h + 2 * h) := by gcongr
    have e : (x ^ 2 - (x - h) ^ 2) / 2 = h * x - h * h / 2 := by ring
    rw [e] at habs
    linarith
  -- divide by `h`
  have hErrh : Err = h * (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 8 * D2 * (L + 1) + 4 * K) := by
    rw [hErr]; field_simp; ring
  have hfin : |ψ x - x| ≤ h / 2 + (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 8 * D2 * (L + 1) + 4 * K) := by
    rw [hErrh] at hup hlo
    rw [abs_le]
    constructor
    · have : h * (x - h / 2 - (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 8 * D2 * (L + 1) + 4 * K)) ≤
          h * ψ x := by
        have : h * (x - h / 2 - (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 8 * D2 * (L + 1) + 4 * K)) =
            h * x - h * h / 2 - h * (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 8 * D2 * (L + 1) + 4 * K) := by
          ring
        linarith
      have := le_of_mul_le_mul_left this hh0
      linarith
    · have : h * ψ x ≤ h * (x + h / 2 + (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 8 * D2 * (L + 1) + 4 * K)) := by
        nlinarith
      have := le_of_mul_le_mul_left this hh0
      linarith
  have hf := final_arith (h := h) (L := L) (d := ‖d0‖) (D1 := D1)
    (D2 := 4 / 3 * D2) (K := K) (by linarith) hL1 (norm_nonneg _) hD1
    (by positivity) hK0
  have hfinal : h / 2 + (‖d0‖ + 2 * h * D1 * (L + 1) ^ 2 + 8 * D2 * (L + 1) + 4 * K) ≤
      (1 / 2 + ‖d0‖ + 8 * D1 + 16 * D2 + 4 * K) * h * L ^ 2 := by
    convert hf using 1 <;> ring
  exact hfin.trans hfinal

/-- Ingham's bound at the supremum Theta, assuming 1/2 ≤ Theta < 1. -/
theorem ingham_theta (htheta : 1 / 2 ≤ Theta) (htheta1 : Theta < 1) :
    ∃ C : ℝ, ∀ x : ℝ, 6 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ Theta * Real.log x ^ 2 := by
  apply ingham_of_zero_bound Theta htheta htheta1
  intro ρ
  have hz := (Set.ext_iff.mp Zall_eq (ρ : ℂ)).mp ρ.2
  exact GSCor2.re_le_Theta ⟨ρ.1, hz⟩

/-- Concrete parameter instance for the zero difference estimate at theta equals one. -/
theorem dW_at_one : ∃ D1 D2 : ℝ, 0 ≤ D1 ∧ 0 ≤ D2 ∧
    ∀ x : ℝ, 6 ≤ x → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 2 * x →
    ‖Wf b - Wf a‖ ≤ (b - a) * (2 * x) ^ (1 : ℝ) * (D1 * (Real.log x + 1) ^ 2) +
      (2 * x) ^ ((1 : ℝ) + 1) * (2 * D2 * (Real.log x + 1) / x) := by
  apply dW_theta 1 (by norm_num)
  intro ρ
  exact (Zall_re_lt ρ.2).le

/-- At theta equals one half, RH supplies the zero bound. -/
theorem ingham_half_of_RH (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ x : ℝ, 6 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ ((1 : ℝ) / 2) * Real.log x ^ 2 := by
  apply ingham_of_zero_bound (1 / 2) (by norm_num) (by norm_num)
  intro ρ
  exact (rh_re hRH ρ.2).le

end LeanLab.GoldbachAverage.InghamTheta
