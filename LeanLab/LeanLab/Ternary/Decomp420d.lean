/-
MMS https://arxiv.org/abs/1610.02017v2, page 12, unsmoothing and normalization.
Separate the uniform Fourier estimate with the actual reference mean
from the elementary replacement of that mean by its limiting value.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420c
import LeanLab.Ternary.MMSBohrSmoothing
import LeanLab.Halupczok2012.U1439Combin

namespace LeanLab.Ternary.MMS.Task420
open Finset Filter Topology

/-- The MMS wheel is the standard primorial at its stated logarithmic cutoff.
MMS page 12 definition of W. -/
theorem wheel_eq_primorial (x : ℝ) :
    wheel x = primorial ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ := rfl

/-- The wheel modulus is positive at every real x.
MMS page 12 definition of W and Mathlib primorial_pos. -/
theorem wheel_pos (x : ℝ) : 0 < wheel x := by
  rw [wheel_eq_primorial]
  exact primorial_pos _

/-- The wheel is at most log x once x is at least exp one.
Derived elementary size bound for the normalization on MMS page 12. -/
theorem wheel_le_log {x : ℝ} (hx : Real.exp 1 ≤ x) : (wheel x : ℝ) ≤ Real.log x := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlx : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    simpa only [Real.log_exp] using h
  have hll : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlx
  have hf := Nat.floor_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.1) hll)
  have hfour : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hpow : (wheel x : ℝ) ≤ (4 : ℝ) ^ ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ := by
    rw [wheel_eq_primorial]
    exact_mod_cast primorial_le_four_pow ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊
  calc
    _ ≤ (4 : ℝ) ^ ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ := hpow
    _ = Real.exp (Real.log 4 * (⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    _ ≤ Real.exp (Real.log (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hf
        (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
      have hmul' := mul_le_mul_of_nonneg_right hfour hll
      nlinarith
    _ = Real.log x := Real.exp_log (by linarith)

/-- Every positive power of x eventually dominates the wheel.
Derived growth bound for the limiting mean replacement on MMS page 12. -/
theorem eventual_wheel_le_rpow (θ : ℝ) (hθ : 0 < θ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → Real.exp 1 ≤ x ∧ (wheel x : ℝ) ≤ x ^ θ := by
  have hsmall := (isLittleO_log_rpow_atTop hθ).bound (by norm_num : (0 : ℝ) < 1)
  apply eventually_atTop.mp
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 1)] with x hx hxe
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hlog : 0 ≤ Real.log x := (wheel_le_log hxe).trans' (by positivity : 0 ≤ (wheel x : ℝ))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hx
  exact ⟨hxe, (wheel_le_log hxe).trans hx⟩

/-- One reduced wheel class contains at most four x to power theta divided by W integers.
The factor four absorbs the two closed endpoints. MMS page 12 normalization.
The proved general residue class count from Halupczok2012 is reused. -/
theorem class_card_mul_wheel_le {θ x : ℝ} (hx : 1 ≤ x)
    (hW : (wheel x : ℝ) ≤ x ^ θ) (c : ℕ) :
    (wheel x : ℝ) *
      (((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x])).card : ℝ) ≤ 4 * x ^ θ := by
  let S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
    (fun n => n ≡ c [MOD wheel x])
  have hx0 : 0 < x := by linarith
  have hp : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hw0 : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have hw1 : (1 : ℝ) ≤ wheel x := by exact_mod_cast wheel_pos x
  have hcount := LeanLab.Halupczok2012.card_cong_le (S := S)
    (x := x - x ^ θ / 3 - 1) (y := 4 * x ^ θ / 3 + 1) (l := wheel x)
    (wheel_pos x) (by positivity) ?_ ?_
  · have hm : ((S.card : ℝ) - 1) * wheel x ≤ 4 * x ^ θ / 3 + 1 :=
      (le_div_iff₀ hw0).mp (by linarith)
    change (wheel x : ℝ) * (S.card : ℝ) ≤ 4 * x ^ θ
    nlinarith
  · intro n hn
    obtain ⟨hn, hnc⟩ := mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
    have hnlo : x - x ^ θ / 3 ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hlo)
    have hnhi : (n : ℝ) ≤ x + x ^ θ :=
      (show (n : ℝ) ≤ (⌊x + x ^ θ⌋₊ : ℝ) by exact_mod_cast hhi).trans
        (Nat.floor_le (by linarith))
    exact ⟨by linarith, by linarith⟩
  · intro n hn m hm
    have hn' := (mem_filter.mp hn).2
    have hm' := (mem_filter.mp hm).2
    exact Int.natCast_modEq_iff.mpr (hn'.trans hm'.symm)

/-- The unweighted exponential sum in a wheel class has the same cardinality bound.
MMS page 12, the coefficient replacement after unsmoothing. -/
theorem class_fourier_mul_wheel_le {θ x : ℝ} (hx : 1 ≤ x)
    (hW : (wheel x : ℝ) ≤ x ^ θ) (c : ℕ) (γ : ℝ) :
    (wheel x : ℝ) *
      ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x]), e (n * γ)‖ ≤ 4 * x ^ θ := by
  have hn := norm_sum_le
    ((ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]))
    (fun n => e (n * γ))
  simp only [norm_e, sum_const, nsmul_eq_mul, mul_one] at hn
  exact (mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ wheel x)).trans
    (class_card_mul_wheel_le hx hW c)

/-- Replacing a Fourier mean costs four times its scalar error.
MMS page 12, the limiting coefficient replacement. The normalization denominator
is written as the positive product of the totient and log x. -/
theorem mean_replacement_norm {A Z : ℂ} {W φ L r α β η : ℝ}
    (hW : 0 ≤ W) (hφ : 0 < φ) (hL : 0 < L)
    (hZ : W * ‖Z‖ ≤ 4 * r)
    (hA : ‖A - ((α / L * (W / φ) : ℝ) : ℂ) * Z‖ ≤ η * r / (φ * L)) :
    ‖A - ((β / L * (W / φ) : ℝ) : ℂ) * Z‖ ≤
      (η + 4 * |α - β|) * r / (φ * L) := by
  have hd : 0 < φ * L := mul_pos hφ hL
  have hc : α / L * (W / φ) - β / L * (W / φ) = (α - β) * W / (φ * L) := by
    field_simp
  have he : A - ((β / L * (W / φ) : ℝ) : ℂ) * Z =
      (A - ((α / L * (W / φ) : ℝ) : ℂ) * Z) +
        (((α - β) * W / (φ * L) : ℝ) : ℂ) * Z := by
    rw [← hc]
    push_cast
    ring
  have hterm : ‖(((α - β) * W / (φ * L) : ℝ) : ℂ) * Z‖ ≤
      4 * |α - β| * r / (φ * L) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg hW, abs_of_pos hd]
    calc
      _ = (|α - β| * (W * ‖Z‖)) / (φ * L) := by ring
      _ ≤ (|α - β| * (4 * r)) / (φ * L) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hZ (abs_nonneg _)) hd.le
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ ‖A - ((α / L * (W / φ) : ℝ) : ℂ) * Z‖ +
        ‖(((α - β) * W / (φ * L) : ℝ) : ℂ) * Z‖ := norm_add_le _ _
    _ ≤ η * r / (φ * L) + 4 * |α - β| * r / (φ * L) := add_le_add hA hterm
    _ = _ := by ring

/-- Hyp1 is stable when its mean changes by a controlled amount.
MMS page 12 coefficient replacement. CONDITIONAL ON the explicit Hyp1 input. -/
theorem hyp1_change_mean {θ x α β η : ℝ} {ρp : ℕ → ℝ} (hx : 1 < x)
    (hW : (wheel x : ℝ) ≤ x ^ θ) (H : Hyp1 θ x α η ρp) :
    Hyp1 θ x β (η + 4 * |α - β|) ρp := by
  intro c hc γ
  have hφ : (0 : ℝ) < (wheel x).totient := by
    exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  exact mean_replacement_norm (by positivity) hφ (Real.log_pos hx)
    (class_fourier_mul_wheel_le hx.le hW c γ) (H c hc γ)

/-- Increasing the allowed Fourier error preserves Hyp1.
MMS page 12, choosing the mean and Fourier tolerances before x.
CONDITIONAL ON the explicit Hyp1 input. -/
theorem hyp1_mono_error {θ x α η η' : ℝ} {ρp : ℕ → ℝ}
    (hx : 1 < x) (hη : η ≤ η') (H : Hyp1 θ x α η ρp) :
    Hyp1 θ x α η' ρp := by
  intro c hc γ
  apply (H c hc γ).trans
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hη (Real.rpow_nonneg (by linarith) _)
  · exact mul_nonneg (by positivity) (Real.log_pos hx).le

/-- LEAF. The actual reference mean normalizes the uniform short interval Fourier estimate.
MMS page 11 Proposition 5.1 and page 12 unsmoothing displays, before replacing
the long reference mean by its limiting coefficient. The written cancellation
proof is in sections 5.1 to 5.3, pages 13 to 27. No limiting mean value or
numerical Buchstab integral bound is assumed or concluded here. -/
theorem harman_fourier_reference_input (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Hyp1 θ x (Task379.referenceMean x) η (Task361.harmanMajorant x) := by
  sorry

/-- The exact existing Fourier transfer statement from the reference mean estimate.
MMS page 12 last normalization step. The limiting mean hypothesis stays explicit.
CONDITIONAL ON harman_fourier_reference_input and the stated convergence input. -/
theorem harman_fourier_of_reference_mean_decomposed
    (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) (αp : ℝ)
    (hmean : ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |Task379.referenceMean x - αp| ≤ δ) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Hyp1 θ x αp η (Task361.harmanMajorant x) := by
  intro η hη
  obtain ⟨X₁, hX₁⟩ := harman_fourier_reference_input θ hθ hθ1 (η / 2) (by linarith)
  obtain ⟨X₂, hX₂⟩ := hmean (η / 8) (by linarith)
  obtain ⟨X₃, hX₃⟩ := eventual_wheel_le_rpow θ (by linarith)
  refine ⟨max X₁ (max X₂ X₃), ?_⟩
  intro x hx
  have hx₁ := (le_max_left X₁ (max X₂ X₃)).trans hx
  have hx₂ := (le_max_left X₂ X₃).trans ((le_max_right X₁ (max X₂ X₃)).trans hx)
  have hx₃ := (le_max_right X₂ X₃).trans ((le_max_right X₁ (max X₂ X₃)).trans hx)
  obtain ⟨hxe, hw⟩ := hX₃ x hx₃
  have hx1 : 1 < x := lt_of_lt_of_le (by linarith [Real.exp_one_gt_d9]) hxe
  have h := hyp1_change_mean (β := αp) hx1 hw (hX₁ x hx₁)
  exact hyp1_mono_error hx1 (by have := hX₂ x hx₂; linarith) h

/-- The exact existing fixed mean Fourier input follows from the two refined analytic leaves.
MMS pages 11 and 12. The numerical envelope is now proved.
CONDITIONAL ON harman_reference_mean_enveloped and harman_fourier_reference_input. -/
theorem harman_fourier_input_decomposed (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ αp : ℝ, 0 < αp ∧ αp < 2.9 ∧
      ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        Hyp1 θ x αp η (Task361.harmanMajorant x) := by
  obtain ⟨αp, hp, hp29, hmean⟩ := harman_reference_mean_decomposed
  exact ⟨αp, hp, hp29, harman_fourier_of_reference_mean_decomposed θ hθ hθ1 αp hmean⟩

end LeanLab.Ternary.MMS.Task420
