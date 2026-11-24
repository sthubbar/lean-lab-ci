import LeanLab.ExceptionalSet.SPLIT_leaf_one_sided_majorant

/-!
Feed of `LeanLab.ExceptionalSet.Decomp523a.leaf_fejer_convolution_majorant`,
burst-20261122 session S90, wave 2.

Finding: the leaf is FALSE as written. Its smoothing integral integrates
`K (x - t) * g (x - t)` over a full period, so by periodicity it equals
`∫ K * g` over one period and does not depend on `x`. When the enlarged interval
sits near `1 / 2`, the normalized Fejer type kernel `K` is at most one there,
so the smoothing integral is at most the mean of `g`, and the whole right side
is at most `12 * (b - a + 2 * s)`. At `H = 20`, `s = 1 / 42`, `a = 1 / 2`,
`b = 1 / 2 + 1 / 1000`, `x = 1 / 2` this is below `1`, the left side.
The intended statement has `g t` in place of `g (x - t)`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp523a

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC)

/-- Powers of `eC`. -/
theorem feed1122_fcm_eC_pow (k : ℕ) (u : ℝ) :
    eC (((k : ℝ) + 1) * u) = (eC u) ^ (k + 1) := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `eC` has unit norm. -/
theorem feed1122_fcm_norm_eC (u : ℝ) : ‖eC u‖ = 1 := by
  unfold eC
  rw [show (2 * (π : ℂ) * Complex.I * (u : ℂ)) = ((2 * π * u : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Real part of `eC`. -/
theorem feed1122_fcm_re_eC (u : ℝ) : (eC u).re = Real.cos (2 * π * u) := by
  unfold eC
  rw [show (2 * (π : ℂ) * Complex.I * (u : ℂ)) = ((2 * π * u : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- On the enlarged interval near `1 / 2`, `cos (2 π u) ≤ 0`. -/
theorem feed1122_fcm_cos_nonpos (u c L : ℝ) (hc : 1 / 4 ≤ c) (hcL : c + L ≤ 3 / 4)
    (hf : Int.fract (u - c) < L) : Real.cos (2 * π * u) ≤ 0 := by
  have hdec := Int.floor_add_fract (u - c)
  set f := Int.fract (u - c) with hfdef
  set n := ⌊u - c⌋ with hndef
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  have hu : 2 * π * u = (2 * π * (c + f - 1 / 2) + π) + (n : ℝ) * (2 * π) := by
    have : u = c + f + n := by linarith
    rw [this]; ring
  rw [hu, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  have hpi := Real.pi_pos
  have h1 : -(π / 2) ≤ 2 * π * (c + f - 1 / 2) := by nlinarith
  have h2 : 2 * π * (c + f - 1 / 2) ≤ π / 2 := by nlinarith
  have := Real.cos_nonneg_of_mem_Icc ⟨h1, h2⟩
  linarith

/-- The normalized kernel is at most one on the enlarged interval near `1 / 2`. -/
theorem feed1122_fcm_kernel_le (H : ℕ) (hH : 4 ≤ (H : ℝ)) (u c L : ℝ) (hc : 1 / 4 ≤ c)
    (hcL : c + L ≤ 3 / 4) (hf : Int.fract (u - c) < L) :
    (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * u)‖ ^ 2 ≤ 1 := by
  set z := eC u with hz
  have hS : ∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * u) = z * ∑ k ∈ Finset.range H, z ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [feed1122_fcm_eC_pow, pow_succ']
  have hgeom : (∑ k ∈ Finset.range H, z ^ k) * (z - 1) = z ^ H - 1 := geom_sum_mul z H
  have hzn : ‖z‖ = 1 := feed1122_fcm_norm_eC u
  have hzH : ‖z ^ H - 1‖ ≤ 2 := by
    calc ‖z ^ H - 1‖ ≤ ‖z ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hzn]; norm_num
  have hz1 : 1 ≤ ‖z - 1‖ := by
    have hre : (z - 1).re = Real.cos (2 * π * u) - 1 := by
      rw [Complex.sub_re, hz, feed1122_fcm_re_eC]; simp
    have hcos := feed1122_fcm_cos_nonpos u c L hc hcL hf
    have := Complex.abs_re_le_norm (z - 1)
    rw [hre, abs_of_neg (by linarith)] at this
    linarith
  have hSn : ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * u)‖ ≤ 2 := by
    rw [hS, norm_mul, hzn, one_mul]
    have hprod : ‖∑ k ∈ Finset.range H, z ^ k‖ * ‖z - 1‖ ≤ 2 := by
      rw [← norm_mul, hgeom]; exact hzH
    have h0 : 0 ≤ ‖∑ k ∈ Finset.range H, z ^ k‖ := norm_nonneg _
    nlinarith
  have hS2 : ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * u)‖ ^ 2 ≤ (H : ℝ) := by
    have h0 := norm_nonneg (∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * u))
    nlinarith
  have hHpos : 0 < (H : ℝ) := by linarith
  calc (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * u)‖ ^ 2
      ≤ (1 / (H : ℝ)) * (H : ℝ) := by gcongr
    _ = 1 := by field_simp

/-- The smoothing integral is at most the mean of the enlarged indicator. -/
theorem feed1122_fcm_integral_le (H : ℕ) (hH : 4 ≤ (H : ℝ)) (c L x : ℝ) (hc : 1 / 4 ≤ c)
    (hcL : c + L ≤ 3 / 4) :
    (∫ t in (0 : ℝ)..1,
        (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
          (if Int.fract (x - t - c) < L then (1 : ℝ) else 0))
      ≤ ∫ y in (0 : ℝ)..1, (if Int.fract (y - c) < L then (1 : ℝ) else 0) := by
  set G : ℝ → ℝ := fun y => if Int.fract (y - c) < L then (1 : ℝ) else 0 with hG
  have hGper : Function.Periodic G 1 := by
    intro y
    simp only [hG]
    rw [show y + 1 - c = (y - c) + 1 by ring, Int.fract_add_one]
  have hGmeas : Measurable G :=
    Measurable.ite (measurableSet_lt (measurable_fract.comp (by fun_prop)) measurable_const)
      measurable_const measurable_const
  have hshift : (∫ t in (0 : ℝ)..1, G (x - t)) = ∫ y in (0 : ℝ)..1, G y := by
    rw [intervalIntegral.integral_comp_sub_left (fun y => G y) x, sub_zero]
    have := hGper.intervalIntegral_add_eq (x - 1) 0
    rwa [sub_add_cancel, zero_add] at this
  have hint : IntervalIntegrable (fun t => G (x - t)) MeasureTheory.volume 0 1 := by
    refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => (1 : ℝ)) intervalIntegrable_const
      (hGmeas.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => ?_))
    simp only [hG]
    split_ifs <;> simp
  have hmono : (∫ t in (0 : ℝ)..1,
        (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 * G (x - t))
      ≤ ∫ t in (0 : ℝ)..1, G (x - t) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    apply MeasureTheory.integral_mono_of_nonneg
    · refine Filter.Eventually.of_forall (fun t => ?_)
      have hHpos : 0 < (H : ℝ) := by linarith
      have : 0 ≤ G (x - t) := by simp only [hG]; split_ifs <;> norm_num
      positivity
    · exact hint.1
    · refine Filter.Eventually.of_forall (fun t => ?_)
      simp only [hG]
      by_cases hf : Int.fract (x - t - c) < L
      · rw [if_pos hf, mul_one]
        exact feed1122_fcm_kernel_le H hH (x - t) c L hc hcL hf
      · rw [if_neg hf, mul_zero]
  calc _ = (∫ t in (0 : ℝ)..1,
        (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 * G (x - t)) :=
          rfl
    _ ≤ ∫ t in (0 : ℝ)..1, G (x - t) := hmono
    _ = ∫ y in (0 : ℝ)..1, G y := hshift

/-- FALSE finding for `leaf_fejer_convolution_majorant`: its universal closure
fails at `a = 1 / 2`, `b = 1 / 2 + 1 / 1000`, `H = 20`, `s = 1 / 42`, `x = 1 / 2`.
The right side is at most `12 * (b - a + 2 * s) < 1`. -/
theorem leaf_fejer_convolution_majorant_false :
    ¬ (∀ (a b : ℝ) (H : ℕ) (_ha : 0 ≤ a) (_hab : a ≤ b) (_hb : b ≤ 1) (_hH : 2 ≤ H)
        (s : ℝ) (_hs : 0 < s) (_hs2 : 2 * s = 1 / ((H : ℝ) + 1)),
        ∀ x : ℝ,
          (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
            12 * (∫ t in (0 : ℝ)..1,
              (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
                (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
              + 12 * (b - a + 2 * s)
              - 12 * (∫ y in (0 : ℝ)..1,
                  (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))) := by
  intro h
  have h1 := h (1 / 2) (1 / 2 + 1 / 1000) 20 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (1 / 42) (by norm_num) (by push_cast; norm_num) (1 / 2)
  have hfr : Int.fract (1 / 2 : ℝ) = 1 / 2 := Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  rw [hfr, if_pos ⟨le_refl _, by norm_num⟩] at h1
  have hI := feed1122_fcm_integral_le 20 (by norm_num) (1 / 2 - 1 / 42)
    (1 / 2 + 1 / 1000 - 1 / 2 + 2 * (1 / 42)) (1 / 2) (by norm_num) (by norm_num)
  have hL : 12 * (1 / 2 + 1 / 1000 - 1 / 2 + 2 * (1 / 42) : ℝ) < 1 := by norm_num
  linarith

end LeanLab.ExceptionalSet.Decomp523a
