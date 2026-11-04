import LeanLab.GoldbachGaps.MainLemmaFourier

/-!
P0030 Goldston 1990 page 288, the unweighted tail estimate in Lemma 1.
Mathlib supplies the finite telescoping identity and Jordan's sine inequality.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.GoldbachGaps.MainLemmaTail
open Finset MeasureTheory

/-- The geometric sum bound before division by the distance to its pole. -/
theorem unweighted_sum_pole_bound (N : ℕ) (x : AddCircle (1 : ℝ)) :
    ‖∑ k ∈ Icc 1 N, fourier (k : ℤ) x‖ * ‖fourier 1 x - 1‖ ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have ht : ∑ k ∈ Icc 1 N, (fourier ((k : ℤ) + 1) x - fourier (k : ℤ) x) =
      fourier ((N : ℤ) + 1) x - fourier 1 x := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Finset.sum_Icc_sub hN (fun k : ℕ => fourier (k : ℤ) x))
  have he : (∑ k ∈ Icc 1 N, fourier (k : ℤ) x) * (fourier 1 x - 1) =
      fourier ((N : ℤ) + 1) x - fourier 1 x := by
    rw [sum_mul, ← ht]
    apply sum_congr rfl
    intro k hk
    rw [fourier_add]
    ring
  have hn (k : ℤ) : ‖fourier k x‖ = 1 := by rw [fourier_apply, Circle.norm_coe]
  calc ‖∑ k ∈ Icc 1 N, fourier (k : ℤ) x‖ * ‖fourier 1 x - 1‖
      = ‖(∑ k ∈ Icc 1 N, fourier (k : ℤ) x) * (fourier 1 x - 1)‖ := (norm_mul _ _).symm
    _ = ‖fourier ((N : ℤ) + 1) x - fourier 1 x‖ := by rw [he]
    _ ≤ ‖fourier ((N : ℤ) + 1) x‖ + ‖fourier 1 x‖ := norm_sub_le _ _
    _ = 2 := by rw [hn, hn]; norm_num

/-- The unweighted exponential sum is bounded by one over twice the distance to zero. -/
theorem unweighted_sum_norm_le (N : ℕ) {x : ℝ} (hx0 : 0 < |x|) (hx1 : |x| ≤ 1 / 2) :
    ‖∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)‖ ≤
      1 / (2 * |x|) := by
  have hden : ‖fourier 1 (x : AddCircle (1 : ℝ)) - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
    rw [fourier_coe_apply]
    norm_num only [Int.cast_one, Complex.ofReal_one, mul_one, div_one]
    have he : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) =
        Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * x) / 2 = Real.pi * x by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have ht : |Real.pi * x| ≤ Real.pi / 2 := by
    calc |Real.pi * x| = Real.pi * |x| := by rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hx1 Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have hs := Real.mul_abs_le_abs_sin ht
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have he : 2 / Real.pi * (Real.pi * |x|) = 2 * |x| := by field_simp
  rw [he] at hs
  have hd : 4 * |x| ≤ ‖fourier 1 (x : AddCircle (1 : ℝ)) - 1‖ := by
    rw [hden]; linarith
  have hp := unweighted_sum_pole_bound N (x : AddCircle (1 : ℝ))
  have hm := mul_le_mul_of_nonneg_left hd
    (norm_nonneg (∑ k ∈ Icc 1 N, fourier (k : ℤ) (x : AddCircle (1 : ℝ))))
  have hb := hm.trans hp
  have hout : ‖∑ k ∈ Icc 1 N, fourier (k : ℤ) (x : AddCircle (1 : ℝ))‖ ≤
      1 / (2 * |x|) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hx0)).mpr
    nlinarith
  simpa only [fourier_coe_apply, Complex.ofReal_one, Int.cast_natCast, div_one] using hout

/-- Integrate the unweighted inverse square majorant on an interval avoiding zero. -/
theorem unweighted_tail_interval_le (N n : ℕ) {a b : ℝ} (hab : a ≤ b)
    (hzero : (0 : ℝ) ∉ Set.Icc a b)
    (hsmall : ∀ x ∈ Set.Icc a b, |x| ≤ 1 / 2) :
    ‖∫ x in a..b,
      (∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))‖ ≤
      (a⁻¹ - b⁻¹) / 4 := by
  have hz : (0 : ℝ) ∉ Set.uIcc a b := by simpa only [Set.uIcc_of_le hab] using hzero
  have hphase (x : ℝ) :
      ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))‖ = 1 := by
    have hh : ‖fourier (-(n : ℤ)) (x : AddCircle (1 : ℝ))‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    simpa only [fourier_coe_apply, Complex.ofReal_one, div_one, Int.cast_neg,
      Int.cast_natCast, mul_neg, neg_mul] using hh
  have hp : ∀ x ∈ Set.Icc a b,
      ‖(∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))‖ ≤
        (1 / 4 : ℝ) * x ^ (-2 : ℤ) := by
    intro x hx
    have hxzero : x ≠ 0 := fun he => hzero (he ▸ hx)
    have hxabs : 0 < |x| := abs_pos.mpr hxzero
    rw [norm_mul, norm_pow, hphase, mul_one]
    refine (pow_le_pow_left₀ (norm_nonneg _) (unweighted_sum_norm_le N hxabs (hsmall x hx)) 2).trans_eq ?_
    rw [zpow_neg, zpow_ofNat]
    field_simp [hxzero, hxabs.ne', sq_abs] ; nlinarith [sq_abs x]
  have hi : IntervalIntegrable (fun x : ℝ => (1 / 4 : ℝ) * x ^ (-2 : ℤ)) volume a b :=
    (intervalIntegral.intervalIntegrable_zpow (n := (-2 : ℤ)) (Or.inr hz)).const_mul _
  refine (intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun x hx => hp x ⟨hx.1.le, hx.2⟩) hi).trans_eq ?_
  rw [intervalIntegral.integral_const_mul,
    integral_zpow (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hz⟩)]
  norm_num ; ring

/-- The two omitted tails give an explicit error for the unweighted small arc. -/
theorem unweighted_small_arc_error (N n : ℕ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 2) :
    ‖(∫ x in (-β)..β,
      (∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))) -
    (∫ x in (-1 / 2 : ℝ)..(1 / 2),
      (∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x)))‖ ≤
      1 / (2 * β) - 1 := by
  let f : ℝ → ℂ := fun x =>
    (∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hL := unweighted_tail_interval_le N n
    (a := (-1 / 2 : ℝ)) (b := -β) (by linarith)
    (by rintro ⟨h1, h2⟩; linarith)
    (fun x hx => abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hR := unweighted_tail_interval_le N n
    (a := β) (b := (1 / 2 : ℝ)) hβ1
    (by rintro ⟨h1, h2⟩; linarith)
    (fun x hx => abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-1 / 2) (-β)) (hf.intervalIntegrable (μ := volume) (-β) (1 / 2))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-β) β) (hf.intervalIntegrable (μ := volume) β (1 / 2))
  have he : (∫ x in (-β)..β, f x) - (∫ x in (-1 / 2 : ℝ)..(1 / 2), f x) =
      -((∫ x in (-1 / 2 : ℝ)..(-β), f x) + (∫ x in β..(1 / 2), f x)) := by
    rw [← hs1, ← hs2]
    abel
  change ‖(∫ x in (-β)..β, f x) - (∫ x in (-1 / 2 : ℝ)..(1 / 2), f x)‖ ≤ _
  calc _ = ‖(∫ x in (-1 / 2 : ℝ)..(-β), f x) + (∫ x in β..(1 / 2), f x)‖ := by
          rw [he, norm_neg]
    _ ≤ ‖∫ x in (-1 / 2 : ℝ)..(-β), f x‖ + ‖∫ x in β..(1 / 2), f x‖ := norm_add_le _ _
    _ ≤ ((-1 / 2 : ℝ)⁻¹ - (-β)⁻¹) / 4 + (β⁻¹ - (1 / 2 : ℝ)⁻¹) / 4 := add_le_add hL hR
    _ = 1 / (2 * β) - 1 := by field_simp [hβ0.ne'] ; ring

/-- The unweighted small arc term has the paper's triangular main term and an explicit error. -/
theorem unweighted_main_term_error (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ 2 * N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 2) :
    ‖(∫ x in (-β)..β,
      (∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))) -
      (min (n - 1) (2 * N - n + 1) : ℕ)‖ ≤ 1 / (2 * β) - 1 := by
  have h := unweighted_small_arc_error N n hβ0 hβ1
  rwa [LeanLab.GoldbachGaps.MainLemmaFourier.unweighted_square_integral N n hn hnN] at h

end LeanLab.GoldbachGaps.MainLemmaTail
