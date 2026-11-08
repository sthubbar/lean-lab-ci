/-
WIP for SPLIT_lemma8, unit ExceptionalSet/SPLIT_lemma8, claim OMOS lomos 20261107T1204Z.
The three leaves of the file are open on main. The private helpers below are added by this run,
each compiled before the next was written. Nothing outside this file is touched.

Progress. The Fourier transform of the kernel `Kfun Δ` is the trapezoid
`β ↦ (1/Δ)(1-|β|)^+ - ((1-Δ)/Δ)(1-|β|/(1-Δ))^+`: the elementary sinc^2 transform
(`tri_cos`, `tri_sin`, `tri_fourier`), the scaling (`tri_scaled`), the shape (`trap_ft`) and
Mathlib's Fourier inversion (`kfun_fourier`). From it, `map_G` gives the Fourier transform of
`u ↦ Kfun Δ u * e(-uv)` at `m` as the trapezoid at `v + m`, and `periodization` is Poisson
summation in twisted form applied to that kernel: for `Δ ≤ v - ν ≤ 1 - Δ`,
`∑' n, Kfun Δ (t+n) e(-(t+n)v) = e(-νt) + e(-(ν+1)t)`. That is the engine of Lemma 1 of the
paper, redone from Mathlib instead of the file's `sorry`ed `LeanLab...U1539.lemma1`.
`majorArcs_add_int`/`majorArcs_periodic_set` are the `Z`-periodicity of the major arcs and the
covering of them by translates of `𝔑 ∩ [0,1]`, the first step of the final assembly.
-/
/-
Split of `lemma8` of this folder into the three steps of its proof in section 5 of the
article the statement comes from.

The statement counts the `n` of the window whose major arc integral is small. The proof
splits that set. Away from the fractional boundary of `F(n)` the major arc integral is the
sum of the two adjacent integer coefficients; those coefficients are large outside their own
sparse exceptional set; and the indices on the fractional boundary are few.

`lemma8_split` below states `Lemma8` unchanged and is assembled from the three leaves, so it
carries no `sorry` of its own. Each leaf carries exactly one step, and each is strictly
weaker than the split's main statement.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open Real MeasureTheory Polynomial
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-! ### Helpers added by this run: the kernel transform of the major-arc identity -/

open scoped FourierTransform

@[fun_prop]
private theorem continuous_eC : Continuous eC := by
  unfold eC
  fun_prop

private theorem tri_cos (a : ℝ) :
    ∫ β in (-1:ℝ)..1, (1 - |β|) * Real.cos (2 * π * a * β) = (Real.sinc (π * a)) ^ 2 := by
  rcases eq_or_ne a 0 with rfl | h0
  · have h1 : ∀ x : ℝ, Real.cos (2 * π * 0 * x) = 1 := by
      intro x; simp
    simp only [h1, mul_one, Real.sinc_zero, one_pow]
    have hsym : ∫ β in (-1:ℝ)..0, (1 - |β|) = ∫ β in (0:ℝ)..1, (1 - |β|) := by
      have h := intervalIntegral.integral_comp_neg (fun x : ℝ => (1 - |x|)) (a := (-1:ℝ)) (b := 0)
      simp only [neg_zero, neg_neg] at h
      simpa [abs_neg] using h
    have hpos : ∫ β in (0:ℝ)..1, (1 - |β|) = 1 / 2 := by
      have hcongr : ∀ β ∈ Set.uIcc (0:ℝ) 1, (1 - |β|) = 1 - β := by
        intro β hβ
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hβ
        show (1 - |β|) = 1 - β
        rw [abs_of_nonneg hβ.1]
      rw [intervalIntegral.integral_congr hcongr,
        intervalIntegral.integral_sub (μ := volume) (by continuity) (by continuity),
        intervalIntegral.integral_const]
      have hid : ∫ β in (0:ℝ)..1, β = 1 / 2 := by
        have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
          intro x _
          have h := (hasDerivAt_pow 2 x).div_const 2
          convert h using 1
          push_cast
          ring
        rw [show (∫ β in (0:ℝ)..1, β) =
            (fun y : ℝ => y ^ 2 / 2) 1 - (fun y : ℝ => y ^ 2 / 2) 0 from
          intervalIntegral.integral_eq_sub_of_hasDerivAt hd
            (by apply Continuous.intervalIntegrable (μ := volume); continuity)]
        norm_num
      rw [hid]
      norm_num
    rw [← intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := fun β : ℝ => 1 - |β|) (a := (-1:ℝ)) (b := (0:ℝ)) (c := (1:ℝ))
      (by apply Continuous.intervalIntegrable (μ := volume); continuity)
      (by apply Continuous.intervalIntegrable (μ := volume); continuity), hsym, hpos]
    norm_num
  · set c : ℝ := 2 * π * a with hcdef
    have hc0 : c ≠ 0 := by
      simp only [hcdef]
      exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) h0
    have hHeven : ∀ x : ℝ, (1 - |-x|) * Real.cos (c * -x) = (1 - |x|) * Real.cos (c * x) := by
      intro x; rw [abs_neg, mul_neg, Real.cos_neg]
    have hsplit : ∫ β in (-1:ℝ)..1, (1 - |β|) * Real.cos (c * β) =
        2 * ∫ β in (0:ℝ)..1, (1 - β) * Real.cos (c * β) := by
      have hadj : ∫ β in (-1:ℝ)..1, (1 - |β|) * Real.cos (c * β) =
          (∫ β in (-1:ℝ)..0, (1 - |β|) * Real.cos (c * β)) +
            (∫ β in (0:ℝ)..1, (1 - |β|) * Real.cos (c * β)) :=
        (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (f := fun β : ℝ => (1 - |β|) * Real.cos (c * β))
          (a := (-1:ℝ)) (b := (0:ℝ)) (c := (1:ℝ))
          (by apply Continuous.intervalIntegrable (μ := volume); continuity)
          (by apply Continuous.intervalIntegrable (μ := volume); continuity)).symm
      have hneg : ∫ β in (-1:ℝ)..0, (1 - |β|) * Real.cos (c * β) =
          ∫ β in (0:ℝ)..1, (1 - |β|) * Real.cos (c * β) := by
        have h := intervalIntegral.integral_comp_neg
          (fun x : ℝ => (1 - |x|) * Real.cos (c * x)) (a := (-1:ℝ)) (b := 0)
        simp only [neg_zero, neg_neg] at h
        rw [show (∫ x in (-1:ℝ)..0, (1 - |-x|) * Real.cos (c * -x)) =
          ∫ β in (-1:ℝ)..0, (1 - |β|) * Real.cos (c * β) from by
            apply intervalIntegral.integral_congr
            intro x _
            exact hHeven x] at h
        exact h
      have hpos : ∫ β in (0:ℝ)..1, (1 - |β|) * Real.cos (c * β) =
          ∫ β in (0:ℝ)..1, (1 - β) * Real.cos (c * β) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        show (1 - |x|) * Real.cos (c * x) = (1 - x) * Real.cos (c * x)
        rw [abs_of_nonneg hx.1]
      rw [hadj, hneg, hpos]; ring
    have hkey : ∫ β in (0:ℝ)..1, (1 - β) * Real.cos (c * β) = (1 - Real.cos c) / c ^ 2 := by
      have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1,
          HasDerivAt (fun y : ℝ => (1 - y) * Real.sin (c * y) / c - Real.cos (c * y) / c ^ 2)
            ((1 - x) * Real.cos (c * x)) x := by
        intro x _
        have h1 : HasDerivAt (fun y : ℝ => Real.sin (c * y)) (Real.cos (c * x) * c) x := by
          have hh := (Real.hasDerivAt_sin (c * x)).comp x ((hasDerivAt_id x).const_mul c)
          simpa [Function.comp_def, mul_comm] using hh
        have h2 : HasDerivAt (fun y : ℝ => Real.cos (c * y)) (-Real.sin (c * x) * c) x := by
          have hh := (Real.hasDerivAt_cos (c * x)).comp x ((hasDerivAt_id x).const_mul c)
          simpa [Function.comp_def, mul_comm] using hh
        have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
          have hb := (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
          convert hb using 1
          · funext y; simp
          · norm_num
        have h3 : HasDerivAt (fun y : ℝ => (1 - y) * Real.sin (c * y))
            (-1 * Real.sin (c * x) + (1 - x) * (Real.cos (c * x) * c)) x := by
          have hm := hsub.mul h1
          rw [show ((fun y : ℝ => 1 - y) * (fun y : ℝ => Real.sin (c * y)))
              = (fun y : ℝ => (1 - y) * Real.sin (c * y)) from rfl] at hm
          exact hm
        have h4 := (h3.div_const c).sub (h2.div_const (c ^ 2))
        convert h4 using 1
        field_simp
        ring
      rw [show (∫ β in (0:ℝ)..1, (1 - β) * Real.cos (c * β)) =
          (fun y : ℝ => (1 - y) * Real.sin (c * y) / c - Real.cos (c * y) / c ^ 2) 1 -
          (fun y : ℝ => (1 - y) * Real.sin (c * y) / c - Real.cos (c * y) / c ^ 2) 0 from
        intervalIntegral.integral_eq_sub_of_hasDerivAt hd
          (by apply Continuous.intervalIntegrable (μ := volume); continuity)]
      simp only [sub_self, zero_mul, Real.sin_zero, Real.cos_zero, zero_div, zero_sub,
        mul_zero, mul_one, one_pow]
      field_simp
      ring
    have hpi : π * a ≠ 0 := mul_ne_zero Real.pi_ne_zero h0
    rw [hsplit, hkey, Real.sinc_of_ne_zero hpi]
    have h2pi : c = 2 * π * a := hcdef
    rw [h2pi, div_pow]
    have key2 : 2 * ((1 - Real.cos (2 * π * a)) / (2 * π * a) ^ 2) =
        Real.sin (π * a) ^ 2 / (π * a) ^ 2 := by
      have hsq : 1 - Real.cos (2 * π * a) = 2 * Real.sin (π * a) ^ 2 := by
        have h3 : (2 * π * a : ℝ) = 2 * (π * a) := by ring
        rw [h3, Real.cos_two_mul]
        have h2 := Real.sin_sq_add_cos_sq (π * a)
        nlinarith [h2]
      field_simp
      linarith [hsq]
    exact key2

private theorem tri_sin (a : ℝ) :
    ∫ β in (-1:ℝ)..1, (1 - |β|) * Real.sin (2 * π * a * β) = 0 := by
  set c : ℝ := 2 * π * a with hcdef
  have hodd : ∀ x : ℝ, (1 - |-x|) * Real.sin (c * -x) = -((1 - |x|) * Real.sin (c * x)) := by
    intro x; rw [abs_neg, mul_neg, Real.sin_neg]; ring
  have hadj : ∫ β in (-1:ℝ)..1, (1 - |β|) * Real.sin (c * β) =
      (∫ β in (-1:ℝ)..0, (1 - |β|) * Real.sin (c * β)) +
        (∫ β in (0:ℝ)..1, (1 - |β|) * Real.sin (c * β)) :=
    (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := fun β : ℝ => (1 - |β|) * Real.sin (c * β))
      (a := (-1:ℝ)) (b := (0:ℝ)) (c := (1:ℝ))
      (by apply Continuous.intervalIntegrable (μ := volume); continuity)
      (by apply Continuous.intervalIntegrable (μ := volume); continuity)).symm
  have hneg : ∫ β in (-1:ℝ)..0, (1 - |β|) * Real.sin (c * β) =
      -∫ β in (0:ℝ)..1, (1 - |β|) * Real.sin (c * β) := by
    have h := intervalIntegral.integral_comp_neg
      (fun x : ℝ => (1 - |x|) * Real.sin (c * x)) (a := (-1:ℝ)) (b := 0)
    simp only [neg_zero, neg_neg] at h
    rw [show (∫ x in (-1:ℝ)..0, (1 - |-x|) * Real.sin (c * -x)) =
        ∫ x in (-1:ℝ)..0, -((1 - |x|) * Real.sin (c * x)) from by
          apply intervalIntegral.integral_congr
          intro x _
          exact hodd x] at h
    rw [intervalIntegral.integral_neg] at h
    linarith [h]
  have hpos : ∫ β in (0:ℝ)..1, (1 - |β|) * Real.sin (c * β) =
      ∫ β in (0:ℝ)..1, (1 - β) * Real.sin (c * β) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    show (1 - |x|) * Real.sin (c * x) = (1 - x) * Real.sin (c * x)
    rw [abs_of_nonneg hx.1]
  rw [hadj, hpos, hneg, hpos]
  ring

private theorem tri_fourier (a : ℝ) :
    ∫ β in (-1:ℝ)..1, ((1 - |β| : ℝ) : ℂ) * eC (-(a * β)) = ((Real.sinc (π * a)) ^ 2 : ℂ) := by
  have hexp : ∀ β : ℝ, eC (-(a * β)) =
      (Real.cos (2 * π * a * β) : ℂ) - (Real.sin (2 * π * a * β) : ℂ) * Complex.I := by
    intro β
    have h1 : (2 * (π : ℂ) * Complex.I * ((↑(-(a * β)) : ℝ) : ℂ)) =
        ((-(2 * π * a * β) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [eC, h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have e1 : ∫ β in (-1:ℝ)..1, (((1 - |β|) * Real.cos (2 * π * a * β) : ℝ) : ℂ) =
      ((Real.sinc (π * a)) ^ 2 : ℂ) := by
    rw [intervalIntegral.integral_ofReal, tri_cos]
    push_cast
    ring
  have e2 : ∫ β in (-1:ℝ)..1, (((1 - |β|) * Real.sin (2 * π * a * β) : ℝ) : ℂ) = 0 := by
    rw [intervalIntegral.integral_ofReal, tri_sin]
    norm_num
  rw [show (∫ β in (-1:ℝ)..1, ((1 - |β| : ℝ) : ℂ) * eC (-(a * β))) =
      ∫ β in (-1:ℝ)..1, (((1 - |β|) * Real.cos (2 * π * a * β) : ℝ) : ℂ) -
        (((1 - |β|) * Real.sin (2 * π * a * β) : ℝ) : ℂ) * Complex.I from by
    apply intervalIntegral.integral_congr
    intro x _
    show ((1 - |x| : ℝ) : ℂ) * eC (-(a * x)) =
      (((1 - |x|) * Real.cos (2 * π * a * x) : ℝ) : ℂ) -
        (((1 - |x|) * Real.sin (2 * π * a * x) : ℝ) : ℂ) * Complex.I
    rw [hexp x]
    push_cast
    ring]
  rw [intervalIntegral.integral_sub (μ := volume)
      (by apply Continuous.intervalIntegrable (μ := volume); continuity)
      (by apply Continuous.intervalIntegrable (μ := volume); continuity),
    intervalIntegral.integral_mul_const, e1, e2]
  ring

private theorem kfun_eq (Δ α : ℝ) (hα : α ≠ 0) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    Kfun Δ α = (Real.sin (π * α) ^ 2 - Real.sin (π * (1 - Δ) * α) ^ 2) / (Δ * π ^ 2 * α ^ 2) := by
  have h1 : π * α ≠ 0 := mul_ne_zero Real.pi_ne_zero hα
  have h2 : π * (1 - Δ) * α ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero Real.pi_ne_zero (by linarith)) hα
  unfold Kfun
  rw [Real.sinc_of_ne_zero h1, Real.sinc_of_ne_zero h2]
  field_simp

private theorem kfun_abs_le (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (α : ℝ) :
    |Kfun Δ α| ≤ 2 / Δ := by
  have h1 : |Real.sinc (π * α)| ≤ 1 := Real.abs_sinc_le_one _
  have h2 : |Real.sinc (π * (1 - Δ) * α)| ≤ 1 := Real.abs_sinc_le_one _
  have h1' : |Real.sinc (π * α)| ^ 2 ≤ 1 := by nlinarith [h1, abs_nonneg (Real.sinc (π * α))]
  have h2' : |Real.sinc (π * (1 - Δ) * α)| ^ 2 ≤ 1 := by
    nlinarith [h2, abs_nonneg (Real.sinc (π * (1 - Δ) * α))]
  have hd : (0:ℝ) < 1 / Δ := by positivity
  have hd2 : (0:ℝ) ≤ (1 / Δ) * (1 - Δ) ^ 2 := by positivity
  unfold Kfun
  have h3 : |(1 / Δ) * Real.sinc (π * α) ^ 2| = (1 / Δ) * |Real.sinc (π * α)| ^ 2 := by
    rw [abs_mul, abs_pow, abs_of_pos hd]
  have h4 : |(1 / Δ) * (1 - Δ) ^ 2 * Real.sinc (π * (1 - Δ) * α) ^ 2| =
      ((1 / Δ) * (1 - Δ) ^ 2) * |Real.sinc (π * (1 - Δ) * α)| ^ 2 := by
    rw [abs_mul, abs_pow, abs_of_nonneg hd2]
  have h5 : |(1 / Δ) * Real.sinc (π * α) ^ 2 -
      (1 / Δ) * (1 - Δ) ^ 2 * Real.sinc (π * (1 - Δ) * α) ^ 2| ≤
      (1 / Δ) * |Real.sinc (π * α)| ^ 2 + ((1 / Δ) * (1 - Δ) ^ 2) * |Real.sinc (π * (1 - Δ) * α)| ^ 2 := by
    calc |(1 / Δ) * Real.sinc (π * α) ^ 2 - (1 / Δ) * (1 - Δ) ^ 2 * Real.sinc (π * (1 - Δ) * α) ^ 2|
        ≤ |(1 / Δ) * Real.sinc (π * α) ^ 2| +
          |(1 / Δ) * (1 - Δ) ^ 2 * Real.sinc (π * (1 - Δ) * α) ^ 2| := abs_sub _ _
      _ = _ := by rw [h3, h4]
  have h6 : (1 / Δ) * |Real.sinc (π * α)| ^ 2 +
      ((1 / Δ) * (1 - Δ) ^ 2) * |Real.sinc (π * (1 - Δ) * α)| ^ 2 ≤ 2 / Δ := by
    have h7 : (1 / Δ) * |Real.sinc (π * α)| ^ 2 ≤ (1 / Δ) := by
      simpa using mul_le_mul_of_nonneg_left h1' hd.le
    have h8 : ((1 / Δ) * (1 - Δ) ^ 2) * |Real.sinc (π * (1 - Δ) * α)| ^ 2 ≤
        (1 / Δ) * (1 - Δ) ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left h2' hd2
    have h9 : (1 - Δ) ^ 2 ≤ 1 := by nlinarith
    have h10 : (1 / Δ) * (1 - Δ) ^ 2 ≤ (1 / Δ) := by
      simpa using mul_le_mul_of_nonneg_left h9 hd.le
    have h11 : (1 / Δ) + (1 / Δ) = 2 / Δ := by ring
    linarith [h7, h8, h10, h11]
  linarith [h5, h6]

private theorem kfun_decay (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) {α : ℝ} (hα : α ≠ 0) :
    |Kfun Δ α| ≤ 2 / (Δ * π ^ 2 * α ^ 2) := by
  have hsin1 : |Real.sin (π * α)| ≤ 1 := Real.abs_sin_le_one _
  have hsin2 : |Real.sin (π * (1 - Δ) * α)| ≤ 1 := Real.abs_sin_le_one _
  have hnum : |Real.sin (π * α) ^ 2 - Real.sin (π * (1 - Δ) * α) ^ 2| ≤ 2 := by
    have h1 : |Real.sin (π * α) ^ 2| ≤ 1 := by
      rw [abs_pow]; nlinarith [hsin1, abs_nonneg (Real.sin (π * α))]
    have h2 : |Real.sin (π * (1 - Δ) * α) ^ 2| ≤ 1 := by
      rw [abs_pow]; nlinarith [hsin2, abs_nonneg (Real.sin (π * (1 - Δ) * α))]
    calc |Real.sin (π * α) ^ 2 - Real.sin (π * (1 - Δ) * α) ^ 2|
        ≤ |Real.sin (π * α) ^ 2| + |Real.sin (π * (1 - Δ) * α) ^ 2| := abs_sub _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  rw [kfun_eq Δ α hα hΔ0 hΔ1, abs_div]
  have hden0 : (0:ℝ) < Δ * π ^ 2 * α ^ 2 := by positivity
  rw [abs_of_pos hden0, div_le_div_iff_of_pos_right hden0]
  linarith [hnum]

private theorem kfun_bound (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (α : ℝ) :
    |Kfun Δ α| ≤ (4 / Δ) / (1 + α ^ 2) := by
  have hpos : (0:ℝ) < 1 + α ^ 2 := by positivity
  have hsqabs : |α| ^ 2 = α ^ 2 := sq_abs α
  rcases le_or_gt |α| 1 with hle | hgt
  · have hA : |Kfun Δ α| ≤ 2 / Δ := kfun_abs_le Δ hΔ0 hΔ1 α
    have hsq : α ^ 2 ≤ 1 := by nlinarith [hle, abs_nonneg α, hsqabs]
    have hkey : 2 / Δ ≤ (4 / Δ) / (1 + α ^ 2) := by
      rw [show (4 / Δ) / (1 + α ^ 2) = 4 / (Δ * (1 + α ^ 2)) by field_simp]
      rw [div_le_div_iff₀ hΔ0 (by positivity)]
      nlinarith [hsq, hΔ0]
    linarith [hA, hkey]
  · have hα : α ≠ 0 := by
      intro h; rw [h, abs_zero] at hgt; norm_num at hgt
    have hB : |Kfun Δ α| ≤ 2 / (Δ * π ^ 2 * α ^ 2) := kfun_decay Δ hΔ0 hΔ1 hα
    have hsq : 1 < α ^ 2 := by nlinarith [hgt, abs_nonneg α, hsqabs]
    have hpi : (9:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have hcmp : 2 / (Δ * π ^ 2 * α ^ 2) ≤ (4 / Δ) / (1 + α ^ 2) := by
      have h1 : 1 + α ^ 2 ≤ 2 * α ^ 2 := by linarith
      have h2 : 2 * α ^ 2 ≤ 2 * π ^ 2 * α ^ 2 := by nlinarith [hpi, hsq]
      have h3 : 1 + α ^ 2 ≤ 2 * π ^ 2 * α ^ 2 := le_trans h1 h2
      rw [show (4 / Δ) / (1 + α ^ 2) = 4 / (Δ * (1 + α ^ 2)) by field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : 2 * (Δ * (1 + α ^ 2)) ≤ 2 * (Δ * (2 * π ^ 2 * α ^ 2)) := by
        have h5 : Δ * (1 + α ^ 2) ≤ Δ * (2 * π ^ 2 * α ^ 2) := by
          gcongr
        linarith [h5]
      nlinarith [h4]
    linarith [hB, hcmp]

private theorem kfun_integrable (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    Integrable (fun α : ℝ => ((Kfun Δ α : ℝ) : ℂ)) := by
  have hcont : Continuous fun α : ℝ => ((Kfun Δ α : ℝ) : ℂ) := by
    unfold Kfun
    fun_prop
  refine Integrable.mono' (g := fun x : ℝ => (4 / Δ) * (1 + x ^ 2)⁻¹) ?_
    hcont.aestronglyMeasurable ?_
  · have hbase : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
    have := hbase.const_mul (4 / Δ)
    simpa [div_eq_mul_inv, mul_comm] using this
  · filter_upwards with α
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact kfun_bound Δ hΔ0 hΔ1 α

private theorem tri_scaled (Δ a : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∫ β in (-(1 - Δ):ℝ)..(1 - Δ), ((1 - |β| / (1 - Δ) : ℝ) : ℂ) * eC (-(a * β)) =
      ((1 - Δ) * (Real.sinc (π * (1 - Δ) * a)) ^ 2 : ℝ) := by
  have hc : (1 - Δ) ≠ 0 := by linarith
  have hcpos : (0:ℝ) < 1 - Δ := by linarith
  set g : ℝ → ℂ := fun x => ((1 - |x| / (1 - Δ) : ℝ) : ℂ) * eC (-(a * x)) with hg
  have hcomp : ∀ x : ℝ, g ((1 - Δ) * x) = ((1 - |x| : ℝ) : ℂ) * eC (-(a * (1 - Δ) * x)) := by
    intro x
    simp only [hg]
    have habs : |(1 - Δ) * x| = (1 - Δ) * |x| := by
      rw [abs_mul, abs_of_pos hcpos]
    rw [habs]
    have hdiv : (1 - Δ) * |x| / (1 - Δ) = |x| := by field_simp
    rw [hdiv]
    ring_nf
  have h := intervalIntegral.integral_comp_mul_left (f := g) (a := (-1:ℝ)) (b := 1) (c := 1 - Δ) hc
  rw [show (1 - Δ) * (-1) = -(1 - Δ) by ring, mul_one] at h
  have hleft : ∫ x in (-1:ℝ)..1, g ((1 - Δ) * x) =
      ∫ x in (-1:ℝ)..1, ((1 - |x| : ℝ) : ℂ) * eC (-(a * (1 - Δ) * x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hcomp x
  have ht : ∫ x in (-1:ℝ)..1, ((1 - |x| : ℝ) : ℂ) * eC (-(a * (1 - Δ) * x)) =
      ((Real.sinc (π * (a * (1 - Δ))) : ℝ) : ℂ) ^ 2 := by
    have := tri_fourier (a * (1 - Δ))
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  have hmul : ∫ x in (-(1 - Δ):ℝ)..(1 - Δ), g x =
      (1 - Δ) • ∫ x in (-1:ℝ)..1, g ((1 - Δ) * x) := by
    rw [h, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [hmul, hleft, ht]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [show (π * (a * (1 - Δ))) = π * (1 - Δ) * a by ring]
  simp

private theorem fourier_form (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = ∫ v, eC (-(v * w)) * f v := by
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with v
  rw [Circle.smul_def, Real.fourierChar_apply, eC, RCLike.inner_apply]
  congr 2
  push_cast
  simp
  ring

private theorem trap_ft (Δ a : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    𝓕 (fun β : ℝ => (((1 / Δ) * max (1 - |β|) 0 -
        ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0 : ℝ) : ℂ)) a = ((Kfun Δ a : ℝ) : ℂ) := by
  set T : ℝ → ℝ := fun β => (1 / Δ) * max (1 - |β|) 0 - ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0
    with hT
  set k : ℝ → ℂ := fun v => eC (-(v * a)) * (T v : ℂ) with hk
  have hΔpos : (0:ℝ) < 1 - Δ := by linarith
  have hz : ∀ β : ℝ, β ∉ Set.Ioo (-1:ℝ) 1 → k β = 0 := by
    intro β hβ
    have hle : 1 ≤ |β| := by
      rw [Set.mem_Ioo, not_and_or] at hβ
      rcases hβ with h | h
      · have h' : β ≤ -1 := by linarith
        rw [abs_of_nonpos (by linarith)]; linarith
      · have h' : 1 ≤ β := by linarith
        rw [abs_of_nonneg (by linarith)]; exact h'
    have h1 : max (1 - |β|) 0 = 0 := by rw [max_eq_right]; linarith
    have h2 : max (1 - |β| / (1 - Δ)) 0 = 0 := by
      have hge : 1 ≤ |β| / (1 - Δ) := by
        rw [le_div_iff₀ hΔpos]
        linarith [hle]
      rw [max_eq_right]; linarith
    simp only [hk, hT, h1, h2]
    simp
  -- the whole line integral is the interval integral
  have e_whole : ∫ v, k v = ∫ v in (-1:ℝ)..1, k v := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (fun x hx => hz x (fun h => hx (Set.Ioo_subset_Ioc_self h)))).symm
  -- pointwise shape on the interval
  have hshape : ∫ v in (-1:ℝ)..1, k v =
      ∫ v in (-1:ℝ)..1, ((1 / Δ : ℂ) * (((1 - |v| : ℝ) : ℂ) * eC (-(v * a))) -
        ((1 - Δ) / Δ : ℂ) * (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a)))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hx
    have habs : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
    have hmax : max (1 - |x|) 0 = 1 - |x| := by rw [max_eq_left]; linarith
    simp only [hk, hT, hmax]
    push_cast
    ring
  -- first piece
  have hf1 : ∫ v in (-1:ℝ)..1, (((1 - |v| : ℝ) : ℂ) * eC (-(v * a))) =
      ((Real.sinc (π * a)) ^ 2 : ℂ) := by
    rw [show (∫ v in (-1:ℝ)..1, (((1 - |v| : ℝ) : ℂ) * eC (-(v * a)))) =
      ∫ v in (-1:ℝ)..1, (((1 - |v| : ℝ) : ℂ) * eC (-(a * v))) from by
        apply intervalIntegral.integral_congr
        intro x _
        show (((1 - |x| : ℝ) : ℂ) * eC (-(x * a))) = (((1 - |x| : ℝ) : ℂ) * eC (-(a * x)))
        rw [mul_comm x a]]
    exact tri_fourier a
  -- second piece
  have hf2 : ∫ v in (-1:ℝ)..1, (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a))) =
      (((1 - Δ) * (Real.sinc (π * (1 - Δ) * a)) ^ 2 : ℝ) : ℂ) := by
    have hg0 : ∀ x : ℝ, x ∈ Set.uIcc (-1:ℝ) (-(1 - Δ)) →
        (((max (1 - |x| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(x * a))) = 0 := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : (-1:ℝ) ≤ -(1 - Δ))] at hx
      have hx' : 1 - Δ ≤ |x| := by
        rw [abs_of_nonpos (by linarith [hx.2])]
        linarith [hx.2]
      have hge : 1 ≤ |x| / (1 - Δ) := by
        rw [le_div_iff₀ hΔpos]
        linarith [hx']
      have hmax : max (1 - |x| / (1 - Δ)) 0 = 0 := by rw [max_eq_right]; linarith
      simp [hmax]
    have hg1 : ∀ x : ℝ, x ∈ Set.uIcc (1 - Δ) 1 →
        (((max (1 - |x| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(x * a))) = 0 := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : (1 - Δ) ≤ 1)] at hx
      have hx' : 1 - Δ ≤ |x| := by
        rw [abs_of_nonneg (by linarith [hx.1])]
        linarith [hx.1]
      have hge : 1 ≤ |x| / (1 - Δ) := by
        rw [le_div_iff₀ hΔpos]
        linarith [hx']
      have hmax : max (1 - |x| / (1 - Δ)) 0 = 0 := by rw [max_eq_right]; linarith
      simp [hmax]
    have hsp1 : ∫ v in (-1:ℝ)..1, (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a))) =
        (∫ v in (-1:ℝ)..-(1 - Δ), (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a)))) +
        (∫ v in (-(1 - Δ):ℝ)..1, (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a)))) :=
      (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (f := fun v : ℝ => (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a))))
        (a := (-1:ℝ)) (b := (-(1 - Δ))) (c := (1:ℝ))
        (by apply Continuous.intervalIntegrable (μ := volume); fun_prop)
        (by apply Continuous.intervalIntegrable (μ := volume); fun_prop)).symm
    have hsp2 : ∫ v in (-(1 - Δ):ℝ)..1, (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a))) =
        (∫ v in (-(1 - Δ):ℝ)..(1 - Δ), (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a)))) +
        (∫ v in (1 - Δ:ℝ)..1, (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a)))) :=
      (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (f := fun v : ℝ => (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a))))
        (a := (-(1 - Δ))) (b := (1 - Δ)) (c := (1:ℝ))
        (by apply Continuous.intervalIntegrable (μ := volume); fun_prop)
        (by apply Continuous.intervalIntegrable (μ := volume); fun_prop)).symm
    have hz1 : ∫ v in (-1:ℝ)..-(1 - Δ), (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a))) = 0 := by
      rw [intervalIntegral.integral_congr hg0]
      simp
    have hz2 : ∫ v in (1 - Δ:ℝ)..1, (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a))) = 0 := by
      rw [intervalIntegral.integral_congr hg1]
      simp
    have hinner : ∫ v in (-(1 - Δ):ℝ)..(1 - Δ), (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a))) =
        (((1 - Δ) * (Real.sinc (π * (1 - Δ) * a)) ^ 2 : ℝ) : ℂ) := by
      rw [show (∫ v in (-(1 - Δ):ℝ)..(1 - Δ), (((max (1 - |v| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(v * a)))) =
        ∫ v in (-(1 - Δ):ℝ)..(1 - Δ), (((1 - |v| / (1 - Δ) : ℝ) : ℂ) * eC (-(a * v))) from by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le (by linarith : (-(1 - Δ):ℝ) ≤ (1 - Δ))] at hx
          have habs : |x| ≤ 1 - Δ := abs_le.mpr ⟨hx.1, hx.2⟩
          have hmax : max (1 - |x| / (1 - Δ)) 0 = 1 - |x| / (1 - Δ) := by
            rw [max_eq_left]
            have hle1 : |x| / (1 - Δ) ≤ 1 := by
              rw [div_le_one hΔpos]
              exact habs
            linarith
          show (((max (1 - |x| / (1 - Δ)) 0 : ℝ) : ℂ) * eC (-(x * a))) =
            (((1 - |x| / (1 - Δ) : ℝ) : ℂ) * eC (-(a * x)))
          rw [hmax, mul_comm x a]]
      exact tri_scaled Δ a hΔ0 hΔ1
    rw [hsp1, hsp2, hz1, hz2, hinner]
    ring
  rw [fourier_form]
  change ∫ v, k v = ((Kfun Δ a : ℝ) : ℂ)
  rw [e_whole, hshape, intervalIntegral.integral_sub (μ := volume)
      (by apply Continuous.intervalIntegrable (μ := volume); fun_prop)
      (by apply Continuous.intervalIntegrable (μ := volume); fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hf1, hf2]
  unfold Kfun
  push_cast
  field_simp

private theorem trap_continuous (Δ : ℝ) :
    Continuous (fun β : ℝ => (((1 / Δ) * max (1 - |β|) 0 -
      ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0 : ℝ) : ℂ)) := by
  fun_prop

private theorem trap_integrable (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    Integrable (fun β : ℝ => (((1 / Δ) * max (1 - |β|) 0 -
      ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0 : ℝ) : ℂ)) := by
  have hΔpos : (0:ℝ) < 1 - Δ := by linarith
  have hgd : (0:ℝ) < 4 / Δ := by positivity
  refine Integrable.mono' (g := fun β : ℝ => (4 / Δ) * (1 + β ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul (4 / Δ))
    (trap_continuous Δ).aestronglyMeasurable ?_
  filter_upwards with β
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hmax1 : max (1 - |β|) 0 ≤ 1 := by
    have h2 : 1 - |β| ≤ 1 := by linarith [abs_nonneg β]
    exact max_le h2 (by norm_num)
  have hmax2 : max (1 - |β| / (1 - Δ)) 0 ≤ 1 := by
    have h1 : (0:ℝ) ≤ |β| / (1 - Δ) := div_nonneg (abs_nonneg β) (le_of_lt hΔpos)
    have h2 : 1 - |β| / (1 - Δ) ≤ 1 := by linarith
    exact max_le h2 (by norm_num)
  have hbound : |(1 / Δ) * max (1 - |β|) 0 - ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0| ≤ 2 / Δ := by
    have h1 : |(1 / Δ) * max (1 - |β|) 0| ≤ 1 / Δ := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / Δ), abs_of_nonneg (le_max_right _ _)]
      calc (1 / Δ) * max (1 - |β|) 0 ≤ (1 / Δ) * 1 := by
            apply mul_le_mul_of_nonneg_left hmax1 (le_of_lt (by positivity : (0:ℝ) < 1 / Δ))
        _ = 1 / Δ := by ring
    have h2 : |((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0| ≤ (1 - Δ) / Δ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 - Δ) / Δ),
        abs_of_nonneg (le_max_right _ _)]
      calc ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0 ≤ ((1 - Δ) / Δ) * 1 := by
            apply mul_le_mul_of_nonneg_left hmax2 (by positivity)
        _ = (1 - Δ) / Δ := by ring
    calc |(1 / Δ) * max (1 - |β|) 0 - ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0|
        ≤ |(1 / Δ) * max (1 - |β|) 0| + |((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0| := abs_sub _ _
      _ ≤ 1 / Δ + (1 - Δ) / Δ := by linarith
      _ = (2 - Δ) / Δ := by ring
      _ ≤ 2 / Δ := by
        rw [div_le_div_iff₀ hΔ0 hΔ0]
        nlinarith [hΔ0]
  rcases le_or_gt |β| 1 with hb | hb
  · have hge : (1:ℝ) / 2 ≤ (1 + β ^ 2)⁻¹ := by
      rw [show (1:ℝ) / 2 = (2:ℝ)⁻¹ by norm_num, inv_le_inv₀ (by norm_num) (by positivity)]
      nlinarith [sq_abs β, hb, abs_nonneg β]
    have hkey : 2 / Δ ≤ (4 / Δ) * (1 + β ^ 2)⁻¹ := by
      have : (2:ℝ) / Δ = (4 / Δ) * (1 / 2) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hge (by positivity)
    linarith [hbound, hkey]
  · have h1 : max (1 - |β|) 0 = 0 := by
      rw [max_eq_right]; linarith
    have h2 : max (1 - |β| / (1 - Δ)) 0 = 0 := by
      have hge : 1 ≤ |β| / (1 - Δ) := by
        rw [le_div_iff₀ hΔpos]
        linarith [hb.le]
      rw [max_eq_right]
      linarith
    rw [h1, h2]
    norm_num
    positivity

private theorem kfun_fourier (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    𝓕 (fun a : ℝ => ((Kfun Δ a : ℝ) : ℂ)) =
      fun β : ℝ => (((1 / Δ) * max (1 - |β|) 0 -
        ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0 : ℝ) : ℂ) := by
  have hcontT := trap_continuous Δ
  have hT := trap_integrable Δ hΔ0 hΔ1
  have hFT : Integrable (𝓕 (fun β : ℝ => (((1 / Δ) * max (1 - |β|) 0 -
      ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0 : ℝ) : ℂ))) := by
    refine (kfun_integrable Δ hΔ0 hΔ1).congr ?_
    filter_upwards with a
    exact (trap_ft Δ a hΔ0 hΔ1).symm
  have hinv := hcontT.fourierInv_fourier_eq hT hFT
  funext β
  have hfun : (fun a : ℝ => ((Kfun Δ a : ℝ) : ℂ)) =
      𝓕 (fun b : ℝ => (((1 / Δ) * max (1 - |b|) 0 -
        ((1 - Δ) / Δ) * max (1 - |b| / (1 - Δ)) 0 : ℝ) : ℂ)) := by
    funext a
    exact (trap_ft Δ a hΔ0 hΔ1).symm
  rw [hfun]
  have hneg : 𝓕 (𝓕 (fun b : ℝ => (((1 / Δ) * max (1 - |b|) 0 -
      ((1 - Δ) / Δ) * max (1 - |b| / (1 - Δ)) 0 : ℝ) : ℂ))) β =
      𝓕⁻ (𝓕 (fun b : ℝ => (((1 / Δ) * max (1 - |b|) 0 -
      ((1 - Δ) / Δ) * max (1 - |b| / (1 - Δ)) 0 : ℝ) : ℂ))) (-β) := by
    rw [Real.fourier_eq, fourierInv_eq]
    congr 1 with v
    rw [RCLike.inner_apply, RCLike.inner_apply]
    congr 2
    push_cast
    ring
  rw [hneg, congrFun hinv (-β)]
  simp [abs_neg]

private theorem eC_add' (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem trap_eq_one (Δ β : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hβ : |β| ≤ 1 - Δ) :
    (1 / Δ) * max (1 - |β|) 0 - ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0 = 1 := by
  have h1 : max (1 - |β|) 0 = 1 - |β| := by
    rw [max_eq_left]; linarith [abs_nonneg β]
  have h2 : max (1 - |β| / (1 - Δ)) 0 = 1 - |β| / (1 - Δ) := by
    rw [max_eq_left]
    have hle : |β| / (1 - Δ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hβ
    linarith
  rw [h1, h2]
  field_simp
  ring

private theorem trap_eq_zero (Δ β : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hβ : 1 ≤ |β|) :
    (1 / Δ) * max (1 - |β|) 0 - ((1 - Δ) / Δ) * max (1 - |β| / (1 - Δ)) 0 = 0 := by
  have h1 : max (1 - |β|) 0 = 0 := by
    rw [max_eq_right]; linarith
  have h2 : max (1 - |β| / (1 - Δ)) 0 = 0 := by
    have hge : 1 ≤ |β| / (1 - Δ) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    rw [max_eq_right]; linarith
  rw [h1, h2, mul_zero, mul_zero, sub_zero]

private theorem map_G (Δ v m : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    𝓕 (fun u : ℝ => ((Kfun Δ u : ℝ) : ℂ) * eC (-(u * v))) m =
      (((1 / Δ) * max (1 - |v + m|) 0 - ((1 - Δ) / Δ) * max (1 - |v + m| / (1 - Δ)) 0 : ℝ) : ℂ) := by
  rw [fourier_form]
  have hcongr : ∀ u : ℝ, eC (-(u * m)) * (((Kfun Δ u : ℝ) : ℂ) * eC (-(u * v))) =
      eC (-(u * (v + m))) * ((Kfun Δ u : ℝ) : ℂ) := by
    intro u
    rw [show (-(u * (v + m))) = -(u * m) + -(u * v) by ring, eC_add']
    ring
  rw [show (∫ u, eC (-(u * m)) * (((Kfun Δ u : ℝ) : ℂ) * eC (-(u * v)))) =
      ∫ u, eC (-(u * (v + m))) * ((Kfun Δ u : ℝ) : ℂ) from by
    apply integral_congr_ae
    filter_upwards with u
    exact hcongr u]
  rw [← fourier_form]
  exact congrFun (kfun_fourier Δ hΔ0 hΔ1) (v + m)

private theorem G_bigO (Δ v : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    (fun u : ℝ => ((Kfun Δ u : ℝ) : ℂ) * eC (-(u * v))) =O[Filter.cocompact ℝ]
      (fun u : ℝ => |u| ^ (-(2:ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (8 / Δ) ?_
  have hlarge : ∀ᶠ u : ℝ in Filter.cocompact ℝ, (1:ℝ) ≤ |u| := by
    have h1 : ∀ᶠ u : ℝ in Filter.atTop, (1:ℝ) ≤ |u| := by
      filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with u hu
      rw [abs_of_nonneg (by linarith)]
      exact hu
    have h2 : ∀ᶠ u : ℝ in Filter.atBot, (1:ℝ) ≤ |u| := by
      filter_upwards [Filter.eventually_le_atBot (-1:ℝ)] with u hu
      rw [abs_of_nonpos (by linarith)]
      linarith
    rw [cocompact_eq_atBot_atTop]
    exact Filter.eventually_sup.mpr ⟨h2, h1⟩
  filter_upwards [hlarge] with u hu
  have hK : ‖((Kfun Δ u : ℝ) : ℂ)‖ ≤ (4 / Δ) / (1 + u ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact kfun_bound Δ hΔ0 hΔ1 u
  have he : ‖eC (-(u * v))‖ = 1 := norm_eC _
  have hsq : (1:ℝ) ≤ u ^ 2 := by
    calc (1:ℝ) = 1 ^ 2 := by norm_num
      _ ≤ |u| ^ 2 := by nlinarith [hu, abs_nonneg u]
      _ = u ^ 2 := sq_abs u
  have hrw : |u| ^ (-(2:ℝ)) = (u ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg u), show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num,
      Real.rpow_natCast, sq_abs]
  rw [norm_mul, he, mul_one]
  conv_rhs => rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _), hrw]
  have h1 : (1 + u ^ 2)⁻¹ ≤ 2 * (u ^ 2)⁻¹ := by
    have hu2 : (0:ℝ) < u ^ 2 := by linarith
    have h2 : (1 + u ^ 2)⁻¹ ≤ (u ^ 2)⁻¹ := inv_anti₀ hu2 (by linarith)
    have h3 : (u ^ 2)⁻¹ ≤ 2 * (u ^ 2)⁻¹ := by
      have hp : (0:ℝ) < (u ^ 2)⁻¹ := by positivity
      linarith
    linarith
  calc ‖((Kfun Δ u : ℝ) : ℂ)‖ ≤ (4 / Δ) / (1 + u ^ 2) := hK
    _ = (4 / Δ) * (1 + u ^ 2)⁻¹ := by ring
    _ ≤ (4 / Δ) * (2 * (u ^ 2)⁻¹) := by
        apply mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (8 / Δ) * (u ^ 2)⁻¹ := by ring

private theorem kfun_continuous (Δ : ℝ) : Continuous fun u : ℝ => ((Kfun Δ u : ℝ) : ℂ) := by
  unfold Kfun
  fun_prop

private theorem periodization (Δ v : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (ν : ℤ)
    (hlo : (Δ:ℝ) ≤ v - (ν:ℝ)) (hhi : v - (ν:ℝ) ≤ 1 - Δ) (t : ℝ) :
    ∑' (n : ℤ), (((Kfun Δ ((t : ℝ) + n) : ℝ) : ℂ) * eC (-(((t : ℝ) + n) * v))) =
      eC (-((ν:ℝ) * t)) + eC (-(((ν:ℝ) + 1) * t)) := by
  set G : ℝ → ℂ := fun u => ((Kfun Δ u : ℝ) : ℂ) * eC (-(u * v)) with hG
  have hGc : Continuous G := by
    rw [hG]
    exact (kfun_continuous Δ).mul (continuous_eC.comp (by fun_prop))
  have hGbig : G =O[Filter.cocompact ℝ] (fun u : ℝ => |u| ^ (-(2:ℝ))) := by
    rw [hG]
    exact G_bigO Δ v hΔ0 hΔ1
  have hzero : ∀ n : ℤ, n ≠ -ν → n ≠ -ν - 1 → 𝓕 G (n : ℝ) = 0 := by
    intro n hn1 hn2
    rw [hG, map_G Δ v (n : ℝ) hΔ0 hΔ1]
    have hbig : 1 ≤ |v + (n:ℝ)| := by
      rcases le_or_gt n (-ν - 2) with h | h
      · have hnle : (n:ℝ) ≤ -(ν:ℝ) - 2 := by
          have : (n : ℝ) ≤ ((-ν - 2 : ℤ) : ℝ) := by exact_mod_cast h
          push_cast at this ⊢
          linarith
        have : v + (n:ℝ) ≤ -1 := by
          have h2 : v - (ν:ℝ) ≤ 1 - Δ := hhi
          linarith
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hge : -ν ≤ n := by omega
        have hge2 : -ν + 1 ≤ n := by omega
        have hnge : -(ν:ℝ) + 1 ≤ (n:ℝ) := by
          have : ((-ν + 1 : ℤ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hge2
          push_cast at this ⊢
          linarith
        have : 1 ≤ v + (n:ℝ) := by linarith
        rw [abs_of_nonneg (by linarith)]
        exact this
    rw [trap_eq_zero Δ (v + (n:ℝ)) hΔ0 hΔ1 hbig]
    simp
  have hsum : Summable (fun n : ℤ => 𝓕 G (n : ℝ)) :=
    summable_of_ne_finset_zero (s := {-ν, -ν - 1}) (fun b hb => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      exact hzero b hb.1 hb.2)
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hGc (by norm_num : (1:ℝ) < 2)
    hGbig hsum t
  rw [show (∑' (n : ℤ), (((Kfun Δ ((t : ℝ) + n) : ℝ) : ℂ) * eC (-(((t : ℝ) + n) * v))) ) =
      ∑' (n : ℤ), G ((t : ℝ) + n) from rfl]
  rw [hpois]
  -- evaluate the two surviving terms
  have hterm : ∀ n : ℤ, 𝓕 G (n:ℝ) * fourier n (t : UnitAddCircle) =
      if n = -ν then eC (-((ν:ℝ) * t)) else if n = -ν - 1 then eC (-(((ν:ℝ) + 1) * t)) else 0 := by
    intro n
    by_cases hn1 : n = -ν
    · subst hn1
      have hkey : 𝓕 G ((-ν : ℤ) : ℝ) = 1 := by
        rw [hG, map_G Δ v ((-ν : ℤ) : ℝ) hΔ0 hΔ1]
        have : ((-ν : ℤ) : ℝ) = -(ν:ℝ) := by push_cast; ring
        rw [this]
        have habs : |v + -(ν:ℝ)| ≤ 1 - Δ := by
          rw [abs_le]
          constructor <;> linarith
        rw [trap_eq_one Δ (v + -(ν:ℝ)) hΔ0 hΔ1 habs]
        norm_num
      rw [hkey, one_mul, if_pos rfl, fourier_coe_apply]
      congr 1
      push_cast
      ring
    · by_cases hn2 : n = -ν - 1
      · subst hn2
        have hkey : 𝓕 G ((-ν - 1 : ℤ) : ℝ) = 1 := by
          rw [hG, map_G Δ v ((-ν - 1 : ℤ) : ℝ) hΔ0 hΔ1]
          have hcast : ((-ν - 1 : ℤ) : ℝ) = -(ν:ℝ) - 1 := by push_cast; ring
          rw [hcast]
          have habs : |v + (-(ν:ℝ) - 1)| ≤ 1 - Δ := by
            rw [abs_le]
            constructor <;> linarith
          rw [trap_eq_one Δ (v + (-(ν:ℝ) - 1)) hΔ0 hΔ1 habs]
          norm_num
        rw [hkey, one_mul, if_neg hn1, if_pos rfl, fourier_coe_apply]
        congr 1
        push_cast
        ring
      · rw [if_neg hn1, if_neg hn2, hzero n hn1 hn2, zero_mul]
  rw [tsum_eq_sum (s := {-ν, -ν - 1}) (fun b hb => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    rw [hterm b, if_neg hb.1, if_neg hb.2])]
  rw [Finset.sum_pair (by omega : (-ν : ℤ) ≠ -ν - 1)]
  rw [hterm (-ν), hterm (-ν - 1)]
  have hne : (-ν - 1 : ℤ) ≠ -ν := by omega
  have hne' : (¬(-ν = -ν - 1) : Prop) := by omega
  simp only [if_pos rfl, hne, hne', ite_false, ite_true]

private theorem eC_int (k : ℤ) : eC (k : ℝ) = 1 := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  refine ⟨k, ?_⟩
  push_cast
  ring

private theorem eC_add_int (x : ℝ) (k : ℤ) : eC (x + (k : ℝ)) = eC x := by
  rw [show x + (k:ℝ) = x + (k:ℝ) from rfl, eC_add', eC_int, mul_one]

private theorem sp_periodic (P X : ℝ) (α : ℝ) (k : ℤ) : Sp P X (α + (k:ℝ)) = Sp P X α := by
  unfold Sp
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  rw [show (α + (k:ℝ)) * (p:ℝ) = α * (p:ℝ) + ((k * (p:ℤ) : ℤ) : ℝ) from by push_cast; ring]
  exact eC_add_int _ _

private theorem majorArcs_add_int (P X : ℝ) (α : ℝ) (k : ℤ) :
    α ∈ majorArcs P X ↔ α + (k:ℝ) ∈ majorArcs P X := by
  constructor
  · rintro ⟨q, a, hq, hqP, hgcd, hineq⟩
    refine ⟨q, a + (q:ℤ) * k, hq, hqP, ?_, ?_⟩
    · show (a + (q:ℤ) * k).gcd (q:ℤ) = 1
      rw [Int.gcd_add_mul_left_left]
      exact hgcd
    · show |(q:ℝ) * (α + (k:ℝ)) - ((a + (q:ℤ) * k : ℤ) : ℝ)| ≤ P / X
      rw [show (q:ℝ) * (α + (k:ℝ)) - ((a + (q:ℤ) * k : ℤ) : ℝ) = (q:ℝ) * α - (a:ℝ) from by
        push_cast; ring]
      exact hineq
  · rintro ⟨q, a, hq, hqP, hgcd, hineq⟩
    refine ⟨q, a - (q:ℤ) * k, hq, hqP, ?_, ?_⟩
    · show (a - (q:ℤ) * k).gcd (q:ℤ) = 1
      rw [show a - (q:ℤ) * k = a + (q:ℤ) * (-k) from by ring, Int.gcd_add_mul_left_left]
      exact hgcd
    · show |(q:ℝ) * α - ((a - (q:ℤ) * k : ℤ) : ℝ)| ≤ P / X
      rw [show (q:ℝ) * α - ((a - (q:ℤ) * k : ℤ) : ℝ) = (q:ℝ) * (α + (k:ℝ)) - (a:ℝ) from by
        push_cast; ring]
      exact hineq

/-! ### The major-arc decomposition and Poisson, assembled -/

private theorem sp_sq_bound (P X α : ℝ) :
    ‖Sp P X α ^ 2‖ ≤ ((∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p)) ^ 2 := by
  have hC : (0:ℝ) ≤ (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p) := by
    apply Finset.sum_nonneg
    intro p hp
    apply Real.log_nonneg
    exact_mod_cast le_of_lt (Nat.Prime.one_lt (Finset.mem_filter.mp hp).2)
  unfold Sp
  rw [norm_pow]
  have hle : ‖∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, (Real.log p : ℂ) * eC (α * p)‖ ≤
      ∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p := by
    calc ‖∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, (Real.log p : ℂ) * eC (α * p)‖
        ≤ ∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, ‖(Real.log p : ℂ) * eC (α * p)‖ :=
          norm_sum_le _ _
      _ = ∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [norm_mul, norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
          apply Real.log_nonneg
          exact_mod_cast le_of_lt (Nat.Prime.one_lt (Finset.mem_filter.mp hp).2)
  calc ‖∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, (Real.log p : ℂ) * eC (α * p)‖ ^ 2
      = ‖∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, (Real.log p : ℂ) * eC (α * p)‖ *
        ‖∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, (Real.log p : ℂ) * eC (α * p)‖ := by ring
    _ ≤ (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p) *
        (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p) :=
        mul_self_le_mul_self (norm_nonneg _) hle
    _ = (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p) ^ 2 := by ring

private theorem integrand_integrable (P X Δ v : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    Integrable (fun α : ℝ => Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) := by
  have hC : (0:ℝ) ≤ (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p) ^ 2 := by positivity
  have hcont : Continuous (fun α : ℝ => Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) := by
    unfold Sp
    exact ((continuous_finsetSum _ (fun p _ => continuous_const.mul (continuous_eC.comp (by fun_prop)))).pow 2).mul
      (kfun_continuous Δ) |>.mul (continuous_eC.comp (by fun_prop))
  refine Integrable.mono' (g := fun α : ℝ => (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p) ^ 2 *
      ((4 / Δ) * (1 + α ^ 2)⁻¹))
    ((integrable_inv_one_add_sq.const_mul (4 / Δ)).const_mul _) hcont.aestronglyMeasurable ?_
  filter_upwards with α
  rw [norm_mul, norm_mul, norm_eC, mul_one]
  have h1 : ‖Sp P X α ^ 2‖ ≤ (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p) ^ 2 :=
    sp_sq_bound P X α
  have h2 : ‖((Kfun Δ α : ℝ) : ℂ)‖ ≤ (4 / Δ) * (1 + α ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := kfun_bound Δ hΔ0 hΔ1 α
    rw [div_eq_mul_inv] at this
    exact this
  calc ‖Sp P X α ^ 2‖ * ‖((Kfun Δ α : ℝ) : ℂ)‖
      ≤ (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p) ^ 2 * ((4 / Δ) * (1 + α ^ 2)⁻¹) :=
        mul_le_mul h1 h2 (norm_nonneg _) hC
    _ = (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p) ^ 2 * ((4 / Δ) * (1 + α ^ 2)⁻¹) := rfl

private theorem majorArcs_periodic_set (P X : ℝ) (S : Set ℝ)
    (hS : S = majorArcs P X ∩ Set.Icc 0 1) :
    majorArcs P X = ⋃ k : ℤ, {t : ℝ | t - (k:ℝ) ∈ S} := by
  subst hS
  ext t
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc]
  constructor
  · intro ht
    refine ⟨⌊t⌋, ?_, ?_, ?_⟩
    · have h2 := (majorArcs_add_int P X t (-⌊t⌋)).mp ht
      convert h2 using 2
      push_cast
      ring
    · have hfr : Int.fract t = t - ⌊t⌋ := Int.self_sub_floor t
      have := Int.fract_nonneg t
      linarith
    · have hfr : Int.fract t = t - ⌊t⌋ := Int.self_sub_floor t
      have := Int.fract_lt_one t
      linarith
  · rintro ⟨k, hk, -⟩
    have h2 := (majorArcs_add_int P X (t - (k:ℝ)) k).mp hk
    convert h2 using 2
    ring



/-! ### Folding the major arcs onto one period, and the identity -/

private theorem measurableSet_majorArcs (P X : ℝ) : MeasurableSet (majorArcs P X) := by
  unfold majorArcs
  measurability

/-- An integrable function on the line is the period integral of its sum of translates. -/
private theorem integral_periodization_local (g : ℝ → ℂ) (hg : Integrable g) :
    (∫ x, g x) = ∫ x in (0 : ℝ)..1, ∑' n : ℤ, g (x + n) := by
  have hi (n : ℤ) : Integrable (fun x : ℝ => g (x + n)) (volume.restrict (Set.Ioc 0 1)) := by
    exact (hg.comp_add_right (n : ℝ)).integrableOn
  have hs : Summable (fun n : ℤ => ∫ x in Set.Ioc (0 : ℝ) 1, ‖g (x + n)‖) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      hg.norm.hasSum_intervalIntegral_comp_add_int.summable
  calc
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, g (x + n) :=
      hg.hasSum_intervalIntegral_comp_add_int.tsum_eq.symm
    _ = _ := by
      simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact integral_tsum_of_summable_integral_norm hi hs

/-- For a periodic `h` and an integrable modulated product, the line integral folds. -/
private theorem fold_of_periodic (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (v : ℝ)
    (hg : Integrable (fun x : ℝ => h x * K x * eC (-(x * v)))) :
    (∫ x, h x * K x * eC (-(x * v))) =
      ∫ x in (0 : ℝ)..1, h x * (∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) := by
  rw [integral_periodization_local _ hg]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  have he (n : ℤ) : h (x + n) = h x := by
    simpa only [mul_one] using hper.int_mul n x
  simp_rw [he, mul_assoc]
  exact tsum_mul_left

private theorem major_periodic (P X : ℝ) :
    Function.Periodic ((majorArcs P X).indicator (fun α => Sp P X α ^ 2)) 1 := by
  classical
  intro α
  have hmem : α + 1 ∈ majorArcs P X ↔ α ∈ majorArcs P X := by
    have := majorArcs_add_int P X α 1
    simpa using this.symm
  have hs : Sp P X (α + 1) = Sp P X α := by simpa using sp_periodic P X α 1
  simp only [Set.indicator_apply, hmem, hs]

private theorem major_intervalIntegrable (P X : ℝ) :
    IntervalIntegrable ((majorArcs P X).indicator (fun α => Sp P X α ^ 2)) volume 0 1 := by
  have hc : Continuous (fun α : ℝ => Sp P X α ^ 2) := by
    unfold Sp eC
    fun_prop
  exact ⟨(hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (measurableSet_majorArcs P X), by simp⟩

/-- The Fourier coefficient of the indicated prime square is `R1` at the same frequency. -/
private theorem major_hcheck (P X : ℝ) (m : ℤ) :
    hcheck ((majorArcs P X).indicator (fun α => Sp P X α ^ 2)) m = R1 P X m := by
  classical
  unfold hcheck R1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have he : (fun α : ℝ => (majorArcs P X).indicator (fun α => Sp P X α ^ 2) α * eC (-(α * m))) =
      (majorArcs P X).indicator (fun α => Sp P X α ^ 2 * eC (-(α * m))) := by
    ext α
    by_cases hα : α ∈ majorArcs P X <;> simp [hα]
  rw [he, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator (measurableSet_majorArcs P X), Set.inter_comm]

/-- The plateau identity: on the plateau the major integral is the sum of the two adjacent
integer coefficients, with kernel weight one. -/
private theorem major_integral_identity (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hlo : Δ ≤ v - (⌊v⌋ : ℝ)) (hhi : v - (⌊v⌋ : ℝ) ≤ 1 - Δ) :
    (∫ α in majorArcs P X, Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) =
      R1 P X ⌊v⌋ + R1 P X (⌊v⌋ + 1) := by
  classical
  set h : ℝ → ℂ := (majorArcs P X).indicator (fun α => Sp P X α ^ 2) with hh
  set K : ℝ → ℂ := fun α => (Kfun Δ α : ℂ) with hK
  have hmeas := measurableSet_majorArcs P X
  have he : (fun α : ℝ => h α * K α * eC (-(α * v))) =
      (majorArcs P X).indicator (fun α => Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) := by
    ext α
    by_cases hα : α ∈ majorArcs P X <;> simp [h, K, hα]
  have hg : Integrable (fun α : ℝ => h α * K α * eC (-(α * v))) := by
    rw [he]
    exact (integrand_integrable P X Δ v hΔ hΔ1).indicator hmeas
  have hfold := fold_of_periodic h K (major_periodic P X) v hg
  rw [he, integral_indicator hmeas] at hfold
  rw [hfold]
  have hg0 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * (⌊v⌋ : ℝ)))) volume 0 1 := by
    apply (major_intervalIntegrable P X).mul_continuousOn
    unfold eC
    fun_prop
  have hg1 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * (((⌊v⌋ + 1 : ℤ)) : ℝ)))) volume 0 1 := by
    apply (major_intervalIntegrable P X).mul_continuousOn
    unfold eC
    fun_prop
  calc (∫ x in (0 : ℝ)..1, h x * (∑' n : ℤ, K (x + n) * eC (-((x + n) * v))))
      = ∫ α in (0 : ℝ)..1, (h α * eC (-(α * (⌊v⌋ : ℝ)))) +
          (h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) := by
        apply intervalIntegral.integral_congr
        intro α _
        dsimp only
        rw [show (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
            eC (-((⌊v⌋ : ℝ) * α)) + eC (-(((⌊v⌋ : ℝ) + 1) * α)) from
          periodization Δ v hΔ hΔ1 ⌊v⌋ hlo hhi α]
        have e1 : eC (-((⌊v⌋ : ℝ) * α)) = eC (-(α * (⌊v⌋ : ℝ))) := by
          congr 1
          ring
        have e2 : eC (-(((⌊v⌋ : ℝ) + 1) * α)) = eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) := by
          congr 1
          push_cast
          ring
        rw [e1, e2, mul_add]
    _ = _ := by
        rw [intervalIntegral.integral_add hg0 hg1,
          show (∫ x in (0 : ℝ)..1, h x * eC (-(x * (⌊v⌋ : ℝ)))) = R1 P X ⌊v⌋ from
            major_hcheck P X ⌊v⌋,
          show (∫ x in (0 : ℝ)..1, h x * eC (-(x * ((⌊v⌋ + 1 : ℤ) : ℝ)))) = R1 P X (⌊v⌋ + 1) from
            major_hcheck P X (⌊v⌋ + 1)]

/-- LEAF. Step of the proof, the plateau identity for the kernel weight, with no counting in
it. For `0 < Δ < 1` with `Δ = ℰ(γ,κ,N)^(-1/8)`, an index `n` whose value `F(n)` has
fractional part between `Δ` and `1 - Δ` lies on the plateau of the kernel, so the real part
of the major arc integral at `F(n)` is the real part of the sum of the two coefficients
adjacent to `F(n)`. One identity, for every `δ`, every `N` and every `n`; it is not an
estimate and it contains no exceptional set. The two fractional hypotheses are satisfied by
every `n` with `F(n)` an integer away from the boundary, so none of them is vacuous. -/
theorem leaf_major_identity (γ δ κ : ℝ) (N n : ℕ)
    (hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)))
    (hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hleft : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ Int.fract (F γ n))
    (hright : Int.fract (F γ n) ≤ 1 - calE γ κ N ^ (-(1 / 8 : ℝ))) :
    (∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
        Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
          * eC (-(α * F γ n))).re =
      (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re := by
  have hlo : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ F γ n - (⌊F γ n⌋ : ℝ) := by
    simpa only [Int.self_sub_floor] using hleft
  have hhi : F γ n - (⌊F γ n⌋ : ℝ) ≤ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) := by
    simpa only [Int.self_sub_floor] using hright
  have hid := major_integral_identity (F γ N ^ (6 * δ)) (F γ N)
    (calE γ κ N ^ (-(1 / 8 : ℝ))) (F γ n) hΔ hΔ1 hlo hhi
  rw [hid]
  simp only [nu]

/-- LEAF. Step of the proof, the sparse exceptional set of the coefficients, with no major
arc integral in it. For `1 < γ < 3/2` and small `δ`, and for `κ` below a positive cap that
does not depend on `κ` itself, all but `O(N ℰ^(-1/12))` indices of the window have the sum of
the two adjacent integer coefficients at least `c₀ F(N) ℰ^(-1/10)` in real part. This is the
coefficient lower bound of Lemma 7 and display 20, a count of indices of the window, and it
is strictly weaker than the split's statement because the quantity counted is a sum of two
coefficients rather than an integral. -/
theorem leaf_coefficient_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
              F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)).filter (fun n : ℕ =>
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
                  R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
                    c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- LEAF. Step of the proof, the fractional boundary count of display 23, purely a count of
indices. For `1 < γ < 3/2` and `κ` below a positive cap, the indices of the window whose
value `F(n)` is within `ℰ^(-1/8)` of an integer are at most `O(N ℰ^(-1/8))` in number. No
coefficient and no integral occurs, so this is strictly weaker than the split's statement.
At `N = 0` and `N = 1` the window is empty and the count is `0`, and the linear bound has a
positive right side, so the inequality is not vacuous there. -/
theorem leaf_fractional_boundary (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ((((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
            F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)).filter (fun n : ℕ =>
              Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
                1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-! ### Assembly -/

/-- Lemma 8 from the three leaves above: the unchanged statement of `lemma8`. The indices of
the window whose integral is small are either on the fractional boundary, counted by the
boundary leaf, or off it, where the identity leaf rewrites the integral into the sum of the
two adjacent coefficients, which is then small only on the exceptional set counted by the
coefficient leaf. The two counts are added, and `ℰ^(-1/8) ≤ ℰ^(-1/12)` absorbs the boundary
count into the exponent of the statement. -/
theorem lemma8_split : Lemma8 := by
  classical
  intro γ h1 h2
  obtain ⟨δ₀, hδ₀, hcoeff⟩ := leaf_coefficient_lower γ h1 h2
  obtain ⟨κb, hκb, hboundary⟩ := leaf_fractional_boundary γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, hcoeff⟩ := hcoeff δ hδ hδsmall
  let κ := min κa κb
  have hκ : 0 < κ := lt_min hκa hκb
  obtain ⟨c₀, Ba, hc₀, hBa, Na, ha⟩ := hcoeff κ hκ (min_le_left _ _)
  obtain ⟨Bb, hBb, Nb, hb⟩ := hboundary κ hκ (min_le_right _ _)
  refine ⟨κ, c₀, Ba + Bb, hκ, hc₀, max 2 (max Na Nb), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE : 1 < calE γ κ N := by
    unfold calE
    exact Real.one_lt_exp_iff.mpr (mul_pos hκ (Real.rpow_pos_of_pos hlog _))
  have hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hE) _
  have hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 := by
    rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hE)]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg (Real.log_pos hE) (by norm_num))
  let W := (Finset.range (2 * N + 1)).filter (fun n : ℕ =>
    F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)
  let A := W.filter (fun n : ℕ =>
    (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
        c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))
  let B := W.filter (fun n : ℕ =>
    Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
      1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))
  have hsubset : (Finset.range (2 * N + 1)).filter (fun n : ℕ =>
      F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N ∧
      (∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
          Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
            * eC (-(α * F γ n))).re
        < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) ⊆ A ∪ B := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn0, hnA, hnBv, hnmajor⟩
    have hnW : n ∈ W := Finset.mem_filter.mpr ⟨hn0, hnA, hnBv⟩
    by_cases hnB : n ∈ B
    · exact Finset.mem_union_right _ hnB
    · have hgood : ¬ (Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n)) := by
        intro hbad
        exact hnB (Finset.mem_filter.mpr ⟨hnW, hbad⟩)
      have hid := leaf_major_identity γ δ κ N n hΔ hΔ1
        (le_of_not_gt (fun h => hgood (Or.inl h)))
        (le_of_not_gt (fun h => hgood (Or.inr h)))
      refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnW, ?_⟩)
      rw [hid] at hnmajor
      exact hnmajor
  have hcard : (((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
      F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N ∧
      (∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
          Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
            * eC (-(α * F γ n))).re
        < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      (A.card : ℝ) + B.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le A B)
  have hpow : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ calE γ κ N ^ (-(1 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hE.le (by norm_num)
  calc (((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
      F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N ∧
      (∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
          Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
            * eC (-(α * F γ n))).re
        < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ)
      ≤ (A.card : ℝ) + B.card := hcard
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
          Bb * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := add_le_add (ha N hNa) (hb N hNb)
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
          Bb * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by gcongr
    _ = (Ba + Bb) * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by ring

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.lemma8_split
