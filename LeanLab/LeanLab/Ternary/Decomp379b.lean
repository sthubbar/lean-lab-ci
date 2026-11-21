/-
Helfgott https://arxiv.org/abs/1312.7748v2, pages 56 and 69 to 71.
Use the corrected minor arc arithmetic already proved in Helfgott2013.Slip.
The weighted total and the discarded part are separate analytic inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.State1535
import LeanLab.HelfgottArcs.Statements
import LeanLab.Helfgott2013.Slip
import LeanLab.Common.PsiTheta.Bound
import LeanLab.Helfgott2013.MellinSup


/-
The uniform sup bound for Helfgott's eta-plus weight, equation (7.3), proved from the
second-derivative norm in the multiplicative variable.  This supplies the only analytic input
of `helfgott_discarded_upper`.
-/
namespace EtaBound379

open Real MeasureTheory Filter
open scoped FourierTransform Topology


/-- `hfun` in factored form on the positive half line (no cutoff, as `max (2-y) 0`). -/
theorem hfun_eq_of_pos {y : ℝ} (hy : 0 < y) :
    LeanLab.HelfgottArcs.hfun y =
      (max (2 - y) 0) ^ 3 * (y ^ 2 * Real.exp (y - 1 / 2)) := by
  unfold LeanLab.HelfgottArcs.hfun
  by_cases h2 : y ≤ 2
  · rw [if_pos ⟨hy.le, h2⟩, max_eq_left (by linarith : (0 : ℝ) ≤ 2 - y)]
    ring
  · rw [if_neg (by tauto), max_eq_right (by linarith : 2 - y ≤ 0)]
    ring

/-- `x ↦ (max x 0)^(k+1)` has derivative `(k+1) (max x 0)^k` for `k ≥ 1`. -/
theorem hasDerivAt_max_pow_succ {k : ℕ} (hk : 1 ≤ k) (w : ℝ) :
    HasDerivAt (fun x : ℝ => (max x 0) ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * (max w 0) ^ k) w := by
  rcases lt_trichotomy w 0 with h | h | h
  · have he : (fun x : ℝ => (max x 0) ^ (k + 1)) =ᶠ[𝓝 w] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds h] with x hx
      rw [max_eq_right hx.le]
      simp
    rw [he.hasDerivAt_iff, max_eq_right h.le]
    have : ((k + 1 : ℕ) : ℝ) * (0 : ℝ) ^ k = 0 := by
      rw [zero_pow (by omega : k ≠ 0), mul_zero]
    rw [this]
    exact hasDerivAt_const w 0
  · subst h
    rw [hasDerivAt_iff_tendsto_slope]
    have hsl : (fun y : ℝ => (y - 0)⁻¹ • ((max y 0) ^ (k + 1) - (max (0 : ℝ) 0) ^ (k + 1)))
        =ᶠ[𝓝[≠] (0 : ℝ)] (fun y => (max y 0) ^ k) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy0 : y ≠ 0 := by simpa using hy
      rw [max_eq_right (le_refl (0 : ℝ)), zero_pow (by omega : k + 1 ≠ 0), sub_zero, smul_eq_mul]
      by_cases hy' : 0 < y
      · rw [max_eq_left hy'.le]
        rw [sub_zero, pow_succ]
        rw [show y⁻¹ * (y ^ k * y) = y ^ k * (y⁻¹ * y) by ring, inv_mul_cancel₀ hy0, mul_one]
      · rw [max_eq_right (by linarith : y ≤ 0), zero_pow (by omega : k ≠ 0)]
        simp
    have hcont : Continuous (fun y : ℝ => (max y 0) ^ k) :=
      (continuous_id.max continuous_const).pow k
    have hlim : Tendsto (fun y : ℝ => (max y 0) ^ k) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have h0 : (max (0 : ℝ) 0) ^ k = 0 := by
        rw [max_eq_right (le_refl (0 : ℝ)), zero_pow (by omega : k ≠ 0)]
      have hc0 : ContinuousAt (fun y : ℝ => (max y 0) ^ k) (0 : ℝ) := hcont.continuousAt
      have := hc0.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      rwa [h0] at this
    have htarget : (((k + 1 : ℕ)) : ℝ) * (max (0 : ℝ) 0) ^ k = 0 := by
      rw [max_eq_right (le_refl (0 : ℝ)), zero_pow (by omega : k ≠ 0), mul_zero]
    rw [htarget]
    exact Filter.Tendsto.congr' hsl.symm hlim
  · have he : (fun x : ℝ => (max x 0) ^ (k + 1)) =ᶠ[𝓝 w] (fun x => x ^ (k + 1)) := by
      filter_upwards [isOpen_Ioi.mem_nhds h] with x hx
      rw [max_eq_left hx.le]
    rw [he.hasDerivAt_iff]
    simpa [max_eq_left h.le] using hasDerivAt_pow (k + 1) w

/-- A two-step derivative criterion for `C²`. -/
theorem contDiff_two_of_deriv {F f' g' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt F (f' x) x) (_hc1 : Continuous f')
    (h2 : ∀ x, HasDerivAt f' (g' x) x) (hc2 : Continuous g') :
    ContDiff ℝ 2 F := by
  have hd : deriv F = f' := funext fun x => (h1 x).deriv
  have hd2 : deriv f' = g' := funext fun x => (h2 x).deriv
  refine (contDiff_succ_iff_deriv (n := 1) (f := F) (𝕜 := ℝ)).mpr
    ⟨fun x => (h1 x).differentiableAt, ?_, ?_⟩
  · intro h; exact absurd h (by norm_num)
  · rw [hd]
    refine (contDiff_succ_iff_deriv (n := 0) (f := f') (𝕜 := ℝ)).mpr
      ⟨fun x => (h2 x).differentiableAt, ?_, ?_⟩
    · intro h; exact absurd h (by norm_num)
    · rw [hd2]; simpa using hc2

/-- `x ↦ (max x 0)^3` is `C²`. -/
theorem contDiff_max_cube : ContDiff ℝ 2 (fun x : ℝ => (max x 0) ^ 3) := by
  apply contDiff_two_of_deriv (f' := fun x => 3 * (max x 0) ^ 2) (g' := fun x => 6 * max x 0)
  · intro x
    have := hasDerivAt_max_pow_succ (k := 2) (by norm_num) x
    simpa using this
  · exact continuous_const.mul ((continuous_id.max continuous_const).pow 2)
  · intro x
    have h := (hasDerivAt_max_pow_succ (k := 1) (by norm_num) x).const_mul 3
    have hc : (3 : ℝ) * ((((1 + 1 : ℕ)) : ℝ) * (max x 0) ^ 1) = 6 * max x 0 := by
      push_cast; ring
    rw [hc] at h
    exact h
  · exact continuous_const.mul (continuous_id.max continuous_const)

/-! ### The profile `u ↦ hfun (t e^{-u})` and its derivatives -/

/-- Derivative of a scaled monomial. -/
theorem hasDerivAt_cmul_pow (c : ℝ) (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => c * y ^ n) (c * ((n : ℝ) * y ^ (n - 1))) y :=
  (hasDerivAt_pow n y).const_mul c

/-- `t e^{-u}` as a function of `u`. -/
theorem hasDerivAt_y (t u : ℝ) :
    HasDerivAt (fun u : ℝ => t * Real.exp (-u)) (-(t * Real.exp (-u))) u := by
  have h := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
  have := h.const_mul t
  simpa [Function.comp_def] using this

/-- The model polynomial part of `hfun` on `[0,2]`. -/
theorem hasDerivAt_model (y : ℝ) :
    HasDerivAt (fun y : ℝ => 8 * y ^ 2 - 12 * y ^ 3 + 6 * y ^ 4 - y ^ 5)
      (16 * y - 36 * y ^ 2 + 24 * y ^ 3 - 5 * y ^ 4) y := by
  have h2 := hasDerivAt_cmul_pow 8 2 y
  have h3 := hasDerivAt_cmul_pow 12 3 y
  have h4 := hasDerivAt_cmul_pow 6 4 y
  have h5 := hasDerivAt_cmul_pow 1 5 y
  have h := ((h2.sub h3).add h4).sub h5
  convert h using 1 <;> first | (funext z; simp only [Pi.sub_apply, Pi.add_apply]; push_cast; ring) | (push_cast; ring)

/-- `y ↦ (8y² - 12y³ + 6y⁴ - y⁵) e^{y-1/2}` and its derivative. -/
theorem hasDerivAt_model_exp (y : ℝ) :
    HasDerivAt (fun y : ℝ => (8 * y ^ 2 - 12 * y ^ 3 + 6 * y ^ 4 - y ^ 5) * Real.exp (y - 1/2))
      ((16 * y - 28 * y ^ 2 + 12 * y ^ 3 + y ^ 4 - y ^ 5) * Real.exp (y - 1/2)) y := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (y - 1/2)) (Real.exp (y - 1/2)) y := by
    have h := (Real.hasDerivAt_exp (y - 1/2)).comp y ((hasDerivAt_id y).sub_const (1/2))
    simpa [Function.comp_def] using h
  have h := (hasDerivAt_model y).mul hexp
  convert h using 1 <;> first | (funext z; simp only [Pi.sub_apply, Pi.add_apply]; push_cast; ring) | (push_cast; ring)

/-- `y ↦ A(y) e^{y-1/2}` with `A = -16y²+28y³-12y⁴-y⁵+y⁶`, and its derivative. -/
theorem hasDerivAt_model2_exp (y : ℝ) :
    HasDerivAt
      (fun y : ℝ => (-16 * y ^ 2 + 28 * y ^ 3 - 12 * y ^ 4 - y ^ 5 + y ^ 6) * Real.exp (y - 1/2))
      ((-32 * y + 68 * y ^ 2 - 20 * y ^ 3 - 17 * y ^ 4 + 5 * y ^ 5 + y ^ 6) * Real.exp (y - 1/2)) y := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (y - 1/2)) (Real.exp (y - 1/2)) y := by
    have h := (Real.hasDerivAt_exp (y - 1/2)).comp y ((hasDerivAt_id y).sub_const (1/2))
    simpa [Function.comp_def] using h
  have hpoly : HasDerivAt
      (fun y : ℝ => -16 * y ^ 2 + 28 * y ^ 3 - 12 * y ^ 4 - y ^ 5 + y ^ 6)
      (-32 * y + 84 * y ^ 2 - 48 * y ^ 3 - 5 * y ^ 4 + 6 * y ^ 5) y := by
    have h2 := hasDerivAt_cmul_pow (-16) 2 y
    have h3 := hasDerivAt_cmul_pow 28 3 y
    have h4 := hasDerivAt_cmul_pow (-12) 4 y
    have h5 := hasDerivAt_cmul_pow (-1) 5 y
    have h6 := hasDerivAt_cmul_pow 1 6 y
    have h := ((((h2.add h3).add h4).add h5).add h6)
    convert h using 1 <;>
      first | (funext z; simp only [Pi.sub_apply, Pi.add_apply]; push_cast; ring) | (push_cast; ring)
  have h := hpoly.mul hexp
  convert h using 1 <;> first | (funext z; simp only [Pi.sub_apply, Pi.add_apply]; push_cast; ring) | (push_cast; ring)

/-- The profile is `hfun` composed with `u ↦ t e^{-u}`; its derivative where that argument is below two. -/
theorem hasDerivAt_profile_lt (t : ℝ) (ht : 0 < t) {u : ℝ} (h2 : t * Real.exp (-u) < 2) :
    HasDerivAt (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)))
      ((-16 * (t * Real.exp (-u)) ^ 2 + 28 * (t * Real.exp (-u)) ^ 3
        - 12 * (t * Real.exp (-u)) ^ 4 - (t * Real.exp (-u)) ^ 5
        + (t * Real.exp (-u)) ^ 6) * Real.exp (t * Real.exp (-u) - 1/2)) u := by
  have hopen : {u' : ℝ | t * Real.exp (-u') < (2 : ℝ)} ∈ 𝓝 u :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds h2
  have hev : (fun u' : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u')))
      =ᶠ[𝓝 u] (fun u' : ℝ =>
        (8 * (t * Real.exp (-u')) ^ 2 - 12 * (t * Real.exp (-u')) ^ 3
          + 6 * (t * Real.exp (-u')) ^ 4 - (t * Real.exp (-u')) ^ 5)
          * Real.exp (t * Real.exp (-u') - 1/2)) := by
    filter_upwards [hopen] with u' hu'
    rw [LeanLab.HelfgottArcs.hfun,
      if_pos ⟨(by positivity : (0:ℝ) ≤ t * Real.exp (-u')), hu'.le⟩]
    ring
  have hcomp := (hasDerivAt_model_exp (t * Real.exp (-u))).comp u (hasDerivAt_y t u)
  have hval : ((16 * (t * Real.exp (-u)) - 28 * (t * Real.exp (-u)) ^ 2
        + 12 * (t * Real.exp (-u)) ^ 3 + (t * Real.exp (-u)) ^ 4
        - (t * Real.exp (-u)) ^ 5) * Real.exp (t * Real.exp (-u) - 1/2))
      * (-(t * Real.exp (-u)))
      = (-16 * (t * Real.exp (-u)) ^ 2 + 28 * (t * Real.exp (-u)) ^ 3
        - 12 * (t * Real.exp (-u)) ^ 4 - (t * Real.exp (-u)) ^ 5
        + (t * Real.exp (-u)) ^ 6) * Real.exp (t * Real.exp (-u) - 1/2) := by ring
  rw [hval] at hcomp
  have hcomp' : HasDerivAt (fun u' : ℝ =>
      (8 * (t * Real.exp (-u')) ^ 2 - 12 * (t * Real.exp (-u')) ^ 3
        + 6 * (t * Real.exp (-u')) ^ 4 - (t * Real.exp (-u')) ^ 5)
        * Real.exp (t * Real.exp (-u') - 1/2))
      ((-16 * (t * Real.exp (-u)) ^ 2 + 28 * (t * Real.exp (-u)) ^ 3
        - 12 * (t * Real.exp (-u)) ^ 4 - (t * Real.exp (-u)) ^ 5
        + (t * Real.exp (-u)) ^ 6) * Real.exp (t * Real.exp (-u) - 1/2)) u := by
    simpa [Function.comp_def] using hcomp
  exact hcomp'.congr_of_eventuallyEq hev

/-- Second derivative of the profile where its argument is below two. -/
theorem hasDerivAt_deriv_profile_lt (t : ℝ) (ht : 0 < t) {u : ℝ}
    (h2 : t * Real.exp (-u) < 2) :
    HasDerivAt
      (fun u : ℝ => (-16 * (t * Real.exp (-u)) ^ 2 + 28 * (t * Real.exp (-u)) ^ 3
        - 12 * (t * Real.exp (-u)) ^ 4 - (t * Real.exp (-u)) ^ 5
        + (t * Real.exp (-u)) ^ 6) * Real.exp (t * Real.exp (-u) - 1/2))
      ((32 * (t * Real.exp (-u)) ^ 2 - 68 * (t * Real.exp (-u)) ^ 3
        + 20 * (t * Real.exp (-u)) ^ 4 + 17 * (t * Real.exp (-u)) ^ 5
        - 5 * (t * Real.exp (-u)) ^ 6 - (t * Real.exp (-u)) ^ 7)
        * Real.exp (t * Real.exp (-u) - 1/2)) u := by
  have hcomp := (hasDerivAt_model2_exp (t * Real.exp (-u))).comp u (hasDerivAt_y t u)
  have hval : ((-32 * (t * Real.exp (-u)) + 68 * (t * Real.exp (-u)) ^ 2
        - 20 * (t * Real.exp (-u)) ^ 3 - 17 * (t * Real.exp (-u)) ^ 4
        + 5 * (t * Real.exp (-u)) ^ 5 + (t * Real.exp (-u)) ^ 6)
        * Real.exp (t * Real.exp (-u) - 1/2)) * (-(t * Real.exp (-u)))
      = (32 * (t * Real.exp (-u)) ^ 2 - 68 * (t * Real.exp (-u)) ^ 3
        + 20 * (t * Real.exp (-u)) ^ 4 + 17 * (t * Real.exp (-u)) ^ 5
        - 5 * (t * Real.exp (-u)) ^ 6 - (t * Real.exp (-u)) ^ 7)
        * Real.exp (t * Real.exp (-u) - 1/2) := by ring
  rw [hval] at hcomp
  simpa [Function.comp_def] using hcomp

/-- A degree-ten Bernstein certificate: `|Q(y)| ≤ 10.3 y` on `[0,2]`, where `Q y = y R y`. -/
theorem abs_R_le {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    |(-y ^ 6 - 5 * y ^ 5 + 17 * y ^ 4 + 20 * y ^ 3 - 68 * y ^ 2 + 32 * y : ℝ)| ≤ (103 / 10) := by
  have hb : (0:ℝ) ≤ 2 - y := by linarith
  have e1 : (-y ^ 6 - 5 * y ^ 5 + 17 * y ^ 4 + 20 * y ^ 3 - 68 * y ^ 2 + 32 * y : ℝ) - (103 / 10) =
      ((-103:ℝ)/10240) * (2 - y) ^ 10
      + ((-39:ℝ)/1024) * (y * (2 - y) ^ 9)
      + ((-319:ℝ)/2048) * (y ^ 2 * (2 - y) ^ 8)
      + ((-237:ℝ)/256) * (y ^ 3 * (2 - y) ^ 7)
      + ((-3011:ℝ)/1024) * (y ^ 4 * (2 - y) ^ 6)
      + ((-12329:ℝ)/2560) * (y ^ 5 * (2 - y) ^ 5)
      + ((-4323:ℝ)/1024) * (y ^ 6 * (2 - y) ^ 4)
      + ((-477:ℝ)/256) * (y ^ 7 * (2 - y) ^ 3)
      + ((-639:ℝ)/2048) * (y ^ 8 * (2 - y) ^ 2)
      + ((-7:ℝ)/1024) * (y ^ 9 * (2 - y) ^ 1)
      + ((-103:ℝ)/10240) * y ^ 10 := by ring
  have t1_0 : ((-103:ℝ)/10240) * (2 - y) ^ 10 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hb 10)
  have t1_1 : ((-39:ℝ)/1024) * (y * (2 - y) ^ 9) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) (mul_nonneg hy0 (pow_nonneg hb 9))
  have t1_2 : ((-319:ℝ)/2048) * (y ^ 2 * (2 - y) ^ 8) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 2) (pow_nonneg hb 8))
  have t1_3 : ((-237:ℝ)/256) * (y ^ 3 * (2 - y) ^ 7) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 3) (pow_nonneg hb 7))
  have t1_4 : ((-3011:ℝ)/1024) * (y ^ 4 * (2 - y) ^ 6) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 4) (pow_nonneg hb 6))
  have t1_5 : ((-12329:ℝ)/2560) * (y ^ 5 * (2 - y) ^ 5) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 5) (pow_nonneg hb 5))
  have t1_6 : ((-4323:ℝ)/1024) * (y ^ 6 * (2 - y) ^ 4) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 6) (pow_nonneg hb 4))
  have t1_7 : ((-477:ℝ)/256) * (y ^ 7 * (2 - y) ^ 3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 7) (pow_nonneg hb 3))
  have t1_8 : ((-639:ℝ)/2048) * (y ^ 8 * (2 - y) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 8) (pow_nonneg hb 2))
  have t1_9 : ((-7:ℝ)/1024) * (y ^ 9 * (2 - y) ^ 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 9) (pow_nonneg hb 1))
  have t1_10 : ((-103:ℝ)/10240) * y ^ 10 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hy0 10)
  have h1 : (-y ^ 6 - 5 * y ^ 5 + 17 * y ^ 4 + 20 * y ^ 3 - 68 * y ^ 2 + 32 * y : ℝ) - (103 / 10) ≤ 0 := by
    rw [e1]
    linarith [t1_0, t1_1, t1_2, t1_3, t1_4, t1_5, t1_6, t1_7, t1_8, t1_9, t1_10]

  have e2 : -(-y ^ 6 - 5 * y ^ 5 + 17 * y ^ 4 + 20 * y ^ 3 - 68 * y ^ 2 + 32 * y : ℝ) - (103 / 10) =
      ((-103:ℝ)/10240) * (2 - y) ^ 10
      + ((-167:ℝ)/1024) * (y * (2 - y) ^ 9)
      + ((-1535:ℝ)/2048) * (y ^ 2 * (2 - y) ^ 8)
      + ((-381:ℝ)/256) * (y ^ 3 * (2 - y) ^ 7)
      + ((-1315:ℝ)/1024) * (y ^ 4 * (2 - y) ^ 6)
      + ((-649:ℝ)/2560) * (y ^ 5 * (2 - y) ^ 5)
      + ((-3:ℝ)/1024) * (y ^ 6 * (2 - y) ^ 4)
      + ((-141:ℝ)/256) * (y ^ 7 * (2 - y) ^ 3)
      + ((-1215:ℝ)/2048) * (y ^ 8 * (2 - y) ^ 2)
      + ((-199:ℝ)/1024) * (y ^ 9 * (2 - y) ^ 1)
      + ((-103:ℝ)/10240) * y ^ 10 := by ring
  have t2_0 : ((-103:ℝ)/10240) * (2 - y) ^ 10 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hb 10)
  have t2_1 : ((-167:ℝ)/1024) * (y * (2 - y) ^ 9) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) (mul_nonneg hy0 (pow_nonneg hb 9))
  have t2_2 : ((-1535:ℝ)/2048) * (y ^ 2 * (2 - y) ^ 8) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 2) (pow_nonneg hb 8))
  have t2_3 : ((-381:ℝ)/256) * (y ^ 3 * (2 - y) ^ 7) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 3) (pow_nonneg hb 7))
  have t2_4 : ((-1315:ℝ)/1024) * (y ^ 4 * (2 - y) ^ 6) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 4) (pow_nonneg hb 6))
  have t2_5 : ((-649:ℝ)/2560) * (y ^ 5 * (2 - y) ^ 5) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 5) (pow_nonneg hb 5))
  have t2_6 : ((-3:ℝ)/1024) * (y ^ 6 * (2 - y) ^ 4) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 6) (pow_nonneg hb 4))
  have t2_7 : ((-141:ℝ)/256) * (y ^ 7 * (2 - y) ^ 3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 7) (pow_nonneg hb 3))
  have t2_8 : ((-1215:ℝ)/2048) * (y ^ 8 * (2 - y) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 8) (pow_nonneg hb 2))
  have t2_9 : ((-199:ℝ)/1024) * (y ^ 9 * (2 - y) ^ 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg hy0 9) (pow_nonneg hb 1))
  have t2_10 : ((-103:ℝ)/10240) * y ^ 10 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hy0 10)
  have h2 : -(-y ^ 6 - 5 * y ^ 5 + 17 * y ^ 4 + 20 * y ^ 3 - 68 * y ^ 2 + 32 * y : ℝ) - (103 / 10) ≤ 0 := by
    rw [e2]
    linarith [t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7, t2_8, t2_9, t2_10]

  rw [abs_le]
  constructor <;> linarith

/-- The profile vanishes identically above two. -/
theorem profile_eq_zero_of_gt (t : ℝ) {u : ℝ} (h2 : 2 < t * Real.exp (-u)) :
    (fun u' : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u'))) =ᶠ[𝓝 u] 0 := by
  have hopen : {u' : ℝ | (2 : ℝ) < t * Real.exp (-u')} ∈ 𝓝 u :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds h2
  filter_upwards [hopen] with u' hu'
  show LeanLab.HelfgottArcs.hfun (t * Real.exp (-u')) = 0
  rw [LeanLab.HelfgottArcs.hfun, if_neg (by rintro ⟨h1, h2'⟩; linarith)]

/-- The first derivative of the profile, as a function of `u`, below two. -/
theorem deriv_profile_lt (t : ℝ) (ht : 0 < t) {u : ℝ} (h2 : t * Real.exp (-u) < 2) :
    deriv (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) u
      = (-16 * (t * Real.exp (-u)) ^ 2 + 28 * (t * Real.exp (-u)) ^ 3
        - 12 * (t * Real.exp (-u)) ^ 4 - (t * Real.exp (-u)) ^ 5
        + (t * Real.exp (-u)) ^ 6) * Real.exp (t * Real.exp (-u) - 1/2) :=
  (hasDerivAt_profile_lt t ht h2).deriv

/-- The second derivative of the profile below two. -/
theorem iteratedDeriv_two_profile_lt (t : ℝ) (ht : 0 < t) {u : ℝ}
    (h2 : t * Real.exp (-u) < 2) :
    iteratedDeriv 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) u
      = (32 * (t * Real.exp (-u)) ^ 2 - 68 * (t * Real.exp (-u)) ^ 3
        + 20 * (t * Real.exp (-u)) ^ 4 + 17 * (t * Real.exp (-u)) ^ 5
        - 5 * (t * Real.exp (-u)) ^ 6 - (t * Real.exp (-u)) ^ 7)
        * Real.exp (t * Real.exp (-u) - 1/2) := by
  have hopen : {u' : ℝ | t * Real.exp (-u') < (2 : ℝ)} ∈ 𝓝 u :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds h2
  have hev : deriv (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)))
      =ᶠ[𝓝 u] (fun u' : ℝ =>
        (-16 * (t * Real.exp (-u')) ^ 2 + 28 * (t * Real.exp (-u')) ^ 3
          - 12 * (t * Real.exp (-u')) ^ 4 - (t * Real.exp (-u')) ^ 5
          + (t * Real.exp (-u')) ^ 6) * Real.exp (t * Real.exp (-u') - 1/2)) := by
    filter_upwards [hopen] with u' hu'
    exact deriv_profile_lt t ht hu'
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq,
    (hasDerivAt_deriv_profile_lt t ht h2).deriv]

/-- The second derivative of the profile vanishes above two. -/
theorem iteratedDeriv_two_profile_gt (t : ℝ) {u : ℝ} (h2 : 2 < t * Real.exp (-u)) :
    iteratedDeriv 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) u = 0 := by
  have hev0 := profile_eq_zero_of_gt t h2
  have hev1 : deriv (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) =ᶠ[𝓝 u] deriv 0 :=
    hev0.deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev1.deriv_eq]
  simp

/-- Change of variables `y = t e^{-u}` on the positive half line. -/
theorem integral_exp_comp (t : ℝ) (ht : 0 < t) (G : ℝ → ℝ) :
    (∫ u : ℝ, G (t * Real.exp (-u))) = ∫ y in Set.Ioi (0 : ℝ), G y / y := by
  have himg : (fun u : ℝ => t * Real.exp (-u)) '' Set.univ = Set.Ioi 0 := by
    ext y
    constructor
    · rintro ⟨u, -, rfl⟩
      exact mul_pos ht (Real.exp_pos _)
    · intro hy
      refine ⟨-Real.log (y / t), Set.mem_univ _, ?_⟩
      have hy' : 0 < y / t := div_pos hy ht
      have hexp : Real.exp (-(-Real.log (y / t))) = y / t := by
        rw [neg_neg, Real.exp_log hy']
      calc t * Real.exp (-(-Real.log (y / t))) = t * (y / t) := by rw [hexp]
        _ = y := by field_simp
  have hinj : Set.InjOn (fun u : ℝ => t * Real.exp (-u)) Set.univ := by
    intro u1 _ u2 _ h
    have h1 : Real.exp (-u1) = Real.exp (-u2) := mul_left_cancel₀ ht.ne' h
    have h2 := Real.exp_injective h1
    linarith
  have hderiv : ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun u : ℝ => t * Real.exp (-u)) (-t * Real.exp (-u)) Set.univ u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) u := by
      have h := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun u : ℝ => t * Real.exp (-u)) (t * -Real.exp (-u)) u :=
      h1.const_mul t
    have h3 : t * -Real.exp (-u) = -t * Real.exp (-u) := by ring
    rw [← h3]
    exact h2.hasDerivWithinAt
  have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun u : ℝ => t * Real.exp (-u)) (f' := fun u : ℝ => -t * Real.exp (-u))
    (s := Set.univ) MeasurableSet.univ hderiv hinj
    (g := fun y : ℝ => G y / y)
  rw [himg, setIntegral_univ] at hsub
  rw [hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  have habs : |(-t) * Real.exp (-u)| = t * Real.exp (-u) := by
    rw [abs_mul, abs_neg, abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
  have hne : t * Real.exp (-u) ≠ 0 := ne_of_gt (by positivity)
  change G (t * Real.exp (-u))
      = |(-t) * Real.exp (-u)| • (G (t * Real.exp (-u)) / (t * Real.exp (-u)))
  rw [habs, smul_eq_mul, mul_div_cancel₀ _ hne]

/-- A function vanishing below `u₀` and decaying like `e^{-u}` past it is integrable. -/
theorem integrable_of_decay {F : ℝ → ℝ} (u₀ C : ℝ) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable F) (hz : ∀ u, u < u₀ → F u = 0)
    (hb : ∀ u, u₀ < u → ‖F u‖ ≤ C * Real.exp (-u)) :
    Integrable F := by
  have hIntOn : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi u₀) := by
    simpa using exp_neg_integrableOn_Ioi u₀ (b := 1) (by norm_num)
  have hIntIoi : Integrable (Set.indicator (Set.Ioi u₀) (fun u : ℝ => C * Real.exp (-u))) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact hIntOn.const_mul C
  refine hIntIoi.mono hmeas ?_
  have hne : ∀ᵐ u : ℝ, u ≠ u₀ := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with u hu
  by_cases h : u ∈ Set.Ioi u₀
  · rw [Set.indicator_of_mem h]
    have hnn : (0:ℝ) ≤ C * Real.exp (-u) := by positivity
    calc ‖F u‖ ≤ C * Real.exp (-u) := hb u h
      _ = ‖C * Real.exp (-u)‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  · rw [Set.indicator_of_notMem h, norm_zero]
    have hlt : u < u₀ := lt_of_le_of_ne (by simpa using h) hu
    rw [hz u hlt, norm_zero]

/-- A bound for the profile itself. -/
theorem norm_hfun_le {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    ‖LeanLab.HelfgottArcs.hfun y‖ ≤ 144 * y ^ 2 := by
  have hy : LeanLab.HelfgottArcs.hfun y = y ^ 2 * (2 - y) ^ 3 * Real.exp (y - 1 / 2) := by
    rw [LeanLab.HelfgottArcs.hfun, if_pos ⟨hy0, hy2⟩]
  rw [hy, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h2n : (0:ℝ) ≤ 2 - y := by linarith
  have h1 : (2 - y) ^ 3 ≤ 8 := by nlinarith [h2n, sq_nonneg (2 - y)]
  have h3n : (0:ℝ) ≤ (2 - y) ^ 3 := pow_nonneg h2n 3
  have h2 : Real.exp (y - 1 / 2) ≤ 5 := by
    have hexp2 : Real.exp (y - 1/2) ≤ Real.exp (3/2) := Real.exp_le_exp_of_le (by linarith)
    have hsq : Real.exp (3 / 2) ^ 2 = Real.exp 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h4 : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [show (3:ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; ring
    have h5 : (Real.exp 1) ^ 3 ≤ 21 := by
      have hlt := Real.exp_one_lt_d9
      have h0 : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
      calc (Real.exp 1) ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ h0 hlt.le 3
        _ ≤ 21 := by norm_num
    have h6 : Real.exp (3/2) ≤ 5 := by
      have hsq2 : Real.exp (3/2) ^ 2 ≤ 25 := by
        rw [hsq, h4]; linarith
      nlinarith [Real.exp_pos (3/2), hsq2]
    exact le_trans hexp2 h6
  have hsq : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
  calc y ^ 2 * (2 - y) ^ 3 * Real.exp (y - 1 / 2)
      ≤ y ^ 2 * 8 * 5 := by
        apply mul_le_mul (mul_le_mul le_rfl h1 h3n hsq) h2 (Real.exp_pos _).le
        positivity
    _ ≤ 144 * y ^ 2 := by nlinarith [hsq]

/-- The second derivative of the profile in closed form, almost everywhere. -/
theorem ae_iteratedDeriv_two_profile (t : ℝ) (ht : 0 < t) :
    ∀ᵐ u : ℝ, iteratedDeriv 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) u
      = (if t * Real.exp (-u) < 2 then
          (32 * (t * Real.exp (-u)) ^ 2 - 68 * (t * Real.exp (-u)) ^ 3
            + 20 * (t * Real.exp (-u)) ^ 4 + 17 * (t * Real.exp (-u)) ^ 5
            - 5 * (t * Real.exp (-u)) ^ 6 - (t * Real.exp (-u)) ^ 7)
          * Real.exp (t * Real.exp (-u) - 1/2)
        else 0) := by
  have hne2 : ∀ᵐ u : ℝ, t * Real.exp (-u) ≠ 2 := by
    rw [MeasureTheory.ae_iff]
    have hsub : {u : ℝ | ¬ t * Real.exp (-u) ≠ 2} ⊆ {Real.log (t / 2)} := by
      intro u hu
      simp only [Set.mem_setOf_eq, not_not] at hu
      simp only [Set.mem_singleton_iff]
      have h1 : Real.exp (-u) = 2 / t := by
        rw [eq_div_iff ht.ne', mul_comm]
        exact hu
      have h2 : -u = Real.log (2 / t) := by rw [← h1, Real.log_exp]
      have h3 : Real.log (2 / t) = Real.log 2 - Real.log t := Real.log_div (by norm_num) ht.ne'
      have h4 : Real.log (t / 2) = Real.log t - Real.log 2 := Real.log_div ht.ne' (by norm_num)
      linarith
    exact measure_mono_null hsub (measure_singleton _)
  filter_upwards [hne2] with u hu
  rcases lt_trichotomy (t * Real.exp (-u)) 2 with h | h | h
  · rw [if_pos h, iteratedDeriv_two_profile_lt t ht h]
  · exact absurd h hu
  · rw [if_neg (by linarith), iteratedDeriv_two_profile_gt t h]

/-- The `L¹` norm of the second derivative of the profile. -/
theorem norm_iteratedDeriv_two_le (t : ℝ) (ht : 0 < t) :
    ∫ u : ℝ, ‖iteratedDeriv 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) u‖
      ≤ 40 := by
  -- rewrite the integrand, then substitute `y = t e^{-u}`
  have h1 : ∫ u : ℝ, ‖iteratedDeriv 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) u‖
      = ∫ u : ℝ, ‖(if t * Real.exp (-u) < 2 then
          (32 * (t * Real.exp (-u)) ^ 2 - 68 * (t * Real.exp (-u)) ^ 3
            + 20 * (t * Real.exp (-u)) ^ 4 + 17 * (t * Real.exp (-u)) ^ 5
            - 5 * (t * Real.exp (-u)) ^ 6 - (t * Real.exp (-u)) ^ 7)
          * Real.exp (t * Real.exp (-u) - 1/2)
        else 0)‖ := by
    apply integral_congr_ae
    filter_upwards [ae_iteratedDeriv_two_profile t ht] with u hu
    rw [hu]
  rw [h1, integral_exp_comp t ht
    (fun y : ℝ => ‖(if y < 2 then
      (32 * y ^ 2 - 68 * y ^ 3 + 20 * y ^ 4 + 17 * y ^ 5 - 5 * y ^ 6 - y ^ 7)
      * Real.exp (y - 1/2) else 0)‖)]
  -- pass to the interval `(0,2)`
  have h2 : ∫ y in Set.Ioi (0:ℝ), ‖(if y < 2 then
        (32 * y ^ 2 - 68 * y ^ 3 + 20 * y ^ 4 + 17 * y ^ 5 - 5 * y ^ 6 - y ^ 7)
        * Real.exp (y - 1/2) else 0)‖ / y
      = ∫ y in (0:ℝ)..2, ‖(if y < 2 then
        (32 * y ^ 2 - 68 * y ^ 3 + 20 * y ^ 4 + 17 * y ^ 5 - 5 * y ^ 6 - y ^ 7)
        * Real.exp (y - 1/2) else 0)‖ / y := by
    rw [← MeasureTheory.integral_indicator (μ := volume) measurableSet_Ioi,
      intervalIntegral.integral_of_le (μ := volume) (a := (0:ℝ)) (b := 2) (by norm_num),
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← MeasureTheory.integral_indicator (μ := volume) measurableSet_Ioo]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    by_cases hy : y ∈ Set.Ioi (0:ℝ)
    · by_cases h2' : y < 2
      · have hy2 : y ∈ Set.Ioo (0:ℝ) 2 := ⟨hy, h2'⟩
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy2]
      · have hy2 : y ∉ Set.Ioo (0:ℝ) 2 := fun h => h2' h.2
        rw [Set.indicator_of_mem hy, Set.indicator_of_notMem hy2]
        have hpos : (0:ℝ) < y := hy
        rw [if_neg (by linarith), norm_zero, zero_div]
    · rw [Set.indicator_of_notMem hy]
      have hy2 : y ∉ Set.Ioo (0:ℝ) 2 := by
        intro h
        exact hy h.1
      rw [Set.indicator_of_notMem hy2]
  rw [h2]
  -- compare with a continuous majorant
  have h3 : ∫ y in (0:ℝ)..2, ‖(if y < 2 then
        (32 * y ^ 2 - 68 * y ^ 3 + 20 * y ^ 4 + 17 * y ^ 5 - 5 * y ^ 6 - y ^ 7)
        * Real.exp (y - 1/2) else 0)‖ / y
      = ∫ y in (0:ℝ)..2,
        |32 * y - 68 * y ^ 2 + 20 * y ^ 3 + 17 * y ^ 4 - 5 * y ^ 5 - y ^ 6|
          * Real.exp (y - 1/2) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hy
    have hy0 : (0:ℝ) < y := hy.1
    by_cases h2' : y < 2
    · rw [if_pos h2']
      have hQ : (32 * y ^ 2 - 68 * y ^ 3 + 20 * y ^ 4 + 17 * y ^ 5 - 5 * y ^ 6 - y ^ 7 : ℝ)
          = y * (32 * y - 68 * y ^ 2 + 20 * y ^ 3 + 17 * y ^ 4 - 5 * y ^ 5 - y ^ 6) := by ring
      rw [hQ, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hy0,
        abs_of_pos (Real.exp_pos _), mul_assoc, mul_div_cancel_left₀ _ hy0.ne']
    · have hy2 : y = 2 := le_antisymm hy.2 (le_of_not_gt h2')
      subst hy2
      rw [if_neg (by norm_num : ¬ (2:ℝ) < 2)]
      norm_num
  rw [h3]
  -- the explicit numerical bound
  have hfi : IntervalIntegrable
      (fun y : ℝ => |32 * y - 68 * y ^ 2 + 20 * y ^ 3 + 17 * y ^ 4 - 5 * y ^ 5 - y ^ 6|
        * Real.exp (y - 1/2)) volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hgi : IntervalIntegrable (fun y : ℝ => (103 / 10) * Real.exp (y - 1/2)) volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h4 : ∫ y in (0:ℝ)..2,
        |32 * y - 68 * y ^ 2 + 20 * y ^ 3 + 17 * y ^ 4 - 5 * y ^ 5 - y ^ 6|
          * Real.exp (y - 1/2)
      ≤ ∫ y in (0:ℝ)..2, (103 / 10) * Real.exp (y - 1/2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (a := (0:ℝ)) (b := 2)
      (f := fun y : ℝ => |32 * y - 68 * y ^ 2 + 20 * y ^ 3 + 17 * y ^ 4 - 5 * y ^ 5 - y ^ 6|
        * Real.exp (y - 1/2))
      (g := fun y : ℝ => (103 / 10) * Real.exp (y - 1/2))
      (by norm_num) hfi hgi ?_
    intro y hy
    have hle := abs_R_le hy.1.le hy.2.le
    have hle' : |32 * y - 68 * y ^ 2 + 20 * y ^ 3 + 17 * y ^ 4 - 5 * y ^ 5 - y ^ 6| ≤ (103/10) := by
      convert hle using 2 <;> ring
    have he : (0:ℝ) < Real.exp (y - 1/2) := Real.exp_pos _
    exact mul_le_mul_of_nonneg_right hle' he.le
  have h5 : ∫ y in (0:ℝ)..2, (103 / 10) * Real.exp (y - 1/2)
      = (103 / 10) * (Real.exp (3/2) - Real.exp (-(1/2))) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => Real.exp (y - 1/2))
      (fun y _ => by
        have h := (Real.hasDerivAt_exp (y - 1/2)).comp y ((hasDerivAt_id y).sub_const (1/2))
        simpa [Function.comp_def] using h)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    norm_num
  have h6 : (103 / 10) * (Real.exp (3/2) - Real.exp (-(1/2))) ≤ 40 := by
    have h32 : Real.exp (3/2) ≤ 4.4817 := by
      have hsq : Real.exp (3/2) ^ 2 = Real.exp 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      have h4' : Real.exp 3 = (Real.exp 1) ^ 3 := by
        rw [show (3:ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; ring
      have hlt := Real.exp_one_lt_d9
      have h0 : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
      have h5' : (Real.exp 1) ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ h0 hlt.le 3
      have h7 : Real.exp 3 ≤ 20.0856 := by rw [h4']; norm_num at h5' ⊢; linarith
      nlinarith [Real.exp_pos (3/2), hsq]
    have hm : (0.6065 : ℝ) ≤ Real.exp (-(1/2)) := by
      have hsq : Real.exp (-(1/2)) * Real.exp (1/2) = 1 := by
        rw [← Real.exp_add]; norm_num
      have hlt := Real.exp_one_lt_d9
      have h0 : (0:ℝ) ≤ Real.exp (1/2) := (Real.exp_pos _).le
      have hsq2 : Real.exp (1/2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hu : Real.exp (1/2) ≤ 1.6488 := by
        nlinarith [Real.exp_pos (1/2), hsq2]
      nlinarith [Real.exp_pos (-(1/2)), hsq]
    linarith
  linarith

/-! ### The Dirichlet kernel as a logarithmic convolution (ported) -/

open MeasureTheory

/-- On the positive half line the sine kernel is the Dirichlet kernel in the `log` variable. -/
private theorem FH_exp_eq (H : ℝ) {u : ℝ} (hu : u ≠ 0) :
    LeanLab.HelfgottArcs.FH H (Real.exp u) = Real.sin (H * u) / (Real.pi * u) := by
  unfold LeanLab.HelfgottArcs.FH
  rw [Real.log_exp]

/-- The Dirichlet kernel `sin (H u) / (pi u)` is an even function. -/
private theorem dirichlet_kernel_even (u : ℝ) :
    Real.sin (200 * (-u)) / (Real.pi * (-u)) = Real.sin (200 * u) / (Real.pi * u) := by
  rw [show (200 : ℝ) * (-u) = -(200 * u) by ring, Real.sin_neg,
    show Real.pi * (-u) = -(Real.pi * u) by ring, neg_div_neg_eq]

/-- The multiplicative convolution with the sine kernel is the Dirichlet integral of the
weight in the logarithm variable. -/
private theorem mconv_hfun_eq_dirichlet (t : ℝ) (ht : 0 < t) :
    LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun (LeanLab.HelfgottArcs.FH 200) t
      = ∫ u : ℝ, LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) *
          (Real.sin (200 * u) / (Real.pi * u)) := by
  have himg : (fun u : ℝ => t * Real.exp (-u)) '' Set.univ = Set.Ioi 0 := by
    ext y
    constructor
    · rintro ⟨u, -, rfl⟩
      exact mul_pos ht (Real.exp_pos _)
    · intro hy
      refine ⟨-Real.log (y / t), Set.mem_univ _, ?_⟩
      have hy' : 0 < y / t := div_pos hy ht
      have hexp : Real.exp (-(-Real.log (y / t))) = y / t := by
        rw [neg_neg, Real.exp_log hy']
      calc t * Real.exp (-(-Real.log (y / t))) = t * (y / t) := by rw [hexp]
        _ = y := by field_simp
  have hinj : Set.InjOn (fun u : ℝ => t * Real.exp (-u)) Set.univ := by
    intro u1 _ u2 _ h
    have h1 : Real.exp (-u1) = Real.exp (-u2) := mul_left_cancel₀ ht.ne' h
    have h2 := Real.exp_injective h1
    linarith
  have hderiv : ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun u : ℝ => t * Real.exp (-u)) (-t * Real.exp (-u)) Set.univ u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) u := by
      have h := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun u : ℝ => t * Real.exp (-u)) (t * -Real.exp (-u)) u :=
      h1.const_mul t
    have h3 : t * -Real.exp (-u) = -t * Real.exp (-u) := by ring
    rw [← h3]
    exact h2.hasDerivWithinAt
  have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun u : ℝ => t * Real.exp (-u)) (f' := fun u : ℝ => -t * Real.exp (-u))
    (s := Set.univ) MeasurableSet.univ hderiv hinj
    (g := fun y : ℝ => LeanLab.HelfgottArcs.hfun y * LeanLab.HelfgottArcs.FH 200 (t / y) / y)
  rw [himg, setIntegral_univ] at hsub
  have h0ae : ∀ᵐ u : ℝ, u ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hne : ∀ u : ℝ, t * Real.exp (-u) ≠ 0 := fun u =>
    ne_of_gt (by positivity)
  have habs : ∀ u : ℝ, |(-t) * Real.exp (-u)| = t * Real.exp (-u) := by
    intro u
    rw [abs_mul, abs_neg, abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
  have harg : ∀ u : ℝ, t / (t * Real.exp (-u)) = Real.exp u := by
    intro u
    have h2 : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [div_eq_iff (hne u),
      show Real.exp u * (t * Real.exp (-u)) = t * (Real.exp u * Real.exp (-u)) by ring, h2,
      mul_one]
  refine hsub.trans ?_
  refine integral_congr_ae ?_
  filter_upwards [h0ae] with u hu
  show |(-t) * Real.exp (-u)| • (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) *
      LeanLab.HelfgottArcs.FH 200 (t / (t * Real.exp (-u))) / (t * Real.exp (-u)))
    = LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) * (Real.sin (200 * u) / (Real.pi * u))
  rw [habs u, harg u, smul_eq_mul, FH_exp_eq 200 hu]
  field_simp

/-- The Dirichlet kernel is even, so reflecting the weight does not change the integral. -/
private theorem dirichlet_reflect (t : ℝ) :
    (∫ u : ℝ, LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) *
        (Real.sin (200 * u) / (Real.pi * u)))
      = ∫ u : ℝ, LeanLab.HelfgottArcs.hfun (t * Real.exp u) *
          (Real.sin (200 * u) / (Real.pi * u)) := by
  rw [← MeasureTheory.integral_neg_eq_self
    (f := fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp u) *
      (Real.sin (200 * u) / (Real.pi * u)))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  show LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) *
      (Real.sin (200 * u) / (Real.pi * u))
    = LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) *
      (Real.sin (200 * (-u)) / (Real.pi * (-u)))
  rw [dirichlet_kernel_even]



/-- `deriv` commutes with the coercion to `ℂ`. -/
theorem deriv_ofReal_comp (h : ℝ → ℝ) (u : ℝ) :
    deriv (fun y : ℝ => (h y : ℂ)) u = ((deriv h u : ℝ) : ℂ) := by
  by_cases hu : DifferentiableAt ℝ h u
  · have h1 : HasDerivAt h (deriv h u) u := hu.hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => (h y : ℂ)) ((deriv h u : ℝ) : ℂ) u := h1.ofReal_comp
    rw [h2.deriv]
  · have h0 : deriv h u = 0 := deriv_zero_of_not_differentiableAt hu
    have h1 : deriv (fun y : ℝ => (h y : ℂ)) u = 0 := by
      apply deriv_zero_of_not_differentiableAt
      intro hd
      refine hu ?_
      have h4 : DifferentiableAt ℝ (fun y : ℝ => Complex.reCLM ((h y : ℂ))) u :=
        DifferentiableAt.comp u Complex.reCLM.differentiableAt hd
      simpa using h4
    rw [h0, h1]
    simp

/-- `iteratedDeriv` commutes with the coercion to `ℂ`. -/
theorem iteratedDeriv_ofReal_comp (n : ℕ) (h : ℝ → ℝ) (u : ℝ) :
    iteratedDeriv n (fun y : ℝ => (h y : ℂ)) u = ((iteratedDeriv n h u : ℝ) : ℂ) := by
  induction n generalizing u with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    have hfun : iteratedDeriv k (fun y : ℝ => (h y : ℂ))
        = fun y : ℝ => ((iteratedDeriv k h y : ℝ) : ℂ) := funext ih
    rw [iteratedDeriv_succ, iteratedDeriv_succ, hfun, deriv_ofReal_comp]

/-- The Dirichlet kernel as an integral of cosines. -/
theorem cos_kernel_eq {u : ℝ} (hu : u ≠ 0) :
    Real.sin (200 * u) / (Real.pi * u)
      = ∫ ξ in (-(100/Real.pi))..(100/Real.pi), Real.cos (2 * Real.pi * ξ * u) := by
  have hcongr : (fun ξ : ℝ => Real.cos (2 * Real.pi * ξ * u))
      = fun ξ : ℝ => Real.cos ((2 * Real.pi * u) * ξ) := by
    funext ξ
    rw [show 2 * Real.pi * ξ * u = (2 * Real.pi * u) * ξ by ring]
  rw [hcongr]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hc : (2 * Real.pi * u) ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact hpi h2
    · exact hu h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun ξ : ℝ => Real.sin ((2*Real.pi*u)*ξ) / (2*Real.pi*u))
    (f' := fun ξ : ℝ => Real.cos ((2*Real.pi*u)*ξ))
    (fun ξ _ => by
      have h1 : HasDerivAt (fun x : ℝ => Real.sin ((2*Real.pi*u) * x))
          (Real.cos ((2*Real.pi*u)*ξ) * (2*Real.pi*u)) ξ := by
        have h0 := (Real.hasDerivAt_sin ((2*Real.pi*u)*ξ)).comp ξ
          ((hasDerivAt_id ξ).const_mul (2*Real.pi*u))
        simpa [Function.comp_def, mul_comm] using h0
      have h2 := h1.div_const (2*Real.pi*u)
      have hval : Real.cos ((2*Real.pi*u)*ξ) * (2*Real.pi*u) / (2*Real.pi*u)
          = Real.cos ((2*Real.pi*u)*ξ) := by
        field_simp
      rw [hval] at h2
      exact h2)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have h1 : (2*Real.pi*u) * (100/Real.pi) = 200*u := by
    field_simp
    norm_num
  have h2 : (2*Real.pi*u) * (-(100/Real.pi)) = -(200*u) := by
    field_simp
    norm_num
  rw [h1, h2, Real.sin_neg]
  field_simp
  ring

/-- The profile is `C²`. -/
theorem contDiff_profile (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) := by
  have h : (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)))
      = fun u : ℝ => (max (2 - t * Real.exp (-u)) 0) ^ 3
          * ((t * Real.exp (-u)) ^ 2 * Real.exp (t * Real.exp (-u) - 1/2)) := by
    funext u
    exact hfun_eq_of_pos (by positivity)
  rw [h]
  exact contDiff_max_cube.comp (by fun_prop) |>.mul (by fun_prop)

/-- `t e^{-u} ≤ 2` above the threshold. -/
theorem y_le_two {t u : ℝ} (ht : 0 < t) (hu : Real.log (t/2) ≤ u) :
    t * Real.exp (-u) ≤ 2 := by
  have h2 : Real.exp u ≥ t/2 := by
    have := Real.exp_le_exp_of_le hu
    rwa [Real.exp_log (by positivity)] at this
  have h4 : (Real.exp u)⁻¹ ≤ (t/2)⁻¹ := inv_anti₀ (by positivity) h2
  rw [Real.exp_neg]
  calc t * (Real.exp u)⁻¹ ≤ t * (t/2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left h4 ht.le
    _ = 2 := by field_simp

/-- `2 ≤ t e^{-u}` below the threshold. -/
theorem two_le_y {t u : ℝ} (ht : 0 < t) (hu : u ≤ Real.log (t/2)) :
    2 ≤ t * Real.exp (-u) := by
  have h2 : Real.exp u ≤ t/2 := by
    have := Real.exp_le_exp_of_le hu
    rwa [Real.exp_log (by positivity)] at this
  have h4 : (t/2)⁻¹ ≤ (Real.exp u)⁻¹ := inv_anti₀ (Real.exp_pos u) h2
  rw [Real.exp_neg]
  calc (2:ℝ) = t * (t/2)⁻¹ := by field_simp
    _ ≤ t * (Real.exp u)⁻¹ := by
        apply mul_le_mul_of_nonneg_left h4 ht.le

/-- `t e^{-u} < 2` strictly above the threshold. -/
theorem y_lt_two {t u : ℝ} (ht : 0 < t) (hu : Real.log (t/2) < u) :
    t * Real.exp (-u) < 2 := by
  have h2 : Real.exp u > t/2 := by
    have := Real.exp_lt_exp.mpr hu
    rwa [Real.exp_log (by positivity)] at this
  have h4 : (Real.exp u)⁻¹ < (t/2)⁻¹ := inv_strictAnti₀ (by positivity) h2
  rw [Real.exp_neg]
  calc t * (Real.exp u)⁻¹ < t * (t/2)⁻¹ := mul_lt_mul_of_pos_left h4 ht
    _ = 2 := by field_simp

/-- `2 < t e^{-u}` strictly below the threshold. -/
theorem two_lt_y {t u : ℝ} (ht : 0 < t) (hu : u < Real.log (t/2)) :
    2 < t * Real.exp (-u) := by
  have h2 : Real.exp u < t/2 := by
    have := Real.exp_lt_exp.mpr hu
    rwa [Real.exp_log (by positivity)] at this
  have h4 : (t/2)⁻¹ < (Real.exp u)⁻¹ := inv_strictAnti₀ (Real.exp_pos u) h2
  rw [Real.exp_neg]
  calc (2:ℝ) = t * (t/2)⁻¹ := by field_simp
    _ < t * (Real.exp u)⁻¹ := mul_lt_mul_of_pos_left h4 ht

/-- `e^{3/2} ≤ 5`. -/
theorem exp_three_halves_le : Real.exp (3/2) ≤ 5 := by
  have hexp2 : Real.exp (3/2) = Real.exp 1 * Real.exp (1/2) := by
    rw [← Real.exp_add]; norm_num
  have hsq : Real.exp (1/2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hu : Real.exp (1/2) ≤ 1.6488 := by
    nlinarith [Real.exp_pos (1/2), hsq, Real.exp_one_lt_d9]
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h0 : (0:ℝ) < Real.exp (1/2) := Real.exp_pos _
  nlinarith [hu, h1, h0]

/-- Integrability of the profile. -/
theorem integrable_profile (t : ℝ) (ht : 0 < t) :
    Integrable (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) := by
  have hcont : Continuous (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) :=
    (contDiff_profile t ht).continuous
  refine integrable_of_decay (Real.log (t/2)) (288 * t) (by nlinarith [ht]) hcont.aestronglyMeasurable
    ?_ ?_
  · -- vanishing above two
    intro u hu
    have hy : 2 < t * Real.exp (-u) := two_lt_y ht hu
    rw [LeanLab.HelfgottArcs.hfun, if_neg (by rintro ⟨_, h2'⟩; linarith)]
  · -- decay
    intro u hu
    have hy2 : t * Real.exp (-u) ≤ 2 := (y_lt_two ht hu).le
    have hy0 : (0:ℝ) ≤ t * Real.exp (-u) := by positivity
    have hb := norm_hfun_le hy0 hy2
    have hle : (t * Real.exp (-u)) ^ 2 ≤ 2 * t * Real.exp (-u) := by
      nlinarith [hy2, Real.exp_pos (-u)]
    calc ‖LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))‖ ≤ 144 * (t * Real.exp (-u)) ^ 2 := hb
      _ ≤ 144 * (2 * t * Real.exp (-u)) := by linarith
      _ = 288 * t * Real.exp (-u) := by ring


/-- The first derivative of the profile vanishes above two. -/
theorem deriv_profile_gt (t : ℝ) {u : ℝ} (h2 : 2 < t * Real.exp (-u)) :
    deriv (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) u = 0 := by
  have hev : deriv (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) =ᶠ[𝓝 u] 0 := by
    have h := (profile_eq_zero_of_gt t h2).deriv
    simpa using h
  exact hev.eq_of_nhds

/-- Crude bound on the polynomial factor of the first derivative. -/
theorem abs_A_le {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    |(-16 * y ^ 2 + 28 * y ^ 3 - 12 * y ^ 4 - y ^ 5 + y ^ 6 : ℝ)| ≤ 145 * y ^ 2 := by
  have h1 : y ^ 2 ≤ 4 := by nlinarith
  have h2 : y ^ 3 ≤ 8 := by nlinarith
  have h3 : y ^ 4 ≤ 16 := by nlinarith
  have h4 : y ^ 5 ≤ 32 := by nlinarith
  have h5 : y ^ 6 ≤ 64 := by nlinarith
  have h0 : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
  have hfac : (-16 * y ^ 2 + 28 * y ^ 3 - 12 * y ^ 4 - y ^ 5 + y ^ 6 : ℝ)
      = y ^ 2 * (-16 + 28 * y - 12 * y ^ 2 - y ^ 3 + y ^ 4) := by ring
  rw [hfac, abs_mul, abs_of_nonneg h0]
  have hb : |(-16 + 28 * y - 12 * y ^ 2 - y ^ 3 + y ^ 4 : ℝ)| ≤ 144 := by
    rw [abs_le]
    constructor <;> nlinarith [hy0, hy2, sq_nonneg y, sq_nonneg (y-1), pow_nonneg hy0 3, pow_nonneg hy0 4]
  calc y ^ 2 * |(-16 + 28 * y - 12 * y ^ 2 - y ^ 3 + y ^ 4 : ℝ)| ≤ y ^ 2 * 144 := by
        apply mul_le_mul_of_nonneg_left hb h0
    _ ≤ 145 * y ^ 2 := by nlinarith


/-- Integrability of the second derivative of the profile. -/
theorem integrable_iteratedDeriv_two_profile (t : ℝ) (ht : 0 < t) :
    Integrable (iteratedDeriv 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)))) := by
  have hcd := contDiff_profile t ht
  have hcont : Continuous
      (iteratedDeriv 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)))) := by
    have h1 : ContDiff ℝ 1 (deriv (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)))) :=
      (contDiff_succ_iff_deriv.mp hcd).2.2
    have h2 : Continuous (deriv (deriv (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))))) :=
      h1.continuous_deriv (by norm_num)
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using h2
  refine integrable_of_decay (Real.log (t/2)) (52 * t) (by nlinarith [ht])
    hcont.aestronglyMeasurable ?_ ?_
  · intro u hu
    exact iteratedDeriv_two_profile_gt t (two_lt_y ht hu)
  · intro u hu
    have hstrict : t * Real.exp (-u) < 2 := y_lt_two ht hu
    have hy2 : t * Real.exp (-u) ≤ 2 := hstrict.le
    have hy0 : (0:ℝ) ≤ t * Real.exp (-u) := by positivity
    rw [iteratedDeriv_two_profile_lt t ht hstrict]
    have hexp : Real.exp (t * Real.exp (-u) - 1/2) ≤ 5 :=
      le_trans (Real.exp_le_exp_of_le (by linarith)) exp_three_halves_le
    have hQ := abs_R_le hy0 hy2
    have hQ' : |(32 * (t * Real.exp (-u)) ^ 2 - 68 * (t * Real.exp (-u)) ^ 3
          + 20 * (t * Real.exp (-u)) ^ 4 + 17 * (t * Real.exp (-u)) ^ 5
          - 5 * (t * Real.exp (-u)) ^ 6 - (t * Real.exp (-u)) ^ 7 : ℝ)|
        ≤ (103 / 10) * (t * Real.exp (-u)) := by
      have hfac : (32 * (t * Real.exp (-u)) ^ 2 - 68 * (t * Real.exp (-u)) ^ 3
          + 20 * (t * Real.exp (-u)) ^ 4 + 17 * (t * Real.exp (-u)) ^ 5
          - 5 * (t * Real.exp (-u)) ^ 6 - (t * Real.exp (-u)) ^ 7 : ℝ)
          = (t * Real.exp (-u)) * (32 * (t * Real.exp (-u)) - 68 * (t * Real.exp (-u)) ^ 2
            + 20 * (t * Real.exp (-u)) ^ 3 + 17 * (t * Real.exp (-u)) ^ 4
            - 5 * (t * Real.exp (-u)) ^ 5 - (t * Real.exp (-u)) ^ 6) := by ring
      rw [hfac, abs_mul, abs_of_nonneg hy0]
      have := abs_R_le hy0 hy2
      have hle' : |32 * (t * Real.exp (-u)) - 68 * (t * Real.exp (-u)) ^ 2
          + 20 * (t * Real.exp (-u)) ^ 3 + 17 * (t * Real.exp (-u)) ^ 4
          - 5 * (t * Real.exp (-u)) ^ 5 - (t * Real.exp (-u)) ^ 6| ≤ (103/10) := by
        convert this using 2 <;> ring
      calc (t * Real.exp (-u)) * |32 * (t * Real.exp (-u)) - 68 * (t * Real.exp (-u)) ^ 2
            + 20 * (t * Real.exp (-u)) ^ 3 + 17 * (t * Real.exp (-u)) ^ 4
            - 5 * (t * Real.exp (-u)) ^ 5 - (t * Real.exp (-u)) ^ 6|
          ≤ (t * Real.exp (-u)) * (103/10) := by
            apply mul_le_mul_of_nonneg_left hle' hy0
        _ = (103 / 10) * (t * Real.exp (-u)) := by ring
    have hres := mul_le_mul hQ' hexp (Real.exp_pos _).le (by positivity : (0:ℝ) ≤ (103/10) * (t * Real.exp (-u)))
    calc ‖(32 * (t * Real.exp (-u)) ^ 2 - 68 * (t * Real.exp (-u)) ^ 3
          + 20 * (t * Real.exp (-u)) ^ 4 + 17 * (t * Real.exp (-u)) ^ 5
          - 5 * (t * Real.exp (-u)) ^ 6 - (t * Real.exp (-u)) ^ 7)
          * Real.exp (t * Real.exp (-u) - 1/2)‖
        = |(32 * (t * Real.exp (-u)) ^ 2 - 68 * (t * Real.exp (-u)) ^ 3
          + 20 * (t * Real.exp (-u)) ^ 4 + 17 * (t * Real.exp (-u)) ^ 5
          - 5 * (t * Real.exp (-u)) ^ 6 - (t * Real.exp (-u)) ^ 7 : ℝ)| * Real.exp (t * Real.exp (-u) - 1/2) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ ((103 / 10) * (t * Real.exp (-u))) * 5 := hres
      _ = (103 / 2) * t * Real.exp (-u) := by ring
      _ ≤ 52 * t * Real.exp (-u) := by
          have hexp : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
          nlinarith [hexp, ht]

/-- Integrability of the first derivative of the profile. -/
theorem integrable_deriv_profile (t : ℝ) (ht : 0 < t) :
    Integrable (deriv (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)))) := by
  have hcd := contDiff_profile t ht
  have hcont : Continuous (deriv (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)))) :=
    hcd.continuous_deriv (by norm_num)
  refine integrable_of_decay (Real.log (t/2)) (1450 * t) (by nlinarith [ht])
    hcont.aestronglyMeasurable ?_ ?_
  · intro u hu
    exact deriv_profile_gt t (two_lt_y ht hu)
  · intro u hu
    have hstrict : t * Real.exp (-u) < 2 := y_lt_two ht hu
    have hy2 : t * Real.exp (-u) ≤ 2 := hstrict.le
    have hy0 : (0:ℝ) ≤ t * Real.exp (-u) := by positivity
    rw [deriv_profile_lt t ht hstrict]
    have hexp : Real.exp (t * Real.exp (-u) - 1/2) ≤ 5 :=
      le_trans (Real.exp_le_exp_of_le (by linarith)) exp_three_halves_le
    have hpoly := abs_A_le hy0 hy2
    have hexpnn : (0:ℝ) < Real.exp (t * Real.exp (-u) - 1/2) := Real.exp_pos _
    have hres := mul_le_mul hpoly hexp hexpnn.le (by positivity : (0:ℝ) ≤ 145 * (t * Real.exp (-u)) ^ 2)
    calc ‖(-16 * (t * Real.exp (-u)) ^ 2 + 28 * (t * Real.exp (-u)) ^ 3
        - 12 * (t * Real.exp (-u)) ^ 4 - (t * Real.exp (-u)) ^ 5
        + (t * Real.exp (-u)) ^ 6) * Real.exp (t * Real.exp (-u) - 1/2)‖
        = |(-16 * (t * Real.exp (-u)) ^ 2 + 28 * (t * Real.exp (-u)) ^ 3
        - 12 * (t * Real.exp (-u)) ^ 4 - (t * Real.exp (-u)) ^ 5
        + (t * Real.exp (-u)) ^ 6 : ℝ)| * Real.exp (t * Real.exp (-u) - 1/2) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ (145 * (t * Real.exp (-u)) ^ 2) * 5 := hres
      _ ≤ 1450 * t * Real.exp (-u) := by
          have hexp : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
          have hsq : (t * Real.exp (-u)) ^ 2 ≤ 2 * t * Real.exp (-u) := by
            nlinarith [hstrict.le, hexp]
          nlinarith [hsq, hexp, ht]

/-- Quadratic decay of the Fourier transform of the profile. -/
theorem fourier_decay (t : ℝ) (ht : 0 < t) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 (fun u : ℝ => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ)) ξ‖
      ≤ 40 / (4 * Real.pi ^ 2 * ξ ^ 2) := by
  have hcd := contDiff_profile t ht
  set F : ℝ → ℂ := fun u => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ) with hF
  have hcdC : ContDiff ℝ 2 F := by
    rw [hF]
    exact Complex.ofRealCLM.contDiff.comp hcd
  have hiter : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (iteratedDeriv n F) := by
    intro n hn
    have hEq : iteratedDeriv n F
        = fun u => ((iteratedDeriv n (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) u : ℝ) : ℂ) := by
      rw [hF]
      exact funext (fun u => iteratedDeriv_ofReal_comp n _ u)
    rw [hEq]
    refine Complex.ofRealCLM.integrable_comp ?_
    have hn' : n ≤ 2 := by exact_mod_cast hn
    interval_cases n
    · simpa using integrable_profile t ht
    · simpa using integrable_deriv_profile t ht
    · show Integrable (iteratedDeriv 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))))
      exact integrable_iteratedDeriv_two_profile t ht
  have hf := Real.fourier_iteratedDeriv (f := F) (N := 2) (n := 2) hcdC hiter le_rfl
  have hnorm : ‖𝓕 (iteratedDeriv 2 F) ξ‖
      = (2 * Real.pi * |ξ|) ^ 2 * ‖𝓕 F ξ‖ := by
    rw [hf]
    simp only [Pi.smul_apply]
    rw [norm_smul, norm_pow]
    have h1 : ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))‖ = 2 * Real.pi * |ξ| := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [h1]
  have hdecay : ‖𝓕 (iteratedDeriv 2 F) ξ‖ ≤ ∫ u : ℝ, ‖iteratedDeriv 2 F u‖ := by
    rw [Real.fourier_eq']
    have h := MeasureTheory.norm_integral_le_integral_norm (μ := volume)
      (fun v : ℝ => Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) • iteratedDeriv 2 F v)
    simpa [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Real.exp_zero, one_mul] using h
  have hbound : ∫ u : ℝ, ‖iteratedDeriv 2 F u‖ ≤ 40 := by
    have hEq : (fun u : ℝ => ‖iteratedDeriv 2 F u‖)
        = fun u : ℝ => ‖iteratedDeriv 2 (fun u : ℝ => LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))) u‖ := by
      funext u
      rw [hF, iteratedDeriv_ofReal_comp]
      exact Complex.norm_real _
    rw [hEq]
    exact norm_iteratedDeriv_two_le t ht
  have hpos : (0:ℝ) < (2 * Real.pi * |ξ|) ^ 2 := by
    have : (0:ℝ) < |ξ| := abs_pos.mpr hξ
    positivity
  have hkey : (2 * Real.pi * |ξ|) ^ 2 * ‖𝓕 F ξ‖ ≤ 40 := by
    rw [← hnorm]
    exact le_trans hdecay hbound
  have hxi2 : (2 * Real.pi * |ξ|) ^ 2 = 4 * Real.pi ^ 2 * ξ ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
    ring
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * Real.pi ^ 2 * ξ ^ 2)]
  rw [hxi2] at hkey
  linarith [hkey]

/-- The weighted profile is bounded by one. -/
theorem hfun_weight_le (t : ℝ) :
    LeanLab.HelfgottArcs.hfun t * t * Real.exp (-(t ^ 2) / 2) ≤ 1 := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [LeanLab.HelfgottArcs.hfun, if_neg (by rintro ⟨h0, _⟩; linarith), zero_mul, zero_mul]
    norm_num
  · subst h
    rw [LeanLab.HelfgottArcs.hfun, if_pos ⟨le_refl 0, by norm_num⟩]
    norm_num
  · rcases le_or_gt t 2 with h2 | h2
    · rw [LeanLab.HelfgottArcs.hfun, if_pos ⟨h.le, h2⟩]
      have h1 : t * (2 - t) ≤ 1 := by nlinarith [h, h2, sq_nonneg (t - 1)]
      have h0 : (0:ℝ) ≤ t * (2 - t) := by nlinarith [h, h2]
      have h3 : (t * (2 - t)) ^ 3 ≤ 1 := pow_le_one₀ h0 h1
      have h4 : Real.exp (t - 1/2 + -(t ^ 2) / 2) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [sq_nonneg (t - 1)]
      calc t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1/2) * t * Real.exp (-(t ^ 2) / 2)
          = (t * (2 - t)) ^ 3 * (Real.exp (t - 1/2) * Real.exp (-(t ^ 2) / 2)) := by ring
        _ = (t * (2 - t)) ^ 3 * Real.exp (t - 1/2 + -(t ^ 2) / 2) := by rw [Real.exp_add]
        _ ≤ 1 * 1 := mul_le_mul h3 h4 (Real.exp_pos _).le (by norm_num)
        _ = 1 := by norm_num
    · rw [LeanLab.HelfgottArcs.hfun, if_neg (by rintro ⟨_, h3⟩; linarith), zero_mul, zero_mul]
      norm_num

/-- The average of the profile, FROM the truncation/inversion bridge (still to be built). -/
theorem mconv_bound_of_bridge (t : ℝ) (ht : 0 < t)
    (hbridge : |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun (LeanLab.HelfgottArcs.FH 200) t|
      ≤ 1 + 40 / (200 * Real.pi)) :
    |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun (LeanLab.HelfgottArcs.FH 200) t|
      ≤ 1 + 40 / (200 * Real.pi) := hbridge

/-- The Fourier transform of the profile is integrable (quadratic decay plus a uniform bound). -/
theorem fourier_profile_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (𝓕 (fun u : ℝ => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ))) := by
  set F : ℝ → ℂ := fun u => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ) with hF
  have hFint : Integrable F := by
    rw [hF]
    exact Complex.ofRealCLM.integrable_comp (integrable_profile t ht)
  set M : ℝ := ∫ u : ℝ, ‖F u‖ with hM
  have hMnn : 0 ≤ M := integral_nonneg (fun u => norm_nonneg _)
  have hbdd : ∀ ξ : ℝ, ‖𝓕 F ξ‖ ≤ M := by
    intro ξ
    rw [Real.fourier_eq']
    have h := MeasureTheory.norm_integral_le_integral_norm (μ := volume)
      (fun v : ℝ => Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) • F v)
    simpa [hM, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Real.exp_zero, one_mul] using h
  have hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖𝓕 F ξ‖ ≤ 40 / (4 * Real.pi ^ 2 * ξ ^ 2) := by
    intro ξ hξ
    rw [hF]
    exact fourier_decay t ht hξ
  set K : ℝ := max (2 * M) (80 / (4 * Real.pi ^ 2)) with hK
  have hKnn : 0 ≤ K := le_trans (by positivity) (le_max_right _ _)
  have hdom : ∀ ξ : ℝ, ‖𝓕 F ξ‖ ≤ K / (1 + ξ ^ 2) := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have h1 : ‖𝓕 F 0‖ ≤ M := hbdd 0
      have h2 : 2 * M ≤ K := le_max_left _ _
      have h3 : K / (1 + (0:ℝ) ^ 2) = K := by norm_num
      rw [h3]
      linarith
    · by_cases h1 : ξ ^ 2 ≤ 1
      · have h3 : ‖𝓕 F ξ‖ ≤ M := hbdd ξ
        have h4 : 2 * M ≤ K := le_max_left _ _
        have hpos : (0:ℝ) < 1 + ξ ^ 2 := by positivity
        rw [le_div_iff₀ hpos]
        nlinarith
      · push_neg at h1
        have h3 : ‖𝓕 F ξ‖ ≤ 40 / (4 * Real.pi ^ 2 * ξ ^ 2) := hdec ξ hξ
        have h4 : 80 / (4 * Real.pi ^ 2) ≤ K := le_max_right _ _
        have hpi : (0:ℝ) < Real.pi := Real.pi_pos
        have hpos : (0:ℝ) < 1 + ξ ^ 2 := by positivity
        have hpos2 : (0:ℝ) < 4 * Real.pi ^ 2 * ξ ^ 2 := by positivity
        rw [le_div_iff₀ hpos]
        rw [le_div_iff₀ hpos2] at h3
        have h4' : 80 ≤ K * (4 * Real.pi ^ 2) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * Real.pi ^ 2)] at h4
          linarith [h4]
        have h6 : 40 * (1 + ξ ^ 2) ≤ K * (4 * Real.pi ^ 2 * ξ ^ 2) := by
          nlinarith [h4', h1, sq_nonneg ξ]
        have hfinal : (‖𝓕 F ξ‖ * (1 + ξ ^ 2)) * (4 * Real.pi ^ 2 * ξ ^ 2)
            ≤ K * (4 * Real.pi ^ 2 * ξ ^ 2) := by nlinarith [h3, h6]
        exact le_of_mul_le_mul_right hfinal hpos2
  have hint : Integrable (fun ξ : ℝ => K / (1 + ξ ^ 2)) := by
    have h := integrable_inv_one_add_sq
    simpa [div_eq_mul_inv] using h.const_mul K
  refine hint.mono ?_ ?_
  · have hFcont : Continuous F := by
      rw [hF]
      exact Complex.ofRealCLM.continuous.comp (contDiff_profile t ht).continuous
    have hcont : Continuous (Function.uncurry (fun (ξ v : ℝ) =>
        Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) * F v)) := by
      apply Continuous.mul
      · fun_prop
      · exact hFcont.comp continuous_snd
    have hsm := hcont.stronglyMeasurable.integral_prod_right (ν := volume)
    have hgoal : (𝓕 F) = fun ξ : ℝ =>
        ∫ v : ℝ, Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) • F v := by
      funext ξ
      rw [Real.fourier_eq']
    rw [hgoal]
    simpa [smul_eq_mul] using hsm.aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hdom ξ

/-- The cosine moment of the profile is the real part of its Fourier transform. -/
theorem cos_moment_eq_re (t : ℝ) (ht : 0 < t) (ξ : ℝ) :
    (∫ u : ℝ, LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) * Real.cos (2 * Real.pi * ξ * u))
      = (𝓕 (fun u : ℝ => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ)) ξ).re := by
  set F : ℝ → ℂ := fun u => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ) with hF
  have hFcont : Continuous F := by
    rw [hF]
    exact Complex.ofRealCLM.continuous.comp (contDiff_profile t ht).continuous
  have hFint : Integrable F := by
    rw [hF]
    exact Complex.ofRealCLM.integrable_comp (integrable_profile t ht)
  have hψ : ∀ v : ℝ, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v
      = Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) * F v := fun v => rfl
  have hInt : Integrable (fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v) := by
    have hmeas : AEStronglyMeasurable (fun v : ℝ =>
        Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v) volume :=
      (((Complex.continuous_exp.comp (by fun_prop : Continuous fun v : ℝ =>
          ↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I)).smul hFcont)).aestronglyMeasurable
    refine hFint.mono hmeas ?_
    filter_upwards with v
    rw [norm_smul, Complex.norm_exp]
    have hre : (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hre, Real.exp_zero, one_mul]
  have hstep : (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v).re
      = ∫ v : ℝ, (Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v).re :=
    (ContinuousLinearMap.integral_comp_comm (L := Complex.reCLM) hInt).symm
  rw [Real.fourier_eq', hstep]
  apply integral_congr_ae
  filter_upwards with v
  have hpt : (Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I)
        • F v).re = LeanLab.HelfgottArcs.hfun (t * Real.exp (-v)) * Real.cos (2 * Real.pi * ξ * v) := by
    rw [hψ v, Complex.exp_ofReal_mul_I, hF]
    have hin : inner ℝ v ξ = ξ * v := by
      simp [RCLike.inner_apply]
    have hθ : -2 * Real.pi * inner ℝ v ξ = -(2 * Real.pi * ξ * v) := by
      rw [hin]; ring
    rw [hθ, Real.cos_neg, Complex.mul_re]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_sin,
      Complex.sin_ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  exact hpt.symm

/-- The Dirichlet average is the truncated inverse Fourier integral. -/
theorem mconv_eq_truncated (t : ℝ) (ht : 0 < t) :
    LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun (LeanLab.HelfgottArcs.FH 200) t
      = ∫ ξ in Set.Ioc (-(100/Real.pi)) (100/Real.pi),
          (𝓕 (fun u : ℝ => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ)) ξ).re := by
  set F : ℝ → ℂ := fun u => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ) with hF
  set s : Set ℝ := Set.Ioc (-(100/Real.pi)) (100/Real.pi) with hs
  have hsmeas : MeasurableSet s := hs ▸ measurableSet_Ioc
  -- the kernel identity on `s`
  have hker : ∀ u : ℝ, u ≠ 0 → (∫ ξ in s, Real.cos (2 * Real.pi * ξ * u))
      = Real.sin (200 * u) / (Real.pi * u) := by
    intro u hu
    have hR : (0:ℝ) < 100/Real.pi := by positivity
    rw [hs, ← intervalIntegral.integral_of_le (by linarith)]
    exact (cos_kernel_eq hu).symm
  have hne : ∀ᵐ u : ℝ, u ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  -- step 1: replace the kernel
  have h1 : (∫ u : ℝ, LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))
        * (Real.sin (200 * u) / (Real.pi * u)))
      = ∫ u : ℝ, LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))
          * (∫ ξ in s, Real.cos (2 * Real.pi * ξ * u)) := by
    apply integral_congr_ae
    filter_upwards [hne] with u hu
    rw [hker u hu]
  rw [mconv_hfun_eq_dirichlet t ht, h1]
  -- step 2: Fubini
  have hfint : Integrable (Function.uncurry (fun (ξ u : ℝ) =>
      s.indicator (fun _ => (1:ℝ)) ξ
        * (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) * Real.cos (2 * Real.pi * ξ * u))))
      (volume.prod volume) := by
    have hind : Integrable (fun ξ : ℝ => s.indicator (fun _ => (1:ℝ)) ξ) := by
      rw [integrable_indicator_iff hsmeas]
      refine integrableOn_const ?_
      rw [hs]
      simp
    have hbase := hind.mul_prod (integrable_profile t ht)
    refine hbase.mono ?_ ?_
    · have hm1 : Measurable (fun p : ℝ × ℝ => s.indicator (fun _ => (1:ℝ)) p.1) :=
        (measurable_const.indicator hsmeas).comp measurable_fst
      have hm2 : Measurable (fun p : ℝ × ℝ =>
          LeanLab.HelfgottArcs.hfun (t * Real.exp (-p.2))) :=
        (contDiff_profile t ht).continuous.measurable.comp (by fun_prop)
      have hm3 : Measurable (fun p : ℝ × ℝ => Real.cos (2 * Real.pi * p.1 * p.2)) := by fun_prop
      exact (hm1.mul (hm2.mul hm3)).aestronglyMeasurable
    · filter_upwards with p
      obtain ⟨ξ, u⟩ := p
      have hcos : ‖Real.cos (2 * Real.pi * ξ * u)‖ ≤ 1 := by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      have hg : (0:ℝ) ≤ ‖LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))‖ := norm_nonneg _
      have hind : (0:ℝ) ≤ ‖s.indicator (fun _ => (1:ℝ)) ξ‖ := norm_nonneg _
      show ‖s.indicator (fun _ => (1:ℝ)) ξ
            * (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) * Real.cos (2 * Real.pi * ξ * u))‖
          ≤ ‖s.indicator (fun _ => (1:ℝ)) ξ * LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))‖
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖s.indicator (fun _ => (1:ℝ)) ξ‖
              * (‖LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))‖ * ‖Real.cos (2 * Real.pi * ξ * u)‖)
          ≤ ‖s.indicator (fun _ => (1:ℝ)) ξ‖ * (‖LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))‖ * 1) := by
            apply mul_le_mul_of_nonneg_left _ hind
            exact mul_le_mul_of_nonneg_left hcos hg
        _ = ‖s.indicator (fun _ => (1:ℝ)) ξ‖ * ‖LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))‖ := by ring
  have hswap := MeasureTheory.integral_integral_swap (μ := volume) (ν := volume) hfint
  -- identify the two sides
  have hL : (∫ ξ in s, ∫ u : ℝ, LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))
        * Real.cos (2 * Real.pi * ξ * u))
      = ∫ ξ : ℝ, ∫ u : ℝ, s.indicator (fun _ => (1:ℝ)) ξ
          * (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) * Real.cos (2 * Real.pi * ξ * u)) := by
    rw [← MeasureTheory.integral_indicator hsmeas (f := fun ξ : ℝ => ∫ u : ℝ,
      LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) * Real.cos (2 * Real.pi * ξ * u))]
    apply integral_congr_ae
    filter_upwards with ξ
    by_cases hξ : ξ ∈ s
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
      simp
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]
      simp
  have hR : (∫ u : ℝ, LeanLab.HelfgottArcs.hfun (t * Real.exp (-u))
        * (∫ ξ in s, Real.cos (2 * Real.pi * ξ * u)))
      = ∫ u : ℝ, ∫ ξ : ℝ, s.indicator (fun _ => (1:ℝ)) ξ
          * (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) * Real.cos (2 * Real.pi * ξ * u)) := by
    apply integral_congr_ae
    filter_upwards with u
    rw [← MeasureTheory.integral_indicator hsmeas (f := fun ξ : ℝ => Real.cos (2 * Real.pi * ξ * u))]
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    by_cases hξ : ξ ∈ s
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]; ring
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]; ring
  rw [hR, ← hswap, ← hL]
  -- step 3: identify the inner integral with the real part of the Fourier transform
  apply setIntegral_congr_fun hsmeas
  intro ξ _
  exact cos_moment_eq_re t ht ξ

/-- Inversion at the origin: the profile is the integral of the real part of its transform. -/
theorem profile_eq_integral_re (t : ℝ) (ht : 0 < t) :
    LeanLab.HelfgottArcs.hfun t
      = ∫ ξ : ℝ, (𝓕 (fun u : ℝ => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ)) ξ).re := by
  set F : ℝ → ℂ := fun u => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ) with hF
  have hFint : Integrable F := by
    rw [hF]
    exact Complex.ofRealCLM.integrable_comp (integrable_profile t ht)
  have hFfour : Integrable (𝓕 F) := by
    rw [hF]
    exact fourier_profile_integrable t ht
  have hcontF : ContinuousAt F 0 := by
    rw [hF]
    exact (Complex.ofRealCLM.continuous.comp (contDiff_profile t ht).continuous).continuousAt
  have hinv := MeasureTheory.Integrable.fourierInv_fourier_eq hFint hFfour hcontF
  have h1 : (∫ ξ : ℝ, 𝓕 F ξ) = F 0 := by
    rw [Real.fourierInv_eq] at hinv
    simpa using hinv
  have h2 : (∫ ξ : ℝ, 𝓕 F ξ).re = ∫ ξ : ℝ, (𝓕 F ξ).re :=
    (ContinuousLinearMap.integral_comp_comm (L := Complex.reCLM) hFfour).symm
  have h3 : (F 0).re = LeanLab.HelfgottArcs.hfun t := by
    rw [hF]
    simp
  rw [← h3, ← h2, h1]

/-- `∫_{R}^{∞} ξ^{-2} = 1/R`. -/
theorem integral_Ioi_inv_sq {R : ℝ} (hR : 0 < R) :
    ∫ ξ in Set.Ioi R, (ξ ^ 2)⁻¹ = 1 / R := by
  have hcongr : ∀ ξ ∈ Set.Ioi R, (ξ ^ 2)⁻¹ = ξ ^ (-2:ℝ) := by
    intro ξ hξ
    have h0 : (0:ℝ) < ξ := hR.trans hξ
    rw [show (-2:ℝ) = -((2:ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt h0), Real.rpow_natCast]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hR]
  have h1 : (-2:ℝ) + 1 = -1 := by norm_num
  rw [h1, Real.rpow_neg_one]
  field_simp

/-- The `L¹` mass of the Fourier transform outside the truncation. -/
theorem tail_le (t : ℝ) (ht : 0 < t) :
    ∫ ξ in (Set.Ioc (-(100/Real.pi)) (100/Real.pi))ᶜ,
        ‖𝓕 (fun u : ℝ => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ)) ξ‖
      ≤ 40 / (200 * Real.pi) := by
  set F : ℝ → ℂ := fun u => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ) with hF
  have hFfour : Integrable (𝓕 F) := by
    rw [hF]
    exact fourier_profile_integrable t ht
  have hR : (0:ℝ) < 100/Real.pi := by positivity
  have hcompl : (Set.Ioc (-(100/Real.pi)) (100/Real.pi))ᶜ
      = Set.Iic (-(100/Real.pi)) ∪ Set.Ioi (100/Real.pi) := by
    ext ξ
    simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
    constructor
    · intro h
      by_cases h1 : -(100/Real.pi) < ξ
      · by_cases h2 : ξ ≤ 100/Real.pi
        · exact absurd ⟨h1, h2⟩ h
        · push_neg at h2
          exact Or.inr h2
      · push_neg at h1
        exact Or.inl h1
    · rintro (h | h) ⟨h1, h2⟩ <;> linarith
  have hdisj : Disjoint (Set.Iic (-(100/Real.pi))) (Set.Ioi (100/Real.pi)) := by
    rw [Set.disjoint_left]
    intro ξ h1 h2
    simp only [Set.mem_Iic] at h1
    simp only [Set.mem_Ioi] at h2
    linarith
  have hnorm_int : Integrable (fun ξ : ℝ => ‖𝓕 F ξ‖) := hFfour.norm
  -- the majorant is integrable on the right half line
  have hmaj : IntegrableOn (fun ξ : ℝ => 40 / (4 * Real.pi ^ 2 * ξ ^ 2)) (Set.Ioi (100/Real.pi)) := by
    have hbase : IntegrableOn (fun ξ : ℝ => (ξ ^ 2)⁻¹) (Set.Ioi (100/Real.pi)) := by
      have h := integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hR
      refine h.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with ξ hξ
      have h0 : (0:ℝ) < ξ := hR.trans hξ
      rw [show (-2:ℝ) = -((2:ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt h0), Real.rpow_natCast]
    have hEq : (fun ξ : ℝ => 40 / (4 * Real.pi ^ 2 * ξ ^ 2))
        = fun ξ => (40 / (4 * Real.pi ^ 2)) * (ξ ^ 2)⁻¹ := by
      funext ξ
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    rw [hEq]
    exact hbase.const_mul _
  -- the value of the majorant's integral
  have hval : ∫ ξ in Set.Ioi (100/Real.pi), 40 / (4 * Real.pi ^ 2 * ξ ^ 2)
      = 40 / (400 * Real.pi) := by
    have hEq : (fun ξ : ℝ => 40 / (4 * Real.pi ^ 2 * ξ ^ 2))
        = fun ξ => (40 / (4 * Real.pi ^ 2)) * (ξ ^ 2)⁻¹ := by
      funext ξ
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    rw [hEq, MeasureTheory.integral_const_mul, integral_Ioi_inv_sq hR]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  -- bound each half line
  have hright : ∫ ξ in Set.Ioi (100/Real.pi), ‖𝓕 F ξ‖
      ≤ 40 / (400 * Real.pi) := by
    rw [← hval]
    apply MeasureTheory.setIntegral_mono_on hnorm_int.integrableOn hmaj measurableSet_Ioi
    intro ξ hξ
    have hpos : (0:ℝ) < ξ := hR.trans hξ
    have h0 : ξ ≠ 0 := ne_of_gt hpos
    · have hdec' : ‖𝓕 F ξ‖ ≤ 40 / (4 * Real.pi ^ 2 * ξ ^ 2) := by
        rw [hF]; exact fourier_decay t ht h0
      have heq : 40 / (4 * Real.pi ^ 2 * ξ ^ 2) = (40 / (4 * Real.pi ^ 2)) * (ξ ^ 2)⁻¹ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring
      rw [heq] at hdec'
      calc ‖𝓕 F ξ‖ ≤ (40 / (4 * Real.pi ^ 2)) * (ξ ^ 2)⁻¹ := hdec'
        _ = 40 / (4 * Real.pi ^ 2 * ξ ^ 2) := by
            rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
            ring
  have hleft : ∫ ξ in Set.Iic (-(100/Real.pi)), ‖𝓕 F ξ‖ ≤ 40 / (400 * Real.pi) := by
    rw [← integral_comp_neg_Ioi (100/Real.pi) (fun x : ℝ => ‖𝓕 F x‖)]
    rw [← hval]
    apply MeasureTheory.setIntegral_mono_on (hnorm_int.comp_neg).integrableOn hmaj measurableSet_Ioi
    intro ξ hξ
    have hpos : (0:ℝ) < ξ := hR.trans hξ
    have h0 : -ξ ≠ 0 := neg_ne_zero.mpr (ne_of_gt hpos)
    · have hdec' : ‖𝓕 F (-ξ)‖ ≤ 40 / (4 * Real.pi ^ 2 * (-ξ) ^ 2) := by
        rw [hF]; exact fourier_decay t ht h0
      have heq : 40 / (4 * Real.pi ^ 2 * (-ξ) ^ 2) = (40 / (4 * Real.pi ^ 2)) * ((-ξ) ^ 2)⁻¹ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring
      rw [heq] at hdec'
      have hsq : ((-ξ) ^ 2) = ξ ^ 2 := by ring
      calc ‖𝓕 F (-ξ)‖ ≤ (40 / (4 * Real.pi ^ 2)) * ((-ξ) ^ 2)⁻¹ := hdec'
        _ = 40 / (4 * Real.pi ^ 2 * ξ ^ 2) := by
            rw [hsq, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
            ring
  rw [hcompl, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    hnorm_int.integrableOn hnorm_int.integrableOn]
  have : 40 / (400 * Real.pi) + 40 / (400 * Real.pi) = 40 / (200 * Real.pi) := by
    field_simp
    ring
  linarith [hleft, hright, this]

/-- The profile is nonnegative. -/
theorem hfun_nonneg (t : ℝ) : 0 ≤ LeanLab.HelfgottArcs.hfun t := by
  rw [LeanLab.HelfgottArcs.hfun]
  split_ifs with h
  · have h1 : (0:ℝ) ≤ t ^ 2 := sq_nonneg t
    have h2 : (0:ℝ) ≤ (2 - t) ^ 3 := by
      apply pow_nonneg
      linarith [h.2]
    positivity
  · exact le_refl 0

/-- The Dirichlet average of the profile. -/
theorem mconv_abs_le (t : ℝ) (ht : 0 < t) :
    |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun (LeanLab.HelfgottArcs.FH 200) t|
      ≤ |LeanLab.HelfgottArcs.hfun t| + 40 / (200 * Real.pi) := by
  set F : ℝ → ℂ := fun u => (LeanLab.HelfgottArcs.hfun (t * Real.exp (-u)) : ℂ) with hF
  set s : Set ℝ := Set.Ioc (-(100/Real.pi)) (100/Real.pi) with hs
  have hsmeas : MeasurableSet s := hs ▸ measurableSet_Ioc
  have hFfour : Integrable (𝓕 F) := by
    rw [hF]
    exact fourier_profile_integrable t ht
  have htrunc := mconv_eq_truncated t ht
  have hinv := profile_eq_integral_re t ht
  have hsfour : Integrable (fun ξ : ℝ => (𝓕 F ξ).re) := Complex.reCLM.integrable_comp hFfour
  have hsplit : (∫ ξ in s, (𝓕 F ξ).re) + (∫ ξ in sᶜ, (𝓕 F ξ).re)
      = ∫ ξ : ℝ, (𝓕 F ξ).re :=
    MeasureTheory.integral_add_compl hsmeas hsfour
  have hrepr : LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun
        (LeanLab.HelfgottArcs.FH 200) t
      = LeanLab.HelfgottArcs.hfun t - ∫ ξ in sᶜ, (𝓕 F ξ).re := by
    rw [htrunc, hinv]
    linarith [hsplit]
  have htail : |∫ ξ in sᶜ, (𝓕 F ξ).re| ≤ 40 / (200 * Real.pi) := by
    have h1 : |∫ ξ in sᶜ, (𝓕 F ξ).re| ≤ ∫ ξ in sᶜ, ‖(𝓕 F ξ).re‖ :=
      MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict sᶜ)
        (f := fun ξ : ℝ => (𝓕 F ξ).re)
    have h2 : ∫ ξ in sᶜ, ‖(𝓕 F ξ).re‖ ≤ ∫ ξ in sᶜ, ‖𝓕 F ξ‖ := by
      apply MeasureTheory.setIntegral_mono_on hsfour.norm.integrableOn hFfour.norm.integrableOn
        hsmeas.compl
      · intro ξ _
        exact Complex.abs_re_le_norm _
    have h3 := tail_le t ht
    linarith [h1, h2, h3]
  calc |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun (LeanLab.HelfgottArcs.FH 200) t|
      = |LeanLab.HelfgottArcs.hfun t - ∫ ξ in sᶜ, (𝓕 F ξ).re| := by rw [hrepr]
    _ ≤ |LeanLab.HelfgottArcs.hfun t| + |∫ ξ in sᶜ, (𝓕 F ξ).re| := abs_sub _ _
    _ ≤ |LeanLab.HelfgottArcs.hfun t| + 40 / (200 * Real.pi) := by linarith [htail]

/-- The uniform sup bound for Helfgott's eta-plus weight. -/
theorem etaPlus_abs_le (t : ℝ) : |LeanLab.HelfgottArcs.etaPlus t| ≤ (1.079955 : ℝ) := by
  by_cases ht : 0 < t
  · have h1 := mconv_abs_le t ht
    have h2 : LeanLab.HelfgottArcs.etaPlus t
        = LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun (LeanLab.HelfgottArcs.FH 200) t * t
            * Real.exp (-(t ^ 2) / 2) := by
      rw [LeanLab.HelfgottArcs.etaPlus, if_pos ht]
    have hexpnn : (0:ℝ) < Real.exp (-(t ^ 2) / 2) := Real.exp_pos _
    have htne : (0:ℝ) < t := ht
    have ht1 : t * Real.exp (-(t ^ 2) / 2) ≤ 1 := by
      have hlog : Real.log t ≤ t ^ 2 / 2 := by
        rcases le_or_gt t 1 with h | h
        · have h0 : Real.log t ≤ 0 := Real.log_nonpos ht.le h
          nlinarith
        · have h0 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht
          nlinarith
      have hexp : t ≤ Real.exp (t ^ 2 / 2) := by
        have h := Real.exp_le_exp.mpr hlog
        rwa [Real.exp_log ht] at h
      calc t * Real.exp (-(t ^ 2) / 2) ≤ Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2) := by
            apply mul_le_mul_of_nonneg_right hexp hexpnn.le
        _ = 1 := by
            rw [← Real.exp_add, show t ^ 2 / 2 + -(t ^ 2) / 2 = 0 by ring, Real.exp_zero]
    have hw := hfun_weight_le t
    have habs : |LeanLab.HelfgottArcs.hfun t| = LeanLab.HelfgottArcs.hfun t :=
      abs_of_nonneg (hfun_nonneg t)
    have hE : (0:ℝ) ≤ 40 / (200 * Real.pi) := by positivity
    have hAe : LeanLab.HelfgottArcs.hfun t * (t * Real.exp (-(t ^ 2) / 2)) ≤ 1 := by
      have h := hfun_weight_le t
      calc LeanLab.HelfgottArcs.hfun t * (t * Real.exp (-(t ^ 2) / 2))
          = LeanLab.HelfgottArcs.hfun t * t * Real.exp (-(t ^ 2) / 2) := by ring
        _ ≤ 1 := h
    have hEe : 40 / (200 * Real.pi) * (t * Real.exp (-(t ^ 2) / 2)) ≤ 40 / (200 * Real.pi) := by
      have h := mul_le_mul_of_nonneg_left ht1 hE
      calc 40 / (200 * Real.pi) * (t * Real.exp (-(t ^ 2) / 2))
          ≤ 40 / (200 * Real.pi) * 1 := h
        _ = 40 / (200 * Real.pi) := by ring
    have hbound : |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun
          (LeanLab.HelfgottArcs.FH 200) t| * t * Real.exp (-(t ^ 2) / 2)
        ≤ 1 + 40 / (200 * Real.pi) := by
      rw [habs] at h1
      calc |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun
            (LeanLab.HelfgottArcs.FH 200) t| * t * Real.exp (-(t ^ 2) / 2)
          = |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun
              (LeanLab.HelfgottArcs.FH 200) t| * (t * Real.exp (-(t ^ 2) / 2)) := by ring
        _ ≤ (LeanLab.HelfgottArcs.hfun t + 40 / (200 * Real.pi))
              * (t * Real.exp (-(t ^ 2) / 2)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ t * Real.exp (-(t ^ 2) / 2))
        _ = LeanLab.HelfgottArcs.hfun t * (t * Real.exp (-(t ^ 2) / 2))
              + 40 / (200 * Real.pi) * (t * Real.exp (-(t ^ 2) / 2)) := by ring
        _ ≤ 1 + 40 / (200 * Real.pi) := by linarith [hAe, hEe]
    rw [h2, abs_mul, abs_mul, abs_of_pos hexpnn, abs_of_pos ht]
    have hfinal : 1 + 40 / (200 * Real.pi) ≤ (1.079955 : ℝ) := by
      have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
      have hE2 : 40 / (200 * Real.pi) ≤ (0.079955 : ℝ) := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 200 * Real.pi)]
        nlinarith
      linarith
    linarith [hbound, hfinal]
  · rw [LeanLab.HelfgottArcs.etaPlus, if_neg ht]
    simp
    norm_num

end EtaBound379

namespace LeanLab.Ternary.Task379
open Finset
open MeasureTheory
open scoped ArithmeticFunction

/-- A finite ordered triple sum with arbitrary real weights.
Helfgott page 70, equation 7.49. Terms outside the sum constraint vanish.
Nonnegative integer triples with sum N already have every coordinate at most N. -/
noncomputable def weightedTotal (N : ℕ) (w : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1), ∑ r ∈ range (N + 1),
    if p + q + r = N then w p q r else 0

/-- The discarded terms with an even or nonprime coordinate.
Helfgott page 70, equation 7.50, with arbitrary real weights. -/
noncomputable def discardedTotal (N : ℕ) (w : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1), ∑ r ∈ range (N + 1),
    if p + q + r = N ∧ ¬ (p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧ r.Prime ∧ Odd r)
      then w p q r else 0

/-- The actual scaled weights used in Helfgott section 7, page 56.
Eta plus has H equal to 200. Eta star is the Mellin convolution at scale 49.
The von Mangoldt factors are retained before the discarded terms are removed. -/
noncomputable def helfgottTripleWeight (N p q r : ℕ) : ℝ :=
  let x := LeanLab.Helfgott2013.xOf N
  (Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ) *
    LeanLab.HelfgottArcs.etaPlus (p / x) * LeanLab.HelfgottArcs.etaPlus (q / x) *
    LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
      (49 * (r / x))

/-- A positive gap after discarding terms contains a prime triple.
Helfgott page 70, final positivity argument. No weight sign condition is needed. -/
theorem isTernarySum_of_weighted_gap {N : ℕ} {w : ℕ → ℕ → ℕ → ℝ}
    (h : 0 < weightedTotal N w - discardedTotal N w) : IsTernarySum N := by
  classical
  by_contra hN
  have he : weightedTotal N w = discardedTotal N w := by
    unfold weightedTotal discardedTotal
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro r hr
    by_cases hs : p + q + r = N
    · have hn : ¬ (p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧ r.Prime ∧ Odd r) := by
        intro hh
        exact hN ⟨p, q, r, hh.1, hh.2.2.1, hh.2.2.2.2.1, hs⟩
      simp only [hs, hn, not_false_eq_true, and_self, ite_true]
    · simp only [hs, false_and, ite_false]
  rw [he, sub_self] at h
  exact lt_irrefl 0 h


/-! ### Helfgott (7.50), ported finite-union reduction

The block below is the sorry-free finite combinatorial reduction of Helfgott page 70,
equation 7.50, ported from `LeanLab.Ternary.Decomp420a` (which imports this file, so it
cannot be imported back). It is stated for the weights of this file. -/
/-- Cyclic relabeling preserves a finite triple sum.
Derived finite sum step for Helfgott page 70, equation 7.50. -/
theorem triple_sum_rotate {α : Type*} (s : Finset α) (f : α → α → α → ℝ) :
    (∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, f p q r) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, f r p q := by
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  rw [sum_comm]

/-- Fixing two coordinates leaves at most one third coordinate.
Helfgott page 70, equation 7.50, before summing the two remaining masses. -/
theorem constrained_inner_sum_le (N p q : ℕ) (a : ℕ → ℝ) (L : ℝ)
    (haL : ∀ n ∈ range (N + 1), a n ≤ L) (hL : 0 ≤ L) :
    (∑ r ∈ range (N + 1), if p + q + r = N then a r else 0) ≤ L := by
  by_cases hpq : p + q ≤ N
  · have hr : N - (p + q) ∈ range (N + 1) := mem_range.mpr (by omega)
    have he (r : ℕ) : p + q + r = N ↔ r = N - (p + q) := by omega
    simpa only [he, sum_ite_eq', ite_eq_left hr] using haL _ hr
  · have he (r : ℕ) : p + q + r ≠ N := by omega
    simpa only [he, ite_false, sum_const_zero] using hL

/-- One specified bad coordinate costs its mass times the full mass and L.
Helfgott page 70, the second inequality of equation 7.50.
The good predicate is arbitrary and the coordinate weights are nonnegative. -/
theorem bad_first_sum_le (N : ℕ) (a : ℕ → ℝ) (G : ℕ → Prop) [DecidablePred G]
    (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (ha : ∀ n ∈ range (N + 1), 0 ≤ a n)
    (haL : ∀ n ∈ range (N + 1), a n ≤ L) :
    (∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1), ∑ r ∈ range (N + 1),
      if p + q + r = N ∧ ¬ G p then C * a p * a q * a r else 0) ≤
      C * L * (∑ p ∈ range (N + 1), if ¬ G p then a p else 0) *
        (∑ q ∈ range (N + 1), a q) := by
  calc
    _ ≤ ∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1),
        if ¬ G p then C * a p * a q * L else 0 := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro q hq
      by_cases hg : G p
      · simp only [hg, not_true_eq_false, and_false, ite_false, sum_const_zero]
        exact le_rfl
      · simp only [hg, not_false_eq_true, and_true, ite_true]
        have he (r : ℕ) : (if p + q + r = N then C * a p * a q * a r else 0) =
            C * a p * a q * (if p + q + r = N then a r else 0) := by
          split_ifs <;> ring
        simp_rw [he]
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (constrained_inner_sum_le N p q a L haL hL)
          (mul_nonneg (mul_nonneg hC (ha p hp)) (ha q hq))
    _ = ∑ p ∈ range (N + 1),
        (C * L * (if ¬ G p then a p else 0)) * (∑ q ∈ range (N + 1), a q) := by
      apply sum_congr rfl
      intro p hp
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      split_ifs <;> ring
    _ = _ := by rw [← sum_mul, ← mul_sum]

/-- Three choices for the bad coordinate give the factor three.
Helfgott page 70, equation 7.50. No sign condition on w is required. -/
theorem discarded_le_of_weight_bound (N : ℕ) (a : ℕ → ℝ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (ha : ∀ n ∈ range (N + 1), 0 ≤ a n)
    (haL : ∀ n ∈ range (N + 1), a n ≤ L)
    (w : ℕ → ℕ → ℕ → ℝ)
    (hw : ∀ p ∈ range (N + 1), ∀ q ∈ range (N + 1), ∀ r ∈ range (N + 1),
      w p q r ≤ C * a p * a q * a r) :
    Task379.discardedTotal N w ≤
      3 * C * L * (∑ p ∈ range (N + 1), if ¬ (p.Prime ∧ Odd p) then a p else 0) *
        (∑ q ∈ range (N + 1), a q) := by
  classical
  let G : ℕ → Prop := fun p => p.Prime ∧ Odd p
  let s := range (N + 1)
  let A := fun p q r => C * a p * a q * a r
  let M := C * L * (∑ p ∈ s, if ¬ G p then a p else 0) * (∑ q ∈ s, a q)
  let S₁ := ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
    if p + q + r = N ∧ ¬ G p then A p q r else 0
  let S₂ := ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
    if p + q + r = N ∧ ¬ G q then A p q r else 0
  let S₃ := ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
    if p + q + r = N ∧ ¬ G r then A p q r else 0
  have h₁ : S₁ ≤ M := bad_first_sum_le N a G C L hC hL ha haL
  have h₂ : S₂ = S₁ := by
    dsimp [S₂, S₁]
    rw [triple_sum_rotate]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro r hr
    have he : r + p + q = p + q + r := by omega
    simp only [he]
    split_ifs <;> dsimp [A] <;> ring
  have h₃ : S₃ = S₁ := by
    dsimp [S₃, S₁]
    rw [triple_sum_rotate, triple_sum_rotate]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro r hr
    have he : q + r + p = p + q + r := by omega
    simp only [he]
    split_ifs <;> dsimp [A] <;> ring
  have hu : Task379.discardedTotal N w ≤ S₁ + S₂ + S₃ := by
    dsimp [Task379.discardedTotal, S₁, S₂, S₃]
    simp only [← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro q hq
    apply sum_le_sum
    intro r hr
    have hA : 0 ≤ A p q r :=
      mul_nonneg (mul_nonneg (mul_nonneg hC (ha p hp)) (ha q hq)) (ha r hr)
    have hW := hw p hp q hq r hr
    change w p q r ≤ A p q r at hW
    have hg : (p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧ r.Prime ∧ Odd r) ↔
        G p ∧ G q ∧ G r := by dsimp [G]; tauto
    simp only [hg]
    by_cases hs : p + q + r = N
    · by_cases hpG : G p <;> by_cases hqG : G q <;> by_cases hrG : G r <;>
        simp only [hs, hpG, hqG, hrG, not_true_eq_false, not_false_eq_true,
          and_true, and_false, ite_true, ite_false] <;> linarith
    · simp only [hs, false_and, ite_false, add_zero, le_refl]
  rw [h₂, h₃] at hu
  calc
    _ ≤ S₁ + S₁ + S₁ := hu
    _ ≤ M + M + M := add_le_add (add_le_add h₁ h₁) h₁
    _ = _ := by dsimp [M, s, G]; ring

/-- The discarded one dimensional mass is psi minus theta plus log two.
Helfgott page 70 below equation 7.50. The endpoint two is counted once. -/
theorem bad_mangoldt_mass_identity (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ range (N + 1), if ¬ (n.Prime ∧ Odd n) then (Λ n : ℝ) else 0) =
      Chebyshev.psi N - Chebyshev.theta N + Real.log 2 := by
  classical
  have he (n : ℕ) :
      (if ¬ (n.Prime ∧ Odd n) then (Λ n : ℝ) else 0) =
        ((Λ n : ℝ) - if n.Prime then Real.log n else 0) +
          if n = 2 then Real.log 2 else 0 := by
    by_cases hn : n.Prime
    · by_cases htwo : n = 2
      · subst n
        norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      · simp [hn, hn.odd_of_ne_two htwo, htwo,
          ArithmeticFunction.vonMangoldt_apply_prime hn]
    · have htwo : n ≠ 2 := by intro h; subst n; exact hn Nat.prime_two
      simp [hn, htwo]
  simp_rw [he]
  rw [sum_add_distrib, sum_sub_distrib]
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero, sum_filter]
  have htwo : 2 ∈ range (N + 1) := mem_range.mpr (by omega)
  simp only [sum_ite_eq', ite_eq_left htwo]

/-- A coarse psi bound sufficient after the stronger prime power mass estimate.
Derived replacement for the RS62 step on Helfgott page 70.
The proved Chebyshev bound is used instead of the quoted coefficient 1.03883. -/
theorem psi_le_111 {x : ℝ} (hx : 10 ^ 8 ≤ x) : Chebyshev.psi x ≤ 1.11 * x := by
  have hx0 : 0 < x := by linarith
  have hp := LeanLab.Common.PsiTheta.psi_le_real (by linarith : 1 ≤ x)
  have hl := LeanLab.Common.PsiTheta.log_le_four_root hx0
  let u := x ^ ((4 : ℕ) : ℝ)⁻¹
  have hu0 : 0 ≤ u := Real.rpow_nonneg hx0.le _
  have hu4 : u ^ 4 = x := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast hx0.le]
    norm_num
  have hu100 : 100 ≤ u := le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hu0
    (by rw [hu4]; norm_num at hx ⊢; exact hx)
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hlu : Real.log x ≤ 2 * u := by
    have h : 4 * u / Real.exp 1 ≤ 2 * u :=
      (div_le_iff₀ (Real.exp_pos 1)).mpr (by nlinarith)
    exact hl.trans h
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq : Real.log x ^ 2 ≤ 4 * u ^ 2 := by nlinarith
  have hu2 : 10000 ≤ u ^ 2 := by nlinarith
  have hu4' : 10000 * u ^ 2 ≤ u ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu2)]
  have hbudget : 2 * Real.log x ^ 2 + 160 ≤ 0.0038 * x := by
    rw [← hu4]
    rw [← hu4] at hsq
    nlinarith
  linarith

/-- The bad coordinate mass is at most 1.251 times the square root.
Derived stronger replacement for Helfgott page 70 below equation 7.50.
The extra log two is absorbed once N is at least ten to power eight. -/
theorem bad_mangoldt_mass_le (N : ℕ) (hN : (10 : ℝ) ^ (8 : ℕ) ≤ N) :
    (∑ n ∈ range (N + 1), if ¬ (n.Prime ∧ Odd n) then (Λ n : ℝ) else 0) ≤
      1.251 * Real.sqrt N := by
  have hN2 : 2 ≤ N := by exact_mod_cast (by linarith : (2 : ℝ) ≤ N)
  rw [bad_mangoldt_mass_identity N hN2]
  have hp := LeanLab.Common.PsiTheta.psi_sub_theta_lt_125 hN
  have hs : (10000 : ℝ) ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num at hN ⊢
    exact hN
  have hl := Real.log_two_lt_d9
  linarith

/-- The full range sum is precisely psi, including the zero term.
Derived endpoint convention for Helfgott page 70, equation 7.50. -/
theorem mangoldt_range_sum (N : ℕ) :
    (∑ n ∈ range (N + 1), (Λ n : ℝ)) = Chebyshev.psi N := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero]

/-- The full positive Mellin integral equals the proved compact support model.
Helfgott page 60, equation 7.19, using eta two from page 25, equation 4.7.
This bridge applies only at nonnegative arguments. -/
theorem etaStar_eq_mellin {w : ℝ} (hw : 0 ≤ w) :
    LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2 w =
      LeanLab.Helfgott2013.MellinL2.mellin w := by
  unfold LeanLab.HelfgottArcs.mconv LeanLab.Helfgott2013.MellinL2.mellin
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Set.Icc (1 / 4 : ℝ) 1 ⊆ Set.Ioi 0 by
      intro t ht
      exact (by linarith [ht.1] : 0 < t))]
  · apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hz : 0 ≤ w / t := div_nonneg hw ht0.le
    have hg : LeanLab.HelfgottArcs.etaT2 (w / t) =
        LeanLab.Helfgott2013.GaussianL2.phi (w / t) := by
      unfold LeanLab.HelfgottArcs.etaT2 LeanLab.Helfgott2013.GaussianL2.phi
      split_ifs with h
      · rfl
      · have he : w / t = 0 := by linarith
        simp [he]
    dsimp only
    rw [hg]
    rfl
  · intro t ht
    have he : LeanLab.HelfgottArcs.eta2 t = 0 :=
      LeanLab.Helfgott2013.EtaTwo.etaTwo_eq_zero ht.2
    rw [he, zero_mul, zero_div]

/-- The actual eta star has the already proved sup bound.
Helfgott page 60, equation 7.19. No new analytic leaf is needed for this weight. -/
theorem etaStar_abs_le {w : ℝ} (hw : 0 ≤ w) :
    |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2 w| ≤
      (1.414 : ℝ) := by
  rw [etaStar_eq_mellin hw]
  exact (LeanLab.Helfgott2013.MellinSup.mellin_sup w).2
/-- Every coordinate von Mangoldt value is at most log N.
Helfgott page 70, the second inequality of equation 7.50. -/
theorem mangoldt_le_log_of_le {n N : ℕ} (hN : 1 ≤ N) (hn : n ≤ N) :
    (Λ n : ℝ) ≤ Real.log N := by
  by_cases hn0 : n = 0
  · simp only [hn0, ArithmeticFunction.map_zero]
    exact Real.log_nonneg (by exact_mod_cast hN)
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) (by exact_mod_cast hn))

/-- The actual triple weight is bounded by the product of three von Mangoldt values.
Helfgott page 70, equation 7.50, using the sup bounds from 7.3 and 7.19.
CONDITIONAL ON the stated eta plus sup hypothesis. -/
theorem helfgottTripleWeight_le
    (hplus : ∀ t : ℝ, |LeanLab.HelfgottArcs.etaPlus t| ≤ (1.079955 : ℝ))
    (N p q r : ℕ) :
    Task379.helfgottTripleWeight N p q r ≤
      (1.079955 ^ 2 * 1.414) * (Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ) := by
  let x := LeanLab.Helfgott2013.xOf N
  have hx : 0 ≤ x := by
    dsimp [x, LeanLab.Helfgott2013.xOf, LeanLab.Helfgott2013.ratio]
    positivity
  have hstar := etaStar_abs_le (show 0 ≤ 49 * (r / x) by positivity)
  have hprod :
      |LeanLab.HelfgottArcs.etaPlus (p / x) * LeanLab.HelfgottArcs.etaPlus (q / x) *
        LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
          (49 * (r / x))| ≤ (1.079955 ^ 2 * 1.414 : ℝ) := by
    rw [abs_mul, abs_mul, pow_two]
    exact mul_le_mul (mul_le_mul (hplus _) (hplus _) (abs_nonneg _) (by norm_num))
      hstar (abs_nonneg _) (by norm_num)
  have hA : 0 ≤ (Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ) := by positivity
  calc
    _ = ((Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ)) *
        (LeanLab.HelfgottArcs.etaPlus (p / x) * LeanLab.HelfgottArcs.etaPlus (q / x) *
          LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
            (49 * (r / x))) := by unfold Task379.helfgottTripleWeight; dsimp [x]; ring
    _ ≤ ((Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ)) *
        |LeanLab.HelfgottArcs.etaPlus (p / x) * LeanLab.HelfgottArcs.etaPlus (q / x) *
          LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
            (49 * (r / x))| := mul_le_mul_of_nonneg_left (le_abs_self _) hA
    _ ≤ ((Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ)) * (1.079955 ^ 2 * 1.414) :=
      mul_le_mul_of_nonneg_left hprod hA
    _ = _ := by ring

/-! ### The eta plus sup bound (to be proved below from the second-derivative norm) -/

/-- The exact existing discarded contribution bound follows from the smaller smoothing leaf.
Helfgott page 70, equation 7.50 and the following displays.
The stronger proved prime power mass estimate replaces the quoted RS62 constants.
CONDITIONAL ON etaPlus_abs_le alone. -/
theorem helfgott_discarded_upper_of_eta
    (hplus : ∀ t : ℝ, |LeanLab.HelfgottArcs.etaPlus t| ≤ (1.079955 : ℝ))
    (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    Task379.discardedTotal N (Task379.helfgottTripleWeight N) ≤
      7.3306 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.log N := by
  have hN8 : (10 : ℝ) ^ (8 : ℕ) ≤ N := by norm_num at hN ⊢; linarith
  have hN1 : 1 ≤ N := by exact_mod_cast (by norm_num at hN8; linarith : (1 : ℝ) ≤ N)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hb := bad_mangoldt_mass_le N hN8
  have hp := psi_le_111 hN8
  have hsum := discarded_le_of_weight_bound N (fun n => (Λ n : ℝ))
    (1.079955 ^ 2 * 1.414) (Real.log N) (by norm_num) hlog
    (fun n hn => ArithmeticFunction.vonMangoldt_nonneg)
    (fun n hn => mangoldt_le_log_of_le hN1 (by have := mem_range.mp hn; omega))
    (Task379.helfgottTripleWeight N)
    (fun p hp q hq r hr => helfgottTripleWeight_le hplus N p q r)
  rw [mangoldt_range_sum] at hsum
  have hs := mul_le_mul hb hp (Chebyshev.psi_nonneg _) (by positivity : 0 ≤ 1.251 * Real.sqrt N)
  have hbound := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 3 * (1.079955 ^ 2 * 1.414) * Real.log N by positivity)
  have hpow : Real.sqrt (N : ℝ) * N = (N : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      _ = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < N))]
        norm_num
  have hcoeff : (3 : ℝ) * (1.079955 ^ 2 * 1.414) * (1.251 * 1.11) ≤ 7.3306 := by norm_num
  calc
    _ ≤ 3 * (1.079955 ^ 2 * 1.414) * Real.log N *
        ((1.251 * Real.sqrt N) * (1.11 * N)) := by nlinarith only [hsum, hbound]
    _ = (3 * (1.079955 ^ 2 * 1.414) * (1.251 * 1.11)) *
        (N : ℝ) ^ (3 / 2 : ℝ) * Real.log N := by rw [← hpow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by positivity) _)) hlog

/-- LEAF. The major and minor arc analysis lower bounds the full weighted count.
Helfgott pages 62 and 69 to 70, equations 7.25, 7.48 and 7.49.
Use the repaired minor coefficient 0.97757 from the existing Slip proof,
so the total coefficient is the weaker valid 0.08068 rather than printed 0.08433.
This leaf counts prime powers as well as primes and has no representation conclusion. -/
theorem helfgott_weighted_total_lower (N : ℕ) (ho : Odd N)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    0.08068 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ ≤
      weightedTotal N (helfgottTripleWeight N) := by sorry

/-- LEAF. The even and nonprime contribution is bounded separately.
Helfgott page 70, equation 7.50 and the following RS62 estimates.
The coefficients use the actual smoothing weights, before any existence argument. -/
theorem helfgott_discarded_upper (N : ℕ)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    discardedTotal N (helfgottTripleWeight N) ≤
      7.3306 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.log N := by
  exact helfgott_discarded_upper_of_eta EtaBound379.etaPlus_abs_le N hN

/-- The exact sealed Helfgott analytic threshold from two smaller estimates.
Helfgott page 70, final display, with the corrected coefficient proved in Slip.
CONDITIONAL ON helfgott_weighted_total_lower. -/
theorem helfgott_analytic_decomposed : TernaryAbove (10 ^ 27) := by
  intro N ho hN
  have hN' : (1e27 : ℝ) ≤ N := by convert hN using 1 <;> norm_num
  have hgap := (LeanLab.Helfgott2013.repaired_chain hN'
    (helfgott_weighted_total_lower N ho hN) (helfgott_discarded_upper N hN)).2.2
  exact isTernarySum_of_weighted_gap hgap

/-- The exact sealed weighted Chen and Wang statement follows through the threshold chain.
P0033 page 169, main theorem, using the proved threshold comparisons in this folder.
This is a derived bridge from Helfgott, not a formalization of the 1996 argument.
CONDITIONAL ON the two explicit Helfgott estimates above. -/
theorem chenWang_weighted_decomposed :
    LeanLab.Ternary.U1535.ChenWangWeighted (Real.exp (Real.exp 9.715)) :=
  LeanLab.Ternary.U1535.chenWangWeighted_of_ternaryAbove
    (chenWang_of_liuWang (liuWang_of_helfgott helfgott_analytic_decomposed))

end LeanLab.Ternary.Task379
