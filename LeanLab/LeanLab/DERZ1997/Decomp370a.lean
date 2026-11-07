import LeanLab.DERZ1997.Decomp1529a

/-!
Supply for primitive_zero_count193. The sealed file is unchanged.
Trudgian, arXiv:1206.1844v4, pages 3 to 9, separates the Gamma phase,
the argument principle and the Backlund argument bound.
The principal character is handled separately through the existing Rosser input.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.DERZ1997.Decomp370a
open Complex Filter Topology MeasureTheory Set Decomp1529a

/-- The character parity in Trudgian page 3, display 2.1.
An even character has parity zero and an odd character has parity one.
-/
noncomputable def parity370 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ := by
  classical
  exact if χ.Even then 0 else 1

/-- The continuous Gamma phase divided by pi, with parity a equal to zero or one.
Trudgian page 3, displays 2.3 to 2.5. Integrating digamma fixes the continuous branch.
-/
noncomputable def gammaPhase370 (a T : ℝ) : ℝ :=
  2 / Real.pi * ∫ t in (0 : ℝ)..T / 2,
    (Complex.digamma (((1 / 4 + a / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re

/-- The continuous Gamma phase integrand is continuous on the real line.
Trudgian page 3, display 2.3. The Gamma argument stays in the positive real half-plane.
-/
theorem gamma_integrand_continuous370 {a : ℝ} (ha : 0 ≤ a) :
    Continuous (fun t : ℝ =>
      (Complex.digamma (((1 / 4 + a / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re) := by
  have hp {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hr := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at hr
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (hp hz)).differentiableWithinAt
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply continuous_iff_continuousAt.mpr
  intro t
  let z : ℂ := ((1 / 4 + a / 2 : ℝ) : ℂ) + (t : ℂ) * I
  have hz : 0 < z.re := by dsimp [z]; simp only [ofReal_re, mul_re, I_re, I_im, ofReal_im]; linarith
  have hg := hd.analyticAt (ho.mem_nhds hz)
  have hc : ContinuousAt Complex.digamma z := by
    exact (hg.deriv.continuousAt.div hg.continuousAt (Complex.Gamma_ne_zero (hp hz)))
  have hf : ContinuousAt (fun u : ℝ => ((1 / 4 + a / 2 : ℝ) : ℂ) + (u : ℂ) * I) t := by fun_prop
  have hcomp : ContinuousAt (fun u : ℝ => Complex.digamma
      (((1 / 4 + a / 2 : ℝ) : ℂ) + (u : ℂ) * I)) t :=
    ContinuousAt.comp (f := fun u : ℝ =>
      ((1 / 4 + a / 2 : ℝ) : ℂ) + (u : ℂ) * I) hc hf
  exact Complex.continuous_re.continuousAt.comp hcomp

/-- The continuous Gamma phase integrand is integrable on every finite interval.
Trudgian page 3, display 2.3. No analytic zero-count input is used.
-/
theorem gamma_phase_integrable370 {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (Complex.digamma (((1 / 4 + a / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re)
      volume 0 (T / 2) :=
  (gamma_integrand_continuous370 ha).intervalIntegrable _ _

/-- The phase is a normalized antiderivative of the real digamma value.
Trudgian page 3, display 2.3. This identifies the derivative without choosing a complex log branch.
-/
theorem gamma_phase_deriv370 {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    HasDerivAt (gammaPhase370 a)
      ((Complex.digamma (((1 / 4 + a / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).re /
        Real.pi) T := by
  have hf := ((gamma_integrand_continuous370 ha).integral_hasStrictDerivAt 0 (T / 2)).hasDerivAt
  have hh := (hf.comp T ((hasDerivAt_id T).div_const 2)).const_mul (2 / Real.pi)
  convert hh using 1 <;> first | rfl | ring

/-- The argument variation divided by pi on the right half of the count contour.
Trudgian pages 3 and 4, display 2.3 and the three segments following 2.6.
The path runs from one half minus iT to 2 minus iT, then upwards and then left.
-/
noncomputable def argument370 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) : ℝ :=
  (1 / Real.pi) *
    ((∫ σ in (1 / 2 : ℝ)..2,
      logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - (T : ℂ) * I)) +
     I * (∫ t in (-T)..T,
      logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)) +
     (∫ σ in (2 : ℝ)..(1 / 2 : ℝ),
      logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I))).im

/-- The right limit of the contour argument includes zeros at the cutoff height.
Trudgian page 1 defines the count with inclusive height. Page 3 gives the contour formula.
-/
noncomputable def argumentRight370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  Filter.limUnder (𝓝[>] T) (argument370 χ)

/-- The elementary part of the Gamma correction in Trudgian page 3, display 2.5.
The Stirling remainder is excluded from this real expression.
-/
noncomputable def gammaCorrection370 (a T : ℝ) : ℝ :=
  T / 4 * Real.log (1 + (2 * a + 1)^2 / (4 * T^2)) +
    (2 * a - 1) / 4 * Real.arctan (2 * T / (2 * a + 1))

/-- The elementary Gamma correction has a uniform numerical majorant.
Trudgian page 3, display 2.5. The bound here is derived and deliberately loose.
-/
theorem gamma_correction_bound370 {a T : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hT : 1 ≤ T) :
    |gammaCorrection370 a T| ≤ 9 / 16 + Real.pi / 8 := by
  have ht0 : 0 < T := by linarith
  have hsq : (2 * a + 1)^2 ≤ 9 := by nlinarith
  have hx0 : 0 ≤ (2 * a + 1)^2 / (4 * T^2) := by positivity
  have hlog0 : 0 ≤ Real.log (1 + (2 * a + 1)^2 / (4 * T^2)) :=
    Real.log_nonneg (by linarith)
  have hlog := Real.log_le_sub_one_of_pos (by positivity :
    0 < 1 + (2 * a + 1)^2 / (4 * T^2))
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ T / 4 by positivity)
  have he : T / 4 * ((1 + (2 * a + 1)^2 / (4 * T^2)) - 1) =
      (2 * a + 1)^2 / (16 * T) := by field_simp; ring
  rw [he] at hm
  have hratio : (2 * a + 1)^2 / (16 * T) ≤ 9 / 16 := by
    rw [div_le_iff₀ (by positivity : 0 < 16 * T)]
    nlinarith
  have hfirst : |T / 4 * Real.log (1 + (2 * a + 1)^2 / (4 * T^2))| ≤ 9/16 := by
    rw [abs_of_nonneg (mul_nonneg (by positivity) hlog0)]
    exact hm.trans hratio
  have hatan0 : 0 ≤ Real.arctan (2 * T / (2 * a + 1)) :=
    Real.arctan_nonneg.mpr (by positivity)
  have hatan : |Real.arctan (2 * T / (2 * a + 1))| ≤ Real.pi / 2 := by
    rw [abs_of_nonneg hatan0]
    exact (Real.arctan_lt_pi_div_two _).le
  have hcoef : |(2 * a - 1) / 4| ≤ 1 / 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hsecond : |(2 * a - 1) / 4 * Real.arctan (2 * T / (2 * a + 1))| ≤ Real.pi / 8 := by
    rw [abs_mul]
    have hh := mul_le_mul hcoef hatan (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/4)
    nlinarith
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-
The explicit Binet helpers below are adapted from `MathExtras.LogGammaBinet` in
https://github.com/gersh/ternary-goldbach-lean at commit
27df23af6a712895f22204d0d81102baa74f0ebe (Lean 4.32.1), Copyright (c) 2026
Gershon Bialer, Apache License 2.0. They are inlined as private lemmas to meet
this file's no-new-definition rule and rechecked here with Lean 4.35.0.
-/
private lemma gamma_log_sub_log_eq370 {z : ℂ} (hz : 0 < z.re) :
    Complex.log (z + 1) - Complex.log z = Complex.log (1 + 1 / z) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz1re : 0 < (z + 1).re := by simp; linarith
  have hexp : Complex.exp (Complex.log (z + 1) - Complex.log z) = 1 + 1 / z := by
    rw [Complex.exp_sub, Complex.exp_log hz1, Complex.exp_log hz0]
    field_simp
  rw [← hexp, Complex.log_exp]
  · have h1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz1re)
    have h2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
    simp only [Complex.sub_im, Complex.log_im]
    rw [abs_lt] at h1 h2
    linarith [h1.1, h2.2]
  · have h1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz1re)
    have h2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
    simp only [Complex.sub_im, Complex.log_im]
    rw [abs_lt] at h1 h2
    linarith [h1.2, h2.1]

private lemma gamma_logTaylor_three370 (u : ℂ) :
    Complex.logTaylor 3 u = u - u ^ 2 / 2 := by
  simp [Complex.logTaylor, Finset.sum_range_succ]
  ring

private lemma gamma_norm_log_one_add_taylor2_370 {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u) - (u - u ^ 2 / 2)‖ ≤ 2 * ‖u‖ ^ 3 / 3 := by
  have hu1 : ‖u‖ < 1 := by linarith
  have h := Complex.norm_log_sub_logTaylor_le 2 hu1
  rw [gamma_logTaylor_three370] at h
  refine le_trans h ?_
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hpos : (0 : ℝ) ≤ ‖u‖ ^ 3 := by positivity
  norm_num
  nlinarith [hinv, hpos]

private lemma gamma_norm_stirlingStep_le370 {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖1 - (z + 1 / 2) * (Complex.log (z + 1) - Complex.log z)‖ ≤ 2 / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hnpos : (0 : ℝ) < ‖z‖ := by linarith
  have hne : (‖z‖ : ℝ) ≠ 0 := ne_of_gt hnpos
  have hnorm1 : ‖(1 : ℂ) / z‖ = 1 / ‖z‖ := by rw [norm_div, norm_one]
  have hu : ‖(1 : ℂ) / z‖ ≤ 1 / 2 := by
    rw [hnorm1, div_le_div_iff₀ hnpos (by norm_num)]
    linarith
  have hE := gamma_norm_log_one_add_taylor2_370 hu
  rw [hnorm1] at hE
  have hcancel : (z + 1 / 2) * ((1 : ℂ) / z - ((1 : ℂ) / z) ^ 2 / 2) =
      1 - 1 / (4 * z ^ 2) := by
    field_simp
    ring
  have hsplit : 1 - (z + 1 / 2) * (Complex.log (z + 1) - Complex.log z) =
      1 / (4 * z ^ 2) - (z + 1 / 2) *
        (Complex.log (1 + 1 / z) - ((1 : ℂ) / z - ((1 : ℂ) / z) ^ 2 / 2)) := by
    rw [gamma_log_sub_log_eq370 hz, mul_sub, hcancel]
    ring
  rw [hsplit]
  have hb1 : ‖(1 : ℂ) / (4 * z ^ 2)‖ = 1 / (4 * ‖z‖ ^ 2) := by
    rw [norm_div, norm_one, norm_mul, norm_pow]
    simp
  have hb2 : ‖z + 1 / 2‖ ≤ ‖z‖ + 1 / 2 := by
    calc ‖z + 1 / 2‖ ≤ ‖z‖ + ‖(1 : ℂ) / 2‖ := norm_add_le _ _
      _ = ‖z‖ + 1 / 2 := by simp
  have hEn : ‖Complex.log (1 + 1 / z) - ((1 : ℂ) / z - ((1 : ℂ) / z) ^ 2 / 2)‖ ≤
      2 / (3 * ‖z‖ ^ 3) := by
    refine le_trans hE (le_of_eq ?_)
    field_simp
  have hprod : ‖(z + 1 / 2) * (Complex.log (1 + 1 / z) -
      ((1 : ℂ) / z - ((1 : ℂ) / z) ^ 2 / 2))‖ ≤
      (‖z‖ + 1 / 2) * (2 / (3 * ‖z‖ ^ 3)) := by
    rw [norm_mul]
    exact mul_le_mul hb2 hEn (norm_nonneg _) (by positivity)
  have hfinal : 1 / (4 * ‖z‖ ^ 2) + (‖z‖ + 1 / 2) * (2 / (3 * ‖z‖ ^ 3)) ≤
      2 / ‖z‖ ^ 2 := by
    have key : 2 / ‖z‖ ^ 2 -
        (1 / (4 * ‖z‖ ^ 2) + (‖z‖ + 1 / 2) * (2 / (3 * ‖z‖ ^ 3))) =
        (13 * ‖z‖ - 4) / (12 * ‖z‖ ^ 3) := by
      field_simp
      ring
    have hnn : 0 ≤ (13 * ‖z‖ - 4) / (12 * ‖z‖ ^ 3) := by
      apply div_nonneg
      · linarith
      · positivity
    linarith
  calc ‖1 / (4 * z ^ 2) - (z + 1 / 2) * (Complex.log (1 + 1 / z) -
        ((1 : ℂ) / z - ((1 : ℂ) / z) ^ 2 / 2))‖
      ≤ ‖(1 : ℂ) / (4 * z ^ 2)‖ + ‖(z + 1 / 2) * (Complex.log (1 + 1 / z) -
          ((1 : ℂ) / z - ((1 : ℂ) / z) ^ 2 / 2))‖ := norm_sub_le _ _
    _ ≤ 1 / (4 * ‖z‖ ^ 2) + (‖z‖ + 1 / 2) * (2 / (3 * ‖z‖ ^ 3)) := by
        rw [hb1]; linarith
    _ ≤ 2 / ‖z‖ ^ 2 := hfinal

private lemma gamma_summable_stirlingStep370 {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    Summable (fun k : ℕ => 1 - (z + (k : ℂ) + 1 / 2) *
      (Complex.log (z + (k : ℂ) + 1) - Complex.log (z + (k : ℂ)))) := by
  have hnorm_add (k : ℕ) : ‖z‖ ≤ ‖z + (k : ℂ)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq (norm_nonneg (z + (k : ℂ)))]
    apply Real.sqrt_le_sqrt
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.natCast_re,
      Complex.natCast_im, add_zero]
    nlinarith [Nat.cast_nonneg (α := ℝ) k, hz.le]
  have hre_add (k : ℕ) : 0 < (z + (k : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hre_le (k : ℕ) : z.re + (k : ℝ) ≤ ‖z + (k : ℂ)‖ := by
    have h := Complex.abs_re_le_norm (z + (k : ℂ))
    simp only [Complex.add_re, Complex.natCast_re] at h
    have hpos : 0 ≤ z.re + (k : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [abs_of_nonneg hpos] at h
    exact h
  apply Summable.of_norm
  have hmaj : ∀ k : ℕ, ‖1 - (z + (k : ℂ) + 1 / 2) *
      (Complex.log (z + (k : ℂ) + 1) - Complex.log (z + (k : ℂ)))‖ ≤
      2 / (z.re + (k : ℝ)) ^ 2 := by
    intro k
    refine le_trans (gamma_norm_stirlingStep_le370 (hre_add k)
      (h2.trans (hnorm_add k))) ?_
    have hb := hre_le k
    have hpos : (0 : ℝ) < z.re + (k : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    gcongr
  have hc : (0 : ℝ) < min z.re 1 := lt_min hz one_pos
  have hbase : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using h
  have hsum : Summable (fun k : ℕ => 2 / (z.re + (k : ℝ)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (hbase.mul_left (2 / (min z.re 1) ^ 2))
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hlow : min z.re 1 * ((k : ℝ) + 1) ≤ z.re + (k : ℝ) := by
      have h1 : min z.re 1 ≤ z.re := min_le_left _ _
      have h2 : min z.re 1 ≤ 1 := min_le_right _ _
      nlinarith
    have hpos : (0 : ℝ) < z.re + (k : ℝ) := by linarith
    have hsq : (min z.re 1 * ((k : ℝ) + 1)) ^ 2 ≤ (z.re + (k : ℝ)) ^ 2 := by
      have hnn : (0 : ℝ) ≤ min z.re 1 * ((k : ℝ) + 1) := by positivity
      nlinarith [hlow, hnn]
    have hexp : (min z.re 1 * ((k : ℝ) + 1)) ^ 2 =
        min z.re 1 ^ 2 * ((k : ℝ) + 1) ^ 2 := by ring
    rw [hexp] at hsq
    have hcne : (min z.re 1 : ℝ) ≠ 0 := ne_of_gt hc
    have hkne : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hrw : 2 / min z.re 1 ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) =
        2 / (min z.re 1 ^ 2 * ((k : ℝ) + 1) ^ 2) := by
      field_simp
    rw [hrw]
    have hYpos : (0 : ℝ) < min z.re 1 ^ 2 * ((k : ℝ) + 1) ^ 2 := by positivity
    exact div_le_div_of_nonneg_left (by norm_num) hYpos hsq
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hmaj hsum

private lemma gamma_sum_stirlingStep_range370 (z : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 - (z + (k : ℂ) + 1 / 2) *
      (Complex.log (z + (k : ℂ) + 1) - Complex.log (z + (k : ℂ))))) =
      ((z - 1 / 2) * Complex.log z - z) -
        ((z + (n : ℂ) - 1 / 2) * Complex.log (z + (n : ℂ)) - (z + (n : ℂ))) +
        ∑ k ∈ Finset.range n, Complex.log (z + (k : ℂ)) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hshift : z + (m : ℂ) + 1 = z + ((m : ℕ) + 1 : ℕ) := by push_cast; ring
      rw [hshift]
      push_cast
      ring

private lemma gamma_mainNoConst_im370 {a T : ℝ} (ha0 : 0 ≤ a) (hT : 0 < T)
    (z : ℂ) (hz : z = (((1 / 4 + a / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)) :
    2 / Real.pi * (((z - 1 / 2) * Complex.log z - z).im) =
      T / Real.pi * Real.log (T / (2 * Real.exp 1)) +
        2 / Real.pi * gammaCorrection370 a T := by
  subst z
  let c : ℝ := 1 / 4 + a / 2
  let t : ℝ := T / 2
  change 2 / Real.pi * ((((c : ℂ) + (t : ℂ) * I - 1 / 2) *
    Complex.log ((c : ℂ) + (t : ℂ) * I) - ((c : ℂ) + (t : ℂ) * I)).im) = _
  have hc : 0 < c := by dsimp [c]; linarith
  have ht : 0 < t := by dsimp [t]; linarith
  have hcorr : 1 + c ^ 2 / t ^ 2 = 1 + (2 * a + 1) ^ 2 / (4 * T ^ 2) := by
    dsimp [c, t]
    field_simp [hT.ne', ht.ne']
    ring
  have hargval : t / c = 2 * T / (2 * a + 1) := by
    dsimp [c, t]
    field_simp [hc.ne', hT.ne']
    ring
  have hsquare : Complex.normSq ((c : ℂ) + (t : ℂ) * I) =
      t ^ 2 * (1 + c ^ 2 / t ^ 2) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    field_simp [ht.ne']
    ring
  have hnorm : Real.log ‖(c : ℂ) + (t : ℂ) * I‖ =
      Real.log T - Real.log 2 + (1 / 2) * Real.log (1 + (2 * a + 1) ^ 2 / (4 * T ^ 2)) := by
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _), hsquare, hcorr,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hlogt : Real.log t = Real.log T - Real.log 2 := by
      dsimp [t]
      exact Real.log_div hT.ne' (by norm_num)
    rw [hlogt]
    push_cast
    ring
  have harg : Complex.arg ((c : ℂ) + (t : ℂ) * I) =
      Real.arctan (2 * T / (2 * a + 1)) := by
    have hzre : 0 < (((c : ℂ) + (t : ℂ) * I).re) := by simpa using hc
    have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
    calc
      Complex.arg ((c : ℂ) + (t : ℂ) * I) =
          Real.arctan ((((c : ℂ) + (t : ℂ) * I).im) /
            (((c : ℂ) + (t : ℂ) * I).re)) :=
        (Real.arctan_eq_of_tan_eq (Complex.tan_arg _) (abs_lt.mp ha)).symm
      _ = Real.arctan (t / c) := by simp
      _ = Real.arctan (2 * T / (2 * a + 1)) := by rw [hargval]
  have hmainlog : Real.log (T / (2 * Real.exp 1)) = Real.log T - Real.log 2 - 1 := by
    rw [Real.log_div hT.ne' (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero 1), Real.log_exp]
    ring
  rw [hmainlog]
  simp only [Complex.sub_im, Complex.mul_im, Complex.sub_re,
    Complex.log_re, Complex.log_im, hnorm, harg]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  dsimp [c, t]
  unfold gammaCorrection370
  push_cast
  norm_num
  ring

private lemma gamma_log_sub_log_of_re_pos370 {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.log a - Complex.log b = Complex.log (a / b) := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hexp : Complex.exp (Complex.log a - Complex.log b) = a / b := by
    rw [Complex.exp_sub, Complex.exp_log ha0, Complex.exp_log hb0]
  rw [← hexp, Complex.log_exp]
  · have h1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
    have h2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
    simp only [Complex.sub_im, Complex.log_im]
    rw [abs_lt] at h1 h2
    linarith [h1.1, h2.2]
  · have h1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
    have h2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
    simp only [Complex.sub_im, Complex.log_im]
    rw [abs_lt] at h1 h2
    linarith [h1.2, h2.1]

private lemma gamma_tendsto_stirling_ratio370 :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) /
      (Nat.factorial n : ℝ)) atTop (𝓝 (1 / Real.sqrt (2 * Real.pi))) := by
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hstir := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlim : Tendsto (fun n : ℕ => 1 / (Real.sqrt 2 * Stirling.stirlingSeq n))
      atTop (𝓝 (1 / (Real.sqrt 2 * Real.sqrt Real.pi))) := by
    refine Tendsto.div tendsto_const_nhds (tendsto_const_nhds.mul hstir) ?_
    positivity
  have hsq : Real.sqrt 2 * Real.sqrt Real.pi = Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by norm_num)]
  rw [hsq] at hlim
  refine hlim.congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Stirling.stirlingSeq]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    unfold Stirling.stirlingSeq
    rw [Real.rpow_add hnpos, Real.rpow_natCast]
    have h2n : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) :=
      Real.sqrt_mul (by norm_num) _
    have hhalf : (n : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (n : ℝ) := by rw [Real.sqrt_eq_rpow]
    rw [hhalf, h2n]
    have hdiv : ((n : ℝ) / Real.exp 1) ^ n =
        (n : ℝ) ^ n * Real.exp (-(n : ℝ)) := by
      rw [div_pow, Real.exp_neg, ← Real.exp_nat_mul]
      simp [div_eq_mul_inv]
    rw [hdiv]
    field_simp

private lemma gamma_tendsto_correction370 {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => (z + (n : ℂ) - 1 / 2) *
      Complex.log (1 + z / (n : ℂ)) - z) atTop (𝓝 0) := by
  let K : ℝ := 3 * ‖z‖ ^ 2 + ‖z‖ / 2 + 1
  have hKpos : 0 ≤ K := by dsimp [K]; positivity
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖(z + (n : ℂ) - 1 / 2) * Complex.log (1 + z / (n : ℂ)) - z‖ ≤ K / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (max 1 (Nat.ceil (2 * ‖z‖ + 2)))] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnbig : 2 * ‖z‖ + 2 ≤ (n : ℝ) := by
      have h := le_trans (le_max_right 1 (Nat.ceil (2 * ‖z‖ + 2))) hn
      have hc := Nat.le_ceil (2 * ‖z‖ + 2)
      exact le_trans hc (by exact_mod_cast h)
    have hu : ‖z / (n : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_natCast, div_le_div_iff₀ hnpos (by norm_num)]
      nlinarith [norm_nonneg z]
    have hu1 : ‖z / (n : ℂ)‖ < 1 := by linarith
    have hE := Complex.norm_log_one_add_sub_self_le hu1
    have hsplit : (z + (n : ℂ) - 1 / 2) * Complex.log (1 + z / (n : ℂ)) - z =
        z ^ 2 / (n : ℂ) - z / (2 * (n : ℂ)) + (z + (n : ℂ) - 1 / 2) *
          (Complex.log (1 + z / (n : ℂ)) - z / (n : ℂ)) := by
      have hne : ((n : ℂ)) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (by omega : n ≠ 0)
      field_simp
      ring
    rw [hsplit]
    have hnormu : ‖z / (n : ℂ)‖ = ‖z‖ / (n : ℝ) := by
      rw [norm_div, Complex.norm_natCast]
    rw [hnormu] at hE
    have hzn : ‖z‖ / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]
      nlinarith [norm_nonneg z]
    have hEn : ‖Complex.log (1 + z / (n : ℂ)) - z / (n : ℂ)‖ ≤
        ‖z‖ ^ 2 / (n : ℝ) ^ 2 := by
      refine le_trans hE ?_
      have hinv : (1 - ‖z‖ / (n : ℝ))⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      have hsq : (0 : ℝ) ≤ (‖z‖ / (n : ℝ)) ^ 2 := by positivity
      calc (‖z‖ / (n : ℝ)) ^ 2 * (1 - ‖z‖ / (n : ℝ))⁻¹ / 2
          ≤ (‖z‖ / (n : ℝ)) ^ 2 * 2 / 2 := by gcongr
        _ = ‖z‖ ^ 2 / (n : ℝ) ^ 2 := by rw [div_pow]; ring
    have hcoef : ‖z + (n : ℂ) - 1 / 2‖ ≤ ‖z‖ + (n : ℝ) := by
      have hrw : z + (n : ℂ) - 1 / 2 = z + (((n : ℝ) - 1 / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hrw]
      refine le_trans (norm_add_le _ _) ?_
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by nlinarith [norm_nonneg z] : (0 : ℝ) ≤ (n : ℝ) - 1 / 2)]
      linarith
    have hterm1 : ‖z ^ 2 / (n : ℂ) - z / (2 * (n : ℂ))‖ ≤
        ‖z‖ ^ 2 / (n : ℝ) + ‖z‖ / (2 * (n : ℝ)) := by
      calc ‖z ^ 2 / (n : ℂ) - z / (2 * (n : ℂ))‖
          ≤ ‖z ^ 2 / (n : ℂ)‖ + ‖z / (2 * (n : ℂ))‖ := norm_sub_le _ _
        _ = ‖z‖ ^ 2 / (n : ℝ) + ‖z‖ / (2 * (n : ℝ)) := by
            rw [norm_div, norm_div, norm_pow, Complex.norm_natCast, norm_mul,
              Complex.norm_natCast]
            simp
    have hterm2 : ‖(z + (n : ℂ) - 1 / 2) *
        (Complex.log (1 + z / (n : ℂ)) - z / (n : ℂ))‖ ≤
        (‖z‖ + (n : ℝ)) * (‖z‖ ^ 2 / (n : ℝ) ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul hcoef hEn (norm_nonneg _) (by positivity)
    have hfinal : ‖z‖ ^ 2 / (n : ℝ) + ‖z‖ / (2 * (n : ℝ)) +
        (‖z‖ + (n : ℝ)) * (‖z‖ ^ 2 / (n : ℝ) ^ 2) ≤ K / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      have hexpand : (‖z‖ ^ 2 / (n : ℝ) + ‖z‖ / (2 * (n : ℝ)) +
          (‖z‖ + (n : ℝ)) * (‖z‖ ^ 2 / (n : ℝ) ^ 2)) * (n : ℝ) =
          ‖z‖ ^ 2 + ‖z‖ / 2 + ‖z‖ ^ 2 * ((‖z‖ + (n : ℝ)) / (n : ℝ)) := by
        field_simp
      rw [hexpand]
      have h2 : (‖z‖ + (n : ℝ)) / (n : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hnpos]
        nlinarith [norm_nonneg z]
      dsimp [K]
      nlinarith [sq_nonneg ‖z‖, h2, norm_nonneg z]
    calc ‖z ^ 2 / (n : ℂ) - z / (2 * (n : ℂ)) +
          (z + (n : ℂ) - 1 / 2) * (Complex.log (1 + z / (n : ℂ)) - z / (n : ℂ))‖
        ≤ ‖z ^ 2 / (n : ℂ) - z / (2 * (n : ℂ))‖ +
          ‖(z + (n : ℂ) - 1 / 2) * (Complex.log (1 + z / (n : ℂ)) - z / (n : ℂ))‖ :=
          norm_add_le _ _
      _ ≤ (‖z‖ ^ 2 / (n : ℝ) + ‖z‖ / (2 * (n : ℝ))) +
          (‖z‖ + (n : ℝ)) * (‖z‖ ^ 2 / (n : ℝ) ^ 2) :=
          add_le_add hterm1 hterm2
      _ ≤ K / (n : ℝ) := hfinal
  refine squeeze_zero_norm' hbound ?_
  simpa using (tendsto_const_div_atTop_nhds_zero_nat K)

private lemma gamma_tendsto_binetRatio370 (mainNoConst : ℂ → ℂ)
    (hmain : mainNoConst = fun z => (z - 1 / 2) * Complex.log z - z)
    {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => Complex.exp (mainNoConst (z + (n : ℂ)) -
      z * Complex.log (n : ℂ)) * (z + (n : ℂ)) / (Nat.factorial n : ℂ)) atTop
      (𝓝 (((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ))) := by
  let stirRatio : ℕ → ℝ := fun n =>
    (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) / (Nat.factorial n : ℝ)
  let binetRatio : ℂ → ℕ → ℂ := fun z n =>
    Complex.exp (mainNoConst (z + (n : ℂ)) - z * Complex.log (n : ℂ)) *
      (z + (n : ℂ)) / (Nat.factorial n : ℂ)
  change Tendsto (binetRatio z) atTop _
  have hnC {n : ℕ} (hn : 1 ≤ n) : ((n : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (by omega : n ≠ 0)
  have hfactor {n : ℕ} (hn : 1 ≤ n) : binetRatio z n =
      Complex.exp ((z + (n : ℂ) - 1 / 2) * Complex.log (1 + z / (n : ℂ)) - z) *
        ((1 + z / (n : ℂ)) * ((stirRatio n : ℝ) : ℂ)) := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnC' := hnC hn
    have hznre : 0 < (z + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hnre : 0 < ((n : ℂ)).re := by simpa using hnR
    have hquot : (z + (n : ℂ)) / (n : ℂ) = 1 + z / (n : ℂ) := by
      field_simp
      ring
    have hlog : Complex.log (z + (n : ℂ)) =
        Complex.log (n : ℂ) + Complex.log (1 + z / (n : ℂ)) := by
      have h := gamma_log_sub_log_of_re_pos370 hznre hnre
      rw [hquot] at h
      linear_combination h
    have hexp : mainNoConst (z + (n : ℂ)) - z * Complex.log (n : ℂ) =
        (((n : ℝ) - 1 / 2 : ℝ) : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ) +
          ((z + (n : ℂ) - 1 / 2) * Complex.log (1 + z / (n : ℂ)) - z) +
          (((-(n : ℝ) : ℝ)) : ℂ) := by
      have hlogc : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
        rw [show ((n : ℂ)) = (((n : ℝ) : ℝ) : ℂ) by push_cast; ring]
        exact (Complex.ofReal_log hnR.le).symm
      rw [hmain]
      dsimp only
      rw [hlog, hlogc]
      push_cast
      ring
    dsimp [binetRatio]
    rw [hexp, Complex.exp_add, Complex.exp_add]
    have hpow : Complex.exp ((((n : ℝ) - 1 / 2 : ℝ) : ℂ) *
        ((Real.log (n : ℝ) : ℝ) : ℂ)) =
        ((((n : ℝ) ^ ((n : ℝ) - 1 / 2) : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
      congr 1
      rw [Real.rpow_def_of_pos hnR]
      ring_nf
    have hem : Complex.exp ((((-(n : ℝ) : ℝ)) : ℂ)) =
        ((Real.exp (-(n : ℝ)) : ℝ) : ℂ) := (Complex.ofReal_exp _).symm
    rw [hpow, hem]
    have hzn : z + (n : ℂ) = (n : ℂ) * (1 + z / (n : ℂ)) := by
      field_simp
      ring
    have hfacC : ((Nat.factorial n : ℂ)) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (Nat.factorial_ne_zero n)
    have hstir : ((stirRatio n : ℝ) : ℂ) =
        ((((n : ℝ) ^ ((n : ℝ) - 1 / 2) : ℝ)) : ℂ) *
          ((Real.exp (-(n : ℝ)) : ℝ) : ℂ) * (n : ℂ) / (Nat.factorial n : ℂ) := by
      dsimp [stirRatio]
      have hsplit : (n : ℝ) ^ ((n : ℝ) + 1 / 2) =
          (n : ℝ) ^ ((n : ℝ) - 1 / 2) * (n : ℝ) := by
        have h := Real.rpow_add hnR ((n : ℝ) - 1 / 2) 1
        rw [Real.rpow_one] at h
        rw [show (n : ℝ) - 1 / 2 + 1 = (n : ℝ) + 1 / 2 by ring] at h
        exact h
      rw [hsplit]
      push_cast
      ring
    rw [hstir, hzn]
    field_simp
  have h1 : Tendsto (fun n : ℕ => Complex.exp ((z + (n : ℂ) - 1 / 2) *
      Complex.log (1 + z / (n : ℂ)) - z)) atTop (𝓝 1) := by
    have hcomp := (Complex.continuous_exp.continuousAt (x := (0 : ℂ))).tendsto.comp
      (gamma_tendsto_correction370 hz)
    rw [Complex.exp_zero] at hcomp
    exact hcomp
  have hz0 : Tendsto (fun n : ℕ => z / (n : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hrw : ∀ n : ℕ, ‖z / (n : ℂ)‖ = ‖z‖ / (n : ℝ) := by
      intro n
      rw [norm_div, Complex.norm_natCast]
    simp only [hrw]
    exact tendsto_const_div_atTop_nhds_zero_nat ‖z‖
  have h2 : Tendsto (fun n : ℕ => 1 + z / (n : ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hz0
  have h3 : Tendsto (fun n : ℕ => ((stirRatio n : ℝ) : ℂ)) atTop
      (𝓝 (((1 / Real.sqrt (2 * Real.pi) : ℝ)) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp gamma_tendsto_stirling_ratio370
  have hprod := h1.mul (h2.mul h3)
  simp only [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hfactor hn).symm

private lemma gamma_exp_logGammaB_eq_mul370
    (mainNoConst stirlingStep logGammaB : ℂ → ℂ)
    (hmain : mainNoConst = fun z => (z - 1 / 2) * Complex.log z - z)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    (hlog : logGammaB = fun z => mainNoConst z -
      ∑' k : ℕ, stirlingStep (z + (k : ℂ)))
    {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) {n : ℕ} (hn : 1 ≤ n) :
    Complex.exp (logGammaB z) =
      (Complex.exp (mainNoConst (z + (n : ℂ)) - z * Complex.log (n : ℂ)) *
        (z + (n : ℂ)) / (Nat.factorial n : ℂ)) *
      Complex.exp (-((∑' k : ℕ, stirlingStep (z + (k : ℂ))) -
        ∑ k ∈ Finset.range n, stirlingStep (z + (k : ℂ)))) *
      Complex.GammaSeq z n := by
  let binetRatio : ℂ → ℕ → ℂ := fun z n =>
    Complex.exp (mainNoConst (z + (n : ℂ)) - z * Complex.log (n : ℂ)) *
      (z + (n : ℂ)) / (Nat.factorial n : ℂ)
  let binetTail : ℂ → ℕ → ℂ := fun z n =>
    (∑' k : ℕ, stirlingStep (z + (k : ℂ))) -
      ∑ k ∈ Finset.range n, stirlingStep (z + (k : ℂ))
  change Complex.exp (logGammaB z) =
    binetRatio z n * Complex.exp (-binetTail z n) * Complex.GammaSeq z n
  have hnC : ((n : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (by omega : n ≠ 0)
  have hfacC : ((Nat.factorial n : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (Nat.factorial_ne_zero n)
  have hprodne : (∏ k ∈ Finset.range n, (z + (k : ℂ))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun k _ => ?_)
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hr
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hznne : z + (n : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have htele : (∑ k ∈ Finset.range n, stirlingStep (z + (k : ℂ))) =
      mainNoConst z - mainNoConst (z + (n : ℂ)) +
        ∑ k ∈ Finset.range n, Complex.log (z + (k : ℂ)) := by
    rw [hstep, hmain]
    exact gamma_sum_stirlingStep_range370 z n
  have hfin : logGammaB z = mainNoConst (z + (n : ℂ)) -
      (∑ k ∈ Finset.range n, Complex.log (z + (k : ℂ))) - binetTail z n := by
    rw [hlog]
    dsimp [binetTail]
    rw [htele]
    ring
  have hexp_sum_log : Complex.exp (∑ k ∈ Finset.range n, Complex.log (z + (k : ℂ))) =
      ∏ k ∈ Finset.range n, (z + (k : ℂ)) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    refine Complex.exp_log ?_
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hr
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  rw [hfin, Complex.exp_sub, Complex.exp_sub, hexp_sum_log]
  have hgauss : Complex.GammaSeq z n = (n : ℂ) ^ z * (Nat.factorial n : ℂ) /
      ((∏ k ∈ Finset.range n, (z + (k : ℂ))) * (z + (n : ℂ))) := by
    unfold Complex.GammaSeq
    rw [Finset.prod_range_succ]
  have hcpowne : ((n : ℂ) ^ z) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    exact Complex.exp_ne_zero _
  have hexpne : Complex.exp (binetTail z n) ≠ 0 := Complex.exp_ne_zero _
  have hratio : binetRatio z n = Complex.exp (mainNoConst (z + (n : ℂ))) *
      (z + (n : ℂ)) / ((n : ℂ) ^ z * (Nat.factorial n : ℂ)) := by
    dsimp [binetRatio]
    rw [Complex.exp_sub, Complex.cpow_def_of_ne_zero hnC,
      mul_comm (Complex.log (n : ℂ)) z]
    field_simp
  rw [hratio, hgauss, Complex.exp_neg]
  field_simp

private lemma gamma_exp_logGammaB_eq370
    (mainNoConst stirlingStep logGammaB : ℂ → ℂ)
    (hmain : mainNoConst = fun z => (z - 1 / 2) * Complex.log z - z)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    (hlog : logGammaB = fun z => mainNoConst z -
      ∑' k : ℕ, stirlingStep (z + (k : ℂ)))
    {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    Complex.exp (logGammaB z) =
      ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.Gamma z := by
  let binetRatio : ℂ → ℕ → ℂ := fun z n =>
    Complex.exp (mainNoConst (z + (n : ℂ)) - z * Complex.log (n : ℂ)) *
      (z + (n : ℂ)) / (Nat.factorial n : ℂ)
  let binetTail : ℂ → ℕ → ℂ := fun z n =>
    (∑' k : ℕ, stirlingStep (z + (k : ℂ))) -
      ∑ k ∈ Finset.range n, stirlingStep (z + (k : ℂ))
  have hsum : Summable (fun k : ℕ => stirlingStep (z + (k : ℂ))) := by
    rw [hstep]
    exact gamma_summable_stirlingStep370 hz h2
  have htail : Tendsto (binetTail z) atTop (𝓝 0) := by
    have hpart := hsum.hasSum.tendsto_sum_nat
    have hd := (tendsto_const_nhds
      (x := ∑' k : ℕ, stirlingStep (z + (k : ℂ)))).sub hpart
    rw [sub_self] at hd
    exact hd
  have hratio : Tendsto (binetRatio z) atTop
      (𝓝 (((1 / Real.sqrt (2 * Real.pi) : ℝ)) : ℂ)) := by
    simpa [binetRatio] using gamma_tendsto_binetRatio370 mainNoConst hmain hz
  have hmul {n : ℕ} (hn : 1 ≤ n) : Complex.exp (logGammaB z) =
      binetRatio z n * Complex.exp (-binetTail z n) * Complex.GammaSeq z n := by
    simpa [binetRatio, binetTail] using
      gamma_exp_logGammaB_eq_mul370 mainNoConst stirlingStep logGammaB
        hmain hstep hlog hz h2 hn
  have hlim : Tendsto (fun n : ℕ => binetRatio z n * Complex.exp (-binetTail z n) *
      Complex.GammaSeq z n) atTop
      (𝓝 ((((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) * 1 * Complex.Gamma z)) := by
    refine (hratio.mul ?_).mul (Complex.GammaSeq_tendsto_Gamma z)
    have hneg : Tendsto (fun n : ℕ => -binetTail z n) atTop (𝓝 0) := by
      have hn0 := htail.neg
      rwa [neg_zero] at hn0
    have hc := (Complex.continuous_exp.continuousAt (x := (0 : ℂ))).tendsto.comp hneg
    rw [Complex.exp_zero] at hc
    exact hc
  have hconst : Tendsto (fun _ : ℕ => Complex.exp (logGammaB z)) atTop
      (𝓝 (Complex.exp (logGammaB z))) := tendsto_const_nhds
  have hcongr : Tendsto (fun n : ℕ => binetRatio z n * Complex.exp (-binetTail z n) *
      Complex.GammaSeq z n) atTop (𝓝 (Complex.exp (logGammaB z))) := by
    refine hconst.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hmul hn
  have heq := tendsto_nhds_unique hcongr hlim
  rw [heq]
  ring

private lemma gamma_summable_stirlingStep_re_pos370
    (stirlingStep : ℂ → ℂ)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    {z : ℂ} (hz : 0 < z.re) :
    Summable (fun k : ℕ => stirlingStep (z + (k : ℂ))) := by
  rw [← summable_nat_add_iff 2]
  have h2re : 0 < (z + 2).re := by
    have h : (z + 2).re = z.re + 2 := by simp
    rw [h]
    linarith
  have hnorm : 2 ≤ ‖z + 2‖ := by
    have hre : (z + 2).re = z.re + 2 := by simp
    have h1 : (z + 2).re ≤ |(z + 2).re| := le_abs_self _
    have h2 : |(z + 2).re| ≤ ‖z + 2‖ := Complex.abs_re_le_norm _
    linarith [hre ▸ h1, h2]
  rw [hstep]
  have h := gamma_summable_stirlingStep370 h2re hnorm
  refine h.congr (fun k => ?_)
  congr 1
  push_cast
  ring

private lemma gamma_tsum_stirlingStep_eq_re_pos370
    (stirlingStep : ℂ → ℂ)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    {z : ℂ} (hz : 0 < z.re) :
    (∑' k : ℕ, stirlingStep (z + (k : ℂ))) =
      stirlingStep z + ∑' k : ℕ, stirlingStep ((z + 1) + (k : ℂ)) := by
  have hsum := gamma_summable_stirlingStep_re_pos370 stirlingStep hstep hz
  rw [hsum.tsum_eq_zero_add]
  congr 1
  · simp
  · refine tsum_congr (fun k => ?_)
    congr 1
    push_cast
    ring

private lemma gamma_logGammaB_add_one_re_pos370
    (mainNoConst stirlingStep logGammaB : ℂ → ℂ)
    (hmain : mainNoConst = fun z => (z - 1 / 2) * Complex.log z - z)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    (hlog : logGammaB = fun z => mainNoConst z -
      ∑' k : ℕ, stirlingStep (z + (k : ℂ)))
    {z : ℂ} (hz : 0 < z.re) :
    logGammaB (z + 1) = logGammaB z + Complex.log z := by
  have htsum := gamma_tsum_stirlingStep_eq_re_pos370 stirlingStep hstep hz
  have hste : stirlingStep z = mainNoConst z - mainNoConst (z + 1) + Complex.log z := by
    rw [hstep, hmain]
    ring
  rw [hlog]
  dsimp only
  rw [htsum, hste]
  ring

private lemma gamma_exp_logGammaB_re_pos370
    (mainNoConst stirlingStep logGammaB : ℂ → ℂ)
    (hmain : mainNoConst = fun z => (z - 1 / 2) * Complex.log z - z)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    (hlog : logGammaB = fun z => mainNoConst z -
      ∑' k : ℕ, stirlingStep (z + (k : ℂ)))
    {z : ℂ} (hz : 0 < z.re) :
    Complex.exp (logGammaB z) =
      ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.Gamma z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hz1re : 0 < (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hstep2 : logGammaB (z + 2) = logGammaB z + Complex.log z +
      Complex.log (z + 1) := by
    have h1 := gamma_logGammaB_add_one_re_pos370 mainNoConst stirlingStep logGammaB
      hmain hstep hlog hz
    have h2 := gamma_logGammaB_add_one_re_pos370 mainNoConst stirlingStep logGammaB
      hmain hstep hlog hz1re
    have hz2 : z + 1 + 1 = z + 2 := by ring
    rw [hz2] at h2
    rw [h2, h1]
  have h2re : 0 < (z + 2).re := by
    have h : (z + 2).re = z.re + 2 := by simp
    rw [h]
    linarith
  have hnorm : 2 ≤ ‖z + 2‖ := by
    have hre : (z + 2).re = z.re + 2 := by simp
    have h1 : (z + 2).re ≤ |(z + 2).re| := le_abs_self _
    have h2 : |(z + 2).re| ≤ ‖z + 2‖ := Complex.abs_re_le_norm _
    linarith [hre ▸ h1, h2]
  have htop := gamma_exp_logGammaB_eq370 mainNoConst stirlingStep logGammaB
    hmain hstep hlog h2re hnorm
  rw [hstep2, Complex.exp_add, Complex.exp_add, Complex.exp_log hz0,
    Complex.exp_log hz1] at htop
  have hΓ2 : Complex.Gamma (z + 2) = (z + 1) * (z * Complex.Gamma z) := by
    have hz2 : z + 2 = (z + 1) + 1 := by ring
    rw [hz2, Complex.Gamma_add_one _ hz1, Complex.Gamma_add_one _ hz0]
  rw [hΓ2] at htop
  field_simp at htop
  exact htop

private lemma gamma_continuous_logGammaB_line370
    (mainNoConst stirlingStep logGammaB : ℂ → ℂ)
    (hmain : mainNoConst = fun z => (z - 1 / 2) * Complex.log z - z)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    (hlog : logGammaB = fun z => mainNoConst z -
      ∑' k : ℕ, stirlingStep (z + (k : ℂ)))
    {c : ℝ} (hc : 0 < c) :
    Continuous (fun τ : ℝ => logGammaB ((c : ℂ) + (τ : ℂ) * Complex.I)) := by
  let lineC : ℝ → ℝ → ℂ := fun c τ => (c : ℂ) + (τ : ℂ) * Complex.I
  change Continuous (fun τ : ℝ => logGammaB (lineC c τ))
  have hcline (x : ℝ) : Continuous (lineC x) := by
    dsimp [lineC]
    fun_prop
  have hlinere (x τ : ℝ) : (lineC x τ).re = x := by simp [lineC]
  have hclog {x : ℝ} (hx : 0 < x) : Continuous (fun τ : ℝ => Complex.log (lineC x τ)) := by
    rw [continuous_iff_continuousAt]
    intro τ
    refine ContinuousAt.clog (hcline x).continuousAt ?_
    left
    rw [hlinere]
    exact hx
  have hcstep (k : ℕ) : Continuous (fun τ : ℝ => stirlingStep (lineC c τ + (k : ℂ))) := by
    have hck : 0 < c + (k : ℝ) := by positivity
    have hck1 : 0 < c + (k : ℝ) + 1 := by positivity
    have hfun : (fun τ : ℝ => stirlingStep (lineC c τ + (k : ℂ))) =
        fun τ : ℝ => 1 - (lineC (c + (k : ℝ)) τ + 1 / 2) *
          (Complex.log (lineC (c + (k : ℝ) + 1) τ) -
            Complex.log (lineC (c + (k : ℝ)) τ)) := by
      funext τ
      have h1 : lineC c τ + (k : ℂ) = lineC (c + (k : ℝ)) τ := by
        dsimp [lineC]
        push_cast
        ring
      have h2 : lineC (c + (k : ℝ)) τ + 1 = lineC (c + (k : ℝ) + 1) τ := by
        dsimp [lineC]
        push_cast
        ring
      rw [hstep]
      dsimp only
      rw [h1, h2]
    rw [hfun]
    refine continuous_const.sub (Continuous.mul ?_ ?_)
    · exact (hcline _).add continuous_const
    · exact (hclog hck1).sub (hclog hck)
  have hu : Summable (fun k : ℕ => 2 / ((k : ℝ) + 2) ^ 2) := by
    have hb : Summable (fun k : ℕ => 1 / ((k : ℝ)) ^ 2) := by
      exact_mod_cast Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hb2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2) ^ 2) := by
      have h := (summable_nat_add_iff (f := fun k : ℕ => 1 / ((k : ℝ)) ^ 2) 2).mpr hb
      refine h.congr (fun k => ?_)
      push_cast
      ring_nf
    simpa [div_eq_mul_inv, mul_comm] using hb2.mul_left 2
  have htail : Continuous (fun τ : ℝ =>
      ∑' k : ℕ, stirlingStep ((lineC c τ + 2) + (k : ℂ))) := by
    refine continuous_tsum (fun k => ?_) hu (fun k τ => ?_)
    · have hshift : ∀ τ : ℝ, lineC c τ + 2 + (k : ℂ) =
          lineC c τ + ((k + 2 : ℕ) : ℂ) := by
        intro τ
        push_cast
        ring
      simp only [hshift]
      exact hcstep (k + 2)
    · let w : ℂ := lineC c τ + 2 + (k : ℂ)
      have hwre : w.re = c + 2 + k := by
        dsimp [w]
        simp [lineC]
      have hwrepos : 0 < w.re := by rw [hwre]; positivity
      have hk2 : ((k : ℝ) + 2) ≤ ‖w‖ := by
        have h1 : w.re ≤ ‖w‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
        rw [hwre] at h1
        linarith
      have h2w : 2 ≤ ‖w‖ := by
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      calc ‖stirlingStep w‖ ≤ 2 / ‖w‖ ^ 2 := by
            rw [hstep]
            exact gamma_norm_stirlingStep_le370 hwrepos h2w
        _ ≤ 2 / ((k : ℝ) + 2) ^ 2 := by gcongr
  have hre : ∀ τ : ℝ, 0 < (lineC c τ).re := by
    intro τ
    rw [hlinere]
    exact hc
  have hre1 : ∀ τ : ℝ, 0 < (lineC c τ + 1).re := by
    intro τ
    simp only [Complex.add_re, Complex.one_re, hlinere]
    linarith
  have hpeel : ∀ τ : ℝ, logGammaB (lineC c τ) =
      mainNoConst (lineC c τ) - stirlingStep (lineC c τ) -
        stirlingStep (lineC c τ + 1) -
        ∑' k : ℕ, stirlingStep ((lineC c τ + 2) + (k : ℂ)) := by
    intro τ
    rw [hlog]
    dsimp only
    rw [gamma_tsum_stirlingStep_eq_re_pos370 stirlingStep hstep (hre τ),
      gamma_tsum_stirlingStep_eq_re_pos370 stirlingStep hstep (hre1 τ)]
    have hcast : ∀ k : ℕ, (lineC c τ + 1 + 1) + (k : ℂ) =
        (lineC c τ + 2) + (k : ℂ) := by intro k; ring
    rw [tsum_congr (fun k => by rw [hcast k])]
    ring
  simp only [hpeel]
  have hmainC : Continuous (fun τ : ℝ => mainNoConst (lineC c τ)) := by
    rw [hmain]
    refine Continuous.sub (Continuous.mul ?_ (hclog hc)) (hcline c)
    exact (hcline c).sub continuous_const
  have hs0 : Continuous (fun τ : ℝ => stirlingStep (lineC c τ)) := by
    have h := hcstep 0
    simpa using h
  have hs1 : Continuous (fun τ : ℝ => stirlingStep (lineC c τ + 1)) := by
    simpa using hcstep 1
  exact ((hmainC.sub hs0).sub hs1).sub htail

private lemma gamma_continuous_digamma_line370 {c : ℝ} (hc : 0 < c) :
    Continuous (fun t : ℝ => Complex.digamma ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  have hp {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hr := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (hp hz)).differentiableWithinAt
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply continuous_iff_continuousAt.mpr
  intro t
  let z : ℂ := (c : ℂ) + (t : ℂ) * I
  have hz : 0 < z.re := by
    dsimp [z]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    linarith
  have hg := hd.analyticAt (ho.mem_nhds hz)
  have hgc : ContinuousAt Complex.digamma z := by
    exact (hg.deriv.continuousAt.div hg.continuousAt (Complex.Gamma_ne_zero (hp hz)))
  have hf : ContinuousAt (fun u : ℝ => (c : ℂ) + (u : ℂ) * I) t := by fun_prop
  exact ContinuousAt.comp (f := fun u : ℝ => (c : ℂ) + (u : ℂ) * I) hgc hf

private lemma gamma_im_logGammaB_line370
    (mainNoConst stirlingStep logGammaB : ℂ → ℂ)
    (hmain : mainNoConst = fun z => (z - 1 / 2) * Complex.log z - z)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    (hlog : logGammaB = fun z => mainNoConst z -
      ∑' k : ℕ, stirlingStep (z + (k : ℂ)))
    {c : ℝ} (hc : 1 / 4 ≤ c) (τ : ℝ) :
    (logGammaB ((c : ℂ) + (τ : ℂ) * Complex.I)).im =
      ∫ t in (0 : ℝ)..τ, (Complex.digamma ((c : ℂ) + (t : ℂ) * Complex.I)).re := by
  let lineC : ℝ → ℝ → ℂ := fun c τ => (c : ℂ) + (τ : ℂ) * Complex.I
  change (logGammaB (lineC c τ)).im = ∫ t in (0 : ℝ)..τ, (Complex.digamma (lineC c t)).re
  let digammaLog : ℝ → ℝ → ℂ := fun c τ =>
    ∫ t in (0 : ℝ)..τ, (Complex.I * Complex.digamma (lineC c t))
  have hcpos : 0 < c := by linarith
  have hre : ∀ σ : ℝ, 0 < (lineC c σ).re := by
    intro σ
    simp [lineC, hcpos]
  have hcre : 0 < (((c : ℝ) : ℂ)).re := by simpa using hcpos
  have hcontdig : Continuous (fun t : ℝ => Complex.digamma (lineC c t)) := by
    simpa [lineC] using gamma_continuous_digamma_line370 hcpos
  have hderivLog (σ : ℝ) : HasDerivAt (digammaLog c)
      (Complex.I * Complex.digamma (lineC c σ)) σ := by
    exact ((continuous_const.mul hcontdig).integral_hasStrictDerivAt 0 σ).hasDerivAt
  have hcontLog : Continuous (digammaLog c) := by
    rw [continuous_iff_continuousAt]
    intro σ
    exact (hderivLog σ).continuousAt
  have hlineDeriv (σ : ℝ) : HasDerivAt (lineC c) Complex.I σ := by
    have h : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 σ := Complex.ofRealCLM.hasDerivAt
    simpa [lineC] using (h.mul_const Complex.I).const_add ((c : ℝ) : ℂ)
  have hgamma (σ : ℝ) : Complex.Gamma (lineC c σ) =
      Complex.Gamma ((c : ℝ) : ℂ) * Complex.exp (digammaLog c σ) := by
    have hne : ∀ u : ℝ, ∀ m : ℕ, lineC c u ≠ -(m : ℂ) := by
      intro u m heq
      have hr := congrArg Complex.re heq
      simp only [lineC, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.neg_re,
        Complex.natCast_re] at hr
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hΓd : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.Gamma (lineC c v))
        (Complex.I * deriv Complex.Gamma (lineC c u)) u := by
      intro u
      have hz : HasDerivAt Complex.Gamma (deriv Complex.Gamma (lineC c u)) (lineC c u) :=
        (Complex.differentiableAt_Gamma _ (hne u)).hasDerivAt
      exact hz.scomp u (hlineDeriv u)
    have hQ : ∀ u : ℝ, HasDerivAt ((fun v : ℝ => Complex.Gamma (lineC c v)) *
        (fun v : ℝ => Complex.exp (-1 * digammaLog c v))) 0 u := by
      intro u
      have hL := (hderivLog u).const_mul (-1 : ℂ)
      have hE := hL.cexp
      have hmul := (hΓd u).mul hE
      have hψΓ : Complex.Gamma (lineC c u) * Complex.digamma (lineC c u) =
          deriv Complex.Gamma (lineC c u) := by
        rw [Complex.digamma_def, logDeriv_apply]
        field_simp [Complex.Gamma_ne_zero (hne u)]
      have hval : Complex.I * deriv Complex.Gamma (lineC c u) *
          Complex.exp (-1 * digammaLog c u) + Complex.Gamma (lineC c u) *
          (Complex.exp (-1 * digammaLog c u) *
            (-1 * (Complex.I * Complex.digamma (lineC c u)))) = 0 := by
        rw [← hψΓ]
        ring
      rwa [hval] at hmul
    have hconst := is_const_of_deriv_eq_zero
      (fun u => (hQ u).differentiableAt) (fun u => (hQ u).deriv)
    have h0 := hconst σ 0
    simp only [Pi.mul_apply] at h0
    have hzero : digammaLog c 0 = 0 := intervalIntegral.integral_same
    rw [hzero] at h0
    have hline0 : lineC c 0 = ((c : ℝ) : ℂ) := by simp [lineC]
    rw [hline0] at h0
    simp only [mul_zero, Complex.exp_zero, mul_one] at h0
    rw [← h0, mul_assoc, ← Complex.exp_add]
    simp
  have hlogReal : (logGammaB ((c : ℝ) : ℂ)).im = 0 := by
    have hlogarg (r : ℝ) (hr : 0 < r) : (Complex.log ((r : ℂ))).im = 0 := by
      rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hr.le]
    have hmain0 : (mainNoConst ((c : ℝ) : ℂ)).im = 0 := by
      rw [hmain]
      dsimp only
      rw [Complex.sub_im, Complex.mul_im, hlogarg c hcpos]
      simp
    have hstep0 : ∀ k : ℕ, (stirlingStep (((c : ℝ) : ℂ) + (k : ℂ))).im = 0 := by
      intro k
      have hck : 0 < c + k := by positivity
      have hcast : ((c : ℝ) : ℂ) + (k : ℂ) = (((c + k : ℝ)) : ℂ) := by
        push_cast
        ring
      have hcast1 : (((c + k : ℝ)) : ℂ) + 1 = (((c + k + 1 : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hstep]
      dsimp only
      rw [hcast, hcast1, Complex.sub_im, Complex.mul_im, Complex.sub_im,
        hlogarg _ hck, hlogarg _ (by positivity : 0 < c + k + 1)]
      simp
    have hsum := gamma_summable_stirlingStep_re_pos370 stirlingStep hstep hcre
    rw [hlog]
    dsimp only
    rw [Complex.sub_im, hmain0, Complex.im_tsum hsum,
      tsum_congr hstep0, tsum_zero]
    ring
  have hbranch : logGammaB (lineC c τ) = digammaLog c τ + logGammaB ((c : ℝ) : ℂ) := by
    let g₁ : ℝ → ℂ := fun σ => logGammaB (lineC c σ)
    let g₂ : ℝ → ℂ := fun σ => digammaLog c σ + logGammaB ((c : ℝ) : ℂ)
    have hcont₁ : Continuous g₁ := by
      simpa [g₁, lineC] using gamma_continuous_logGammaB_line370
        mainNoConst stirlingStep logGammaB hmain hstep hlog hcpos
    have hcont₂ : Continuous g₂ := hcontLog.add continuous_const
    have hexp : ∀ σ : ℝ, Complex.exp (g₁ σ) = Complex.exp (g₂ σ) := by
      intro σ
      rw [show g₁ σ = logGammaB (lineC c σ) from rfl,
        show g₂ σ = digammaLog c σ + logGammaB ((c : ℝ) : ℂ) from rfl,
        gamma_exp_logGammaB_re_pos370 mainNoConst stirlingStep logGammaB
          hmain hstep hlog (hre σ),
        hgamma σ, Complex.exp_add,
        gamma_exp_logGammaB_re_pos370 mainNoConst stirlingStep logGammaB
          hmain hstep hlog hcre]
      ring
    have h0 : g₁ 0 = g₂ 0 := by
      have hzero : digammaLog c 0 = 0 := intervalIntegral.integral_same
      simp [g₁, g₂, hzero, lineC]
    have hlift := Complex.isCoveringMap_exp.eq_of_comp_eq
      (g₁ := g₁) (g₂ := g₂) hcont₁ hcont₂
      (funext fun σ => Subtype.ext (hexp σ)) 0 h0
    exact congrFun hlift τ
  rw [hbranch, Complex.add_im, hlogReal, add_zero]
  have hint : IntervalIntegrable (fun t : ℝ => Complex.I * Complex.digamma (lineC c t))
      volume 0 τ := (continuous_const.mul hcontdig).intervalIntegrable 0 τ
  have hcomm := Complex.imCLM.intervalIntegral_comp_comm hint
  change ((digammaLog c τ).im) = _
  rw [show digammaLog c τ = ∫ t in (0 : ℝ)..τ,
    Complex.I * Complex.digamma (lineC c t) from rfl]
  rw [show ((∫ t in (0 : ℝ)..τ, Complex.I * Complex.digamma (lineC c t)).im) =
    Complex.imCLM (∫ t in (0 : ℝ)..τ, Complex.I * Complex.digamma (lineC c t)) from rfl,
    ← hcomm]
  refine intervalIntegral.integral_congr fun t _ => ?_
  show (Complex.I * Complex.digamma (lineC c t)).im = (Complex.digamma (lineC c t)).re
  rw [Complex.mul_im]
  simp

private lemma gamma_stirlingStep_eq_kernel_integral370
    (stirlingStep : ℂ → ℂ)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    {w : ℂ} (hw : 0 < w.re) :
    stirlingStep w = ∫ s in (0 : ℝ)..1,
      -((s : ℂ) * (1 - (s : ℂ)) / (2 * (w + (s : ℂ)) ^ 2)) := by
  let F : ℝ → ℂ := fun s =>
    (s : ℂ) / 2 - (w + 1 / 2) * Complex.log (w + (s : ℂ)) -
      (w * (w + 1) / 2) * (w + (s : ℂ))⁻¹
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F (-((s : ℂ) * (1 - (s : ℂ)) /
        (2 * (w + (s : ℂ)) ^ 2))) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hs0 : 0 ≤ s := hs.1
    have hre : 0 < (w + (s : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have hne : w + (s : ℂ) ≠ 0 := ne_zero_of_re_pos hre
    have hslit : w + (s : ℂ) ∈ Complex.slitPlane := Or.inl hre
    have haff : HasDerivAt (fun u : ℂ => w + u) 1 (s : ℂ) :=
      (hasDerivAt_id (s : ℂ)).const_add w
    have hlogC : HasDerivAt (fun u : ℂ => Complex.log (w + u))
        (w + (s : ℂ))⁻¹ (s : ℂ) := by
      simpa [Function.comp_def] using (Complex.hasDerivAt_log hslit).comp (s : ℂ) haff
    have hlog : HasDerivAt (fun t : ℝ => Complex.log (w + (t : ℂ)))
        (w + (s : ℂ))⁻¹ s := hlogC.comp_ofReal
    have hinvC : HasDerivAt (fun u : ℂ => (w + u)⁻¹)
        (-((w + (s : ℂ)) ^ 2)⁻¹) (s : ℂ) := by
      have h := (hasDerivAt_inv hne).comp (s : ℂ) haff
      simpa [Function.comp_def] using h
    have hinv : HasDerivAt (fun t : ℝ => (w + (t : ℂ))⁻¹)
        (-((w + (s : ℂ)) ^ 2)⁻¹) s := hinvC.comp_ofReal
    have h : HasDerivAt F
        (1 / 2 - (w + 1 / 2) * (w + (s : ℂ))⁻¹ -
          (w * (w + 1) / 2) * (-((w + (s : ℂ)) ^ 2)⁻¹)) s := by
      have hsCast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
      exact ((hsCast.div_const 2).sub (hlog.const_mul (w + 1 / 2))).sub
        (hinv.const_mul (w * (w + 1) / 2))
    convert h using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun s : ℝ =>
      -((s : ℂ) * (1 - (s : ℂ)) / (2 * (w + (s : ℂ)) ^ 2)))
      (Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.neg
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      have hs0 : 0 ≤ s := hs.1
      have hre : 0 < (w + (s : ℂ)).re := by
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_zero_of_re_pos hre))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hw0 : w ≠ 0 := ne_zero_of_re_pos hw
  have hw1 : w + 1 ≠ 0 := by
    apply ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith
  simp only [F, Complex.ofReal_zero, Complex.ofReal_one, zero_div, sub_self,
    mul_zero, add_zero]
  rw [hstep]
  dsimp only
  field_simp
  ring

private lemma gamma_stirlingStep_line_im_eq370
    (stirlingStep : ℂ → ℂ)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    {c t : ℝ} (hc : 0 < c) :
    (stirlingStep ((c : ℂ) + (t : ℂ) * Complex.I)).im =
      ∫ s in (0 : ℝ)..1, s * (1 - s) * (c + s) * t /
        (((c + s) ^ 2 + t ^ 2) ^ 2) := by
  have hw : 0 < (((c : ℂ) + (t : ℂ) * Complex.I).re) := by simpa using hc
  rw [gamma_stirlingStep_eq_kernel_integral370 stirlingStep hstep hw]
  have hcont : ContinuousOn (fun s : ℝ =>
      -((s : ℂ) * (1 - (s : ℂ)) /
        (2 * (((c : ℂ) + (t : ℂ) * Complex.I) + (s : ℂ)) ^ 2)))
      (Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.neg
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      have hre : 0 < (((c : ℂ) + (t : ℂ) * Complex.I) + (s : ℂ)).re := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
          sub_zero, add_zero]
        linarith [hs.1]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_zero_of_re_pos hre))
  have hint : IntervalIntegrable (fun s : ℝ =>
      -((s : ℂ) * (1 - (s : ℂ)) /
        (2 * (((c : ℂ) + (t : ℂ) * Complex.I) + (s : ℂ)) ^ 2)))
      volume (0 : ℝ) 1 := hcont.intervalIntegrable
  change Complex.imCLM (∫ s in (0 : ℝ)..1,
    -((s : ℂ) * (1 - (s : ℂ)) /
      (2 * (((c : ℂ) + (t : ℂ) * Complex.I) + (s : ℂ)) ^ 2))) = _
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hint]
  simp only [Complex.imCLM_apply]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := by simpa using hs.1
  have hne : ((c : ℂ) + (t : ℂ) * Complex.I) + (s : ℂ) ≠ 0 := by
    apply ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    linarith
  have hxs : 0 < c + s := by linarith
  have hD : (c + s) ^ 2 + t ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hxs, sq_nonneg t]
  have hnumRe : ((s : ℂ) * (1 - (s : ℂ))).re = s * (1 - s) := by simp
  have hnumIm : ((s : ℂ) * (1 - (s : ℂ))).im = 0 := by simp
  have hz : ((c : ℂ) + (t : ℂ) * Complex.I) + (s : ℂ) = ⟨c + s, t⟩ := by
    apply Complex.ext <;> simp
  have hdenRe : (2 * (((c : ℂ) + (t : ℂ) * Complex.I) + (s : ℂ)) ^ 2).re =
      2 * ((c + s) ^ 2 - t ^ 2) := by
    rw [hz, pow_two]
    simp [Complex.mul_re]
    ring
  have hdenIm : (2 * (((c : ℂ) + (t : ℂ) * Complex.I) + (s : ℂ)) ^ 2).im =
      4 * (c + s) * t := by
    rw [hz, pow_two]
    simp [Complex.mul_im]
    ring
  have hdenNorm : Complex.normSq
      (2 * (((c : ℂ) + (t : ℂ) * Complex.I) + (s : ℂ)) ^ 2) =
      4 * (((c + s) ^ 2 + t ^ 2) ^ 2) := by
    rw [Complex.normSq_apply, hdenRe, hdenIm]
    ring
  dsimp only
  rw [Complex.neg_im, Complex.div_im, hnumRe, hnumIm, hdenRe, hdenIm, hdenNorm]
  field_simp [hD]
  ring

private lemma gamma_stirlingStep_line_im_bounds370
    (stirlingStep : ℂ → ℂ)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    0 ≤ (stirlingStep ((c : ℂ) + (t : ℂ) * Complex.I)).im ∧
      (stirlingStep ((c : ℂ) + (t : ℂ) * Complex.I)).im ≤
        t / 8 * (1 / (c ^ 2 + t ^ 2) - 1 / ((c + 1) ^ 2 + t ^ 2)) := by
  let f : ℝ → ℝ := fun s => s * (1 - s) * (c + s) * t / (((c + s) ^ 2 + t ^ 2) ^ 2)
  let g : ℝ → ℝ := fun s => (1 / 4 : ℝ) * (c + s) * t / (((c + s) ^ 2 + t ^ 2) ^ 2)
  have hf : IntervalIntegrable f volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro s
      have hden : 0 < (c + s) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (c + s), sq_pos_of_pos ht]
      exact pow_ne_zero 2 hden.ne'
  have hg : IntervalIntegrable g volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro s
      have hden : 0 < (c + s) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (c + s), sq_pos_of_pos ht]
      exact pow_ne_zero 2 hden.ne'
  have hf_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f s := by
    intro s hs
    dsimp [f]
    have hs0 : 0 ≤ s := hs.1
    have hsle : s ≤ 1 := hs.2
    have hs1 : 0 ≤ 1 - s := by linarith
    have hxs : 0 < c + s := by linarith
    positivity
  have hfg : ∀ s ∈ Set.Icc (0 : ℝ) 1, f s ≤ g s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hsle : s ≤ 1 := hs.2
    have hsQuarter : s * (1 - s) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (s - 1 / 2)]
    have hxs : 0 < c + s := by linarith
    have hden : 0 < ((c + s) ^ 2 + t ^ 2) ^ 2 := by positivity
    dsimp [f, g]
    have hfactor : 0 ≤ (c + s) * t / (((c + s) ^ 2 + t ^ 2) ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hsQuarter hfactor
    calc s * (1 - s) * (c + s) * t / (((c + s) ^ 2 + t ^ 2) ^ 2) =
        (s * (1 - s)) * ((c + s) * t / (((c + s) ^ 2 + t ^ 2) ^ 2)) := by ring
      _ ≤ (1 / 4 : ℝ) * ((c + s) * t / (((c + s) ^ 2 + t ^ 2) ^ 2)) := hmul
      _ = (1 / 4 : ℝ) * (c + s) * t / (((c + s) ^ 2 + t ^ 2) ^ 2) := by ring
  have hzero : 0 ≤ ∫ s in (0 : ℝ)..1, f s :=
    intervalIntegral.integral_nonneg (by norm_num) hf_nonneg
  have hmono : (∫ s in (0 : ℝ)..1, f s) ≤ ∫ s in (0 : ℝ)..1, g s :=
    intervalIntegral.integral_mono_on (by norm_num) hf hg hfg
  have hgIntegral : (∫ s in (0 : ℝ)..1, g s) =
      t / 8 * (1 / (c ^ 2 + t ^ 2) - 1 / ((c + 1) ^ 2 + t ^ 2)) := by
    let F : ℝ → ℝ := fun s => (-t / 8) * (((c + s) ^ 2 + t ^ 2)⁻¹)
    have hderiv : ∀ s : ℝ, HasDerivAt F (g s) s := by
      intro s
      have hinner : HasDerivAt (fun u : ℝ => (c + u) ^ 2 + t ^ 2) (2 * (c + s)) s := by
        have h := (((hasDerivAt_id s).const_add c).pow 2).add_const (t ^ 2)
        simpa [Function.id_def, mul_comm] using h
      have hne : (c + s) ^ 2 + t ^ 2 ≠ 0 := by
        have h : 0 < (c + s) ^ 2 + t ^ 2 := by
          nlinarith [sq_nonneg (c + s), sq_pos_of_pos ht]
        exact h.ne'
      have h := (hinner.inv hne).const_mul (-t / 8)
      have h' : HasDerivAt F ((-t / 8) * (-(2 * (c + s)) /
        ((c + s) ^ 2 + t ^ 2) ^ 2)) s := by
        simpa [F, Function.comp_def] using h
      refine h'.congr_deriv ?_
      dsimp [g]
      field_simp [hne]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hg]
    dsimp [F]
    have h0 : c ^ 2 + t ^ 2 ≠ 0 := by positivity
    have h1 : (c + 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
    field_simp [h0, h1]
    ring
  rw [gamma_stirlingStep_line_im_eq370 stirlingStep hstep hc]
  change 0 ≤ ∫ s in (0 : ℝ)..1, f s ∧
    (∫ s in (0 : ℝ)..1, f s) ≤
      t / 8 * (1 / (c ^ 2 + t ^ 2) - 1 / ((c + 1) ^ 2 + t ^ 2))
  exact ⟨hzero, hmono.trans_eq hgIntegral⟩

private lemma gamma_hasSum_stepImagUpper370
    (stirlingStep : ℂ → ℂ)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasSum (fun k : ℕ => t / 8 *
      (1 / ((c + (k : ℝ)) ^ 2 + t ^ 2) -
        1 / ((c + (k : ℝ) + 1) ^ 2 + t ^ 2)))
      (t / 8 * (1 / (c ^ 2 + t ^ 2))) := by
  have hnonneg : ∀ k : ℕ, 0 ≤ t / 8 *
      (1 / ((c + (k : ℝ)) ^ 2 + t ^ 2) -
        1 / ((c + (k : ℝ) + 1) ^ 2 + t ^ 2)) := by
    intro k
    have hx : 0 < c + (k : ℝ) := by positivity
    have hb := gamma_stirlingStep_line_im_bounds370 stirlingStep hstep hx ht
    exact hb.1.trans hb.2
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hpartial : ∀ N : ℕ, (∑ k ∈ Finset.range N, t / 8 *
      (1 / ((c + (k : ℝ)) ^ 2 + t ^ 2) -
        1 / ((c + (k : ℝ) + 1) ^ 2 + t ^ 2))) =
      t / 8 * (1 / (c ^ 2 + t ^ 2) - 1 / ((c + (N : ℝ)) ^ 2 + t ^ 2)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [show (fun N : ℕ => ∑ k ∈ Finset.range N, t / 8 *
      (1 / ((c + (k : ℝ)) ^ 2 + t ^ 2) -
        1 / ((c + (k : ℝ) + 1) ^ 2 + t ^ 2))) =
      fun N : ℕ => t / 8 * (1 / (c ^ 2 + t ^ 2) -
        1 / ((c + (N : ℝ)) ^ 2 + t ^ 2)) by
    funext N
    exact hpartial N]
  have hshift : Tendsto (fun N : ℕ => c + (N : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun N : ℕ => (c + (N : ℝ)) ^ 2 + t ^ 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (t ^ 2)
      ((Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hshift)
  have hinv : Tendsto (fun N : ℕ => 1 / ((c + (N : ℝ)) ^ 2 + t ^ 2)) atTop (𝓝 0) := by
    refine hden.inv_tendsto_atTop.congr ?_
    intro N
    simp [one_div]
  have hsub : Tendsto (fun N : ℕ => 1 / (c ^ 2 + t ^ 2) -
      1 / ((c + (N : ℝ)) ^ 2 + t ^ 2)) atTop
      (𝓝 (1 / (c ^ 2 + t ^ 2) - 0)) := tendsto_const_nhds.sub hinv
  have hmul : Tendsto (fun N : ℕ => t / 8 * (1 / (c ^ 2 + t ^ 2) -
      1 / ((c + (N : ℝ)) ^ 2 + t ^ 2))) atTop
      (𝓝 (t / 8 * (1 / (c ^ 2 + t ^ 2) - 0))) := hsub.const_mul (t / 8)
  simpa only [sub_zero] using hmul

private lemma gamma_tsum_stirlingStep_line_im_bounds370
    (stirlingStep : ℂ → ℂ)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    0 ≤ ∑' k : ℕ, (stirlingStep (((c : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ))).im ∧
      (∑' k : ℕ, (stirlingStep (((c : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ))).im) ≤
        t / 8 * (1 / (c ^ 2 + t ^ 2)) := by
  have hre : 0 < (((c : ℂ) + (t : ℂ) * Complex.I).re) := by simpa using hc
  have hsumC := gamma_summable_stirlingStep_re_pos370 stirlingStep hstep hre
  have hsumIm : Summable (fun k : ℕ =>
      (stirlingStep (((c : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ))).im) := by
    have h := hsumC.map Complex.imCLM Complex.imCLM.continuous
    refine h.congr (fun k => ?_)
    rfl
  have hupper := gamma_hasSum_stepImagUpper370 stirlingStep hstep hc ht
  have hnonneg : ∀ k : ℕ,
      0 ≤ (stirlingStep (((c : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ))).im := by
    intro k
    have heq : ((c : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ) =
        (((c + (k : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [heq]
    exact (gamma_stirlingStep_line_im_bounds370 stirlingStep hstep
      (by positivity : 0 < c + (k : ℝ)) ht).1
  have hle : ∀ k : ℕ,
      (stirlingStep (((c : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ))).im ≤
        t / 8 * (1 / ((c + (k : ℝ)) ^ 2 + t ^ 2) -
          1 / ((c + (k : ℝ) + 1) ^ 2 + t ^ 2)) := by
    intro k
    have heq : ((c : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ) =
        (((c + (k : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [heq]
    exact (gamma_stirlingStep_line_im_bounds370 stirlingStep hstep
      (by positivity : 0 < c + (k : ℝ)) ht).2
  refine ⟨tsum_nonneg hnonneg, ?_⟩
  have hcmp := Summable.tsum_le_tsum hle hsumIm hupper.summable
  rw [hupper.tsum_eq] at hcmp
  exact hcmp

private lemma gamma_abs_logGammaB_sub_mainNoConst_im_le370
    (mainNoConst stirlingStep logGammaB : ℂ → ℂ)
    (hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
      (Complex.log (z + 1) - Complex.log z))
    (hlog : logGammaB = fun z => mainNoConst z -
      ∑' k : ℕ, stirlingStep (z + (k : ℂ)))
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    |(logGammaB ((c : ℂ) + (t : ℂ) * Complex.I) -
      mainNoConst ((c : ℂ) + (t : ℂ) * Complex.I)).im| ≤
        t / 8 * (1 / (c ^ 2 + t ^ 2)) := by
  have hbounds := gamma_tsum_stirlingStep_line_im_bounds370 stirlingStep hstep hc ht
  have hre : 0 < (((c : ℂ) + (t : ℂ) * Complex.I).re) := by simpa using hc
  have hsumC := gamma_summable_stirlingStep_re_pos370 stirlingStep hstep hre
  have him : (logGammaB ((c : ℂ) + (t : ℂ) * Complex.I) -
      mainNoConst ((c : ℂ) + (t : ℂ) * Complex.I)).im =
      -(∑' k : ℕ, (stirlingStep (((c : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ))).im) := by
    rw [hlog]
    dsimp only
    rw [Complex.sub_im, Complex.sub_im, Complex.im_tsum hsumC]
    ring
  rw [him, abs_neg, abs_of_nonneg hbounds.1]
  exact hbounds.2

/-- LEAF. Explicit Stirling remainder for the continuous Gamma phase.
Trudgian page 3, displays 2.4 and 2.5, scaled by twice the reciprocal of pi.
This isolates the analytic remainder before the elementary norm rounding.
-/
theorem gamma_stirling_raw370 {a T : ℝ} (ha : a = 0 ∨ a = 1) (hT : 1 ≤ T) :
    |gammaPhase370 a T - T / Real.pi * Real.log (T / (2 * Real.exp 1)) -
      2 / Real.pi * gammaCorrection370 a T| ≤
        1 / (3 * Real.pi * ‖(((1 / 4 + a / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)‖) := by
  have ha0 : 0 ≤ a := by rcases ha with rfl | rfl <;> norm_num
  let mainNoConst : ℂ → ℂ := fun z => (z - 1 / 2) * Complex.log z - z
  let stirlingStep : ℂ → ℂ := fun z =>
    1 - (z + 1 / 2) * (Complex.log (z + 1) - Complex.log z)
  let logGammaB : ℂ → ℂ := fun z => mainNoConst z -
    ∑' k : ℕ, stirlingStep (z + (k : ℂ))
  have hmain : mainNoConst = fun z => (z - 1 / 2) * Complex.log z - z := rfl
  have hstep : stirlingStep = fun z => 1 - (z + 1 / 2) *
    (Complex.log (z + 1) - Complex.log z) := rfl
  have hlog : logGammaB = fun z => mainNoConst z -
    ∑' k : ℕ, stirlingStep (z + (k : ℂ)) := rfl
  let c : ℝ := 1 / 4 + a / 2
  let t : ℝ := T / 2
  let z : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
  have hc : 1 / 4 ≤ c := by dsimp [c]; linarith
  have hcpos : 0 < c := by linarith
  have ht : 0 < t := by dsimp [t]; linarith
  have hphase : gammaPhase370 a T = 2 / Real.pi * (logGammaB z).im := by
    unfold gammaPhase370
    change 2 / Real.pi * (∫ u in (0 : ℝ)..T / 2,
      (Complex.digamma (((1 / 4 + a / 2 : ℝ) : ℂ) + (u : ℂ) * I)).re) = _
    rw [gamma_im_logGammaB_line370 mainNoConst stirlingStep logGammaB
      hmain hstep hlog hc t]
  have hmainid := gamma_mainNoConst_im370 ha0 (by linarith : 0 < T) z rfl
  have htail := gamma_abs_logGammaB_sub_mainNoConst_im_le370
    mainNoConst stirlingStep logGammaB hstep hlog hcpos ht
  have hrewrite : gammaPhase370 a T - T / Real.pi * Real.log (T / (2 * Real.exp 1)) -
      2 / Real.pi * gammaCorrection370 a T =
      2 / Real.pi * ((logGammaB z - mainNoConst z).im) := by
    rw [hphase]
    calc 2 / Real.pi * (logGammaB z).im -
        T / Real.pi * Real.log (T / (2 * Real.exp 1)) -
          2 / Real.pi * gammaCorrection370 a T =
        2 / Real.pi * (logGammaB z).im - 2 / Real.pi * (mainNoConst z).im := by
          linear_combination hmainid
      _ = 2 / Real.pi * ((logGammaB z - mainNoConst z).im) := by
          dsimp [logGammaB]
          rw [Complex.sub_im]
          ring
  rw [hrewrite, abs_mul, abs_of_nonneg (show 0 ≤ 2 / Real.pi by positivity)]
  have hsq : c ^ 2 + t ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply]
    ring
  have him_norm : t ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    simpa [z, abs_of_nonneg ht.le] using h
  have hnpos : 0 < ‖z‖ := ht.trans_le him_norm
  calc 2 / Real.pi * |(logGammaB z - mainNoConst z).im|
      ≤ 2 / Real.pi * (t / 8 * (1 / (c ^ 2 + t ^ 2))) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = t / (4 * Real.pi * ‖z‖ ^ 2) := by
        rw [← hsq]
        field_simp [Real.pi_ne_zero, hnpos.ne']
        ring
    _ ≤ 1 / (3 * Real.pi * ‖z‖) := by
        rw [div_le_div_iff₀ (by positivity : 0 < 4 * Real.pi * ‖z‖ ^ 2)
          (by positivity : 0 < 3 * Real.pi * ‖z‖)]
        have hm := mul_le_mul_of_nonneg_left him_norm
          (show 0 ≤ 3 * Real.pi * ‖z‖ by positivity)
        nlinarith [sq_nonneg ‖z‖, Real.pi_pos]
/-- The Gamma argument norm is at least half the height, giving the rounded remainder.
Trudgian page 3, displays 2.4 and 2.5. CONDITIONAL ON gamma_stirling_raw370.
-/
theorem gamma_stirling_remainder370 {a T : ℝ} (ha : a = 0 ∨ a = 1) (hT : 1 ≤ T) :
    |gammaPhase370 a T - T / Real.pi * Real.log (T / (2 * Real.exp 1)) -
      2 / Real.pi * gammaCorrection370 a T| ≤ 2 / (3 * Real.pi * T) := by
  let z : ℂ := ((1 / 4 + a / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I
  have hn : T / 2 ≤ ‖z‖ := by
    have hh := Complex.abs_im_le_norm z
    simpa [z, abs_of_nonneg (show 0 ≤ T / 2 by linarith)] using hh
  have ht0 : 0 < T := by linarith
  have hn0 : 0 < ‖z‖ := by linarith
  have hb : 1 / (3 * Real.pi * ‖z‖) ≤ 2 / (3 * Real.pi * T) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 3 * Real.pi * ‖z‖)
      (by positivity : 0 < 3 * Real.pi * T)]
    nlinarith [mul_nonneg (show 0 ≤ 3 * Real.pi by positivity)
      (show 0 ≤ 2 * ‖z‖ - T by linarith)]
  exact (gamma_stirling_raw370 ha hT).trans hb

/-- The Stirling remainder and elementary correction fit within the Gamma budget.
Trudgian page 3, displays 2.4 to 2.6. CONDITIONAL ON gamma_stirling_remainder370.
-/
theorem gamma_phase_error370 {a T : ℝ} (ha : a = 0 ∨ a = 1) (hT : 1 ≤ T) :
    |gammaPhase370 a T - T / Real.pi * Real.log (T / (2 * Real.exp 1))| ≤ 2 := by
  have ha0 : 0 ≤ a := by rcases ha with rfl | rfl <;> norm_num
  have ha1 : a ≤ 1 := by rcases ha with rfl | rfl <;> norm_num
  have hc := gamma_correction_bound370 ha0 ha1 hT
  have hr := gamma_stirling_remainder370 ha hT
  have hcoef : 0 ≤ 2 / Real.pi := by positivity
  have hscale : |2 / Real.pi * gammaCorrection370 a T| ≤
      2 / Real.pi * (9 / 16 + Real.pi / 8) := by
    rw [abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left hc hcoef
  have hsum := (abs_sub_abs_le_abs_sub (gammaPhase370 a T -
    T / Real.pi * Real.log (T / (2 * Real.exp 1)))
    (2 / Real.pi * gammaCorrection370 a T))
  have htail : 2 / (3 * Real.pi * T) ≤ 2 / (3 * Real.pi) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [Real.pi_pos]
  have hbudget : 2 / (3 * Real.pi) + 2 / Real.pi * (9 / 16 + Real.pi / 8) ≤ 2 := by
    field_simp
    nlinarith [Real.pi_gt_three]
  linarith

private lemma LFunction_star_conj370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction (star χ) (starRingEnd ℂ s) =
      starRingEnd ℂ (DirichletCharacter.LFunction χ s) := by
  have hstar : star χ ≠ 1 := by
    rw [MulChar.star_eq_inv]
    exact inv_ne_one.mpr hne
  have hf_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction (star χ)) Set.univ :=
    (DirichletCharacter.differentiable_LFunction hstar).differentiableOn.analyticOnNhd isOpen_univ
  have hg_an : AnalyticOnNhd ℂ
      (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ => (differentiableAt_conj_conj_iff.mpr
        (DirichletCharacter.differentiable_LFunction hne (starRingEnd ℂ z))).differentiableWithinAt)
      isOpen_univ
  have hgz (z : ℂ) (hz : 1 < z.re) :
      starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)) =
        DirichletCharacter.LFunction (star χ) z := by
    rw [DirichletCharacter.LFunction_eq_LSeries (star χ) hz,
      DirichletCharacter.LFunction_eq_LSeries χ (by rwa [Complex.conj_re]),
      LSeries, LSeries, conj_tsum]
    refine tsum_congr (fun n => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      ← conj_cpow _ _ (by rw [Complex.natCast_arg]; positivity), conj_natCast]
    congr 1
  have heq : Set.EqOn (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)))
      (DirichletCharacter.LFunction (star χ)) Set.univ := by
    refine hg_an.eqOn_of_preconnected_of_eventuallyEq hf_an isPreconnected_univ (Set.mem_univ 2) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hgz z hz
  have h := heq (Set.mem_univ (starRingEnd ℂ s))
  simp only [Complex.conj_conj] at h
  exact h.symm

private lemma gammaFactor_ne_zero370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [hχ.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith

private lemma completedLFunction_eq_LFunction_mul_gammaFactor370
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hN : q ≠ 1) (hΓ : DirichletCharacter.gammaFactor χ s ≠ 0) :
    DirichletCharacter.completedLFunction χ s = DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN), div_mul_cancel₀ _ hΓ]

private lemma rootNumber_ne_zero370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    DirichletCharacter.rootNumber χ ≠ 0 := by
  have hN : q ≠ 1 := by
    intro hN1
    cases hN1
    exact hne (Subsingleton.elim _ _)
  intro hRoot
  have hFE : ∀ s : ℂ, DirichletCharacter.completedLFunction χ (1 - s) = 0 := by
    intro s
    rw [hχ.completedLFunction_one_sub s, hRoot]
    ring
  have hZero2 : DirichletCharacter.completedLFunction χ (2 : ℂ) = 0 := by
    have h := hFE (-1)
    convert h using 2 <;> ring
  have hL_ne : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
    norm_num
  have hΓ_ne : DirichletCharacter.gammaFactor χ (2 : ℂ) ≠ 0 := gammaFactor_ne_zero370 χ (by norm_num)
  have hLam_ne : DirichletCharacter.completedLFunction χ (2 : ℂ) ≠ 0 := by
    rw [completedLFunction_eq_LFunction_mul_gammaFactor370 χ hN hΓ_ne]
    exact mul_ne_zero hL_ne hΓ_ne
  exact hLam_ne hZero2

private lemma completedLFunction_star_conj370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction (star χ) (starRingEnd ℂ s) =
      starRingEnd ℂ (DirichletCharacter.completedLFunction χ s) := by
  have hstar : star χ ≠ 1 := by
    rw [MulChar.star_eq_inv]
    exact inv_ne_one.mpr hne
  have hN : q ≠ 1 := by
    intro hN1
    cases hN1
    exact hne (Subsingleton.elim _ _)
  have hf_an : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction (star χ)) Set.univ :=
    (DirichletCharacter.differentiable_completedLFunction hstar).differentiableOn.analyticOnNhd
      isOpen_univ
  have hg_an : AnalyticOnNhd ℂ
      (fun z => starRingEnd ℂ (DirichletCharacter.completedLFunction χ (starRingEnd ℂ z)))
      Set.univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ => (differentiableAt_conj_conj_iff.mpr
        (DirichletCharacter.differentiable_completedLFunction hne
          (starRingEnd ℂ z))).differentiableWithinAt)
      isOpen_univ
  have hgz (z : ℂ) (hz : 1 < z.re) :
      DirichletCharacter.completedLFunction (star χ) z =
        starRingEnd ℂ (DirichletCharacter.completedLFunction χ (starRingEnd ℂ z)) := by
    have hz0 : 0 < z.re := by linarith
    have hcz : 1 < (starRingEnd ℂ z).re := by rwa [Complex.conj_re]
    have hΓ1 : DirichletCharacter.gammaFactor (star χ) z ≠ 0 :=
      gammaFactor_ne_zero370 (star χ) hz0
    have hΓ2 : DirichletCharacter.gammaFactor χ (starRingEnd ℂ z) ≠ 0 :=
      gammaFactor_ne_zero370 χ (by rw [Complex.conj_re]; linarith)
    rw [completedLFunction_eq_LFunction_mul_gammaFactor370 (star χ) hN hΓ1,
      completedLFunction_eq_LFunction_mul_gammaFactor370 χ hN hΓ2, map_mul]
    congr 1
    · have h := LFunction_star_conj370 χ hne (starRingEnd ℂ z)
      rwa [Complex.conj_conj] at h
    · rcases χ.even_or_odd with hpar | hpar
      · have hp : (star χ).Even := by
          unfold DirichletCharacter.Even at hpar ⊢
          simp [MulChar.star_apply, hpar]
        rw [hpar.gammaFactor_def, hp.gammaFactor_def, Gammaℝ_conj, Complex.conj_conj]
      · have hp : (star χ).Odd := by
          unfold DirichletCharacter.Odd at hpar ⊢
          simp [MulChar.star_apply, hpar]
        rw [hpar.gammaFactor_def, hp.gammaFactor_def]
        have hc : starRingEnd ℂ z + 1 = starRingEnd ℂ (z + 1) := by rw [map_add, map_one]
        rw [hc, Gammaℝ_conj, Complex.conj_conj]
  have hev : DirichletCharacter.completedLFunction (star χ) =ᶠ[nhds (2 : ℂ)]
      fun z => starRingEnd ℂ (DirichletCharacter.completedLFunction χ (starRingEnd ℂ z)) := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
    exact hgz w hw
  have hEq : Set.EqOn (DirichletCharacter.completedLFunction (star χ))
      (fun z => starRingEnd ℂ (DirichletCharacter.completedLFunction χ (starRingEnd ℂ z)))
      Set.univ :=
    hf_an.eqOn_of_preconnected_of_eventuallyEq hg_an isPreconnected_univ
      (Set.mem_univ (2 : ℂ)) hev
  have h := hEq (Set.mem_univ (starRingEnd ℂ s))
  simp only [Complex.conj_conj] at h
  exact h

private lemma logDeriv_completedLFunction_star_conj370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (DirichletCharacter.completedLFunction (star χ)) (starRingEnd ℂ s) =
      starRingEnd ℂ (logDeriv (DirichletCharacter.completedLFunction χ) s) := by
  have hd : deriv (DirichletCharacter.completedLFunction (star χ)) (starRingEnd ℂ s) =
      starRingEnd ℂ (deriv (DirichletCharacter.completedLFunction χ) s) := by
    have hfun : DirichletCharacter.completedLFunction (star χ) =
        fun z => starRingEnd ℂ (DirichletCharacter.completedLFunction χ (starRingEnd ℂ z)) := by
      funext z
      have h := completedLFunction_star_conj370 χ hne (starRingEnd ℂ z)
      rwa [Complex.conj_conj] at h
    rw [hfun]
    exact deriv_conj_conj' (DirichletCharacter.completedLFunction χ) s
  rw [logDeriv_apply, logDeriv_apply, hd, completedLFunction_star_conj370 χ hne s]
  exact (map_div₀ (starRingEnd ℂ) _ _).symm

private lemma logDeriv_completedLFunction_one_sub370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ}
    (hΛ : DirichletCharacter.completedLFunction (star χ) s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) (1 - s) =
      -((Real.log (q : ℝ) : ℝ) : ℂ) -
        logDeriv (DirichletCharacter.completedLFunction (star χ)) s := by
  have hstar : star χ ≠ 1 := by
    rw [MulChar.star_eq_inv]
    exact inv_ne_one.mpr hne
  have hfe : (fun w : ℂ => DirichletCharacter.completedLFunction χ (1 - w)) =
      fun w : ℂ => (q : ℂ) ^ (w - 1 / 2) *
        (DirichletCharacter.rootNumber χ * DirichletCharacter.completedLFunction (star χ) w) := by
    funext w
    have h := hχ.completedLFunction_one_sub w
    rw [show χ⁻¹ = star χ from (MulChar.star_eq_inv χ).symm] at h
    rw [h]
    ring
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hrn : DirichletCharacter.rootNumber χ ≠ 0 := rootNumber_ne_zero370 hχ hne
  have hpow : (q : ℂ) ^ (s - 1 / 2) ≠ 0 := by
    apply cpow_ne_zero_iff.mpr
    left
    exact hq0
  have hcast : ((q : ℝ) : ℂ) = (q : ℂ) := by push_cast; rfl
  have hlogq : Complex.log ((q : ℂ)) = ((Real.log (q : ℝ) : ℝ) : ℂ) := by
    rw [← hcast]
    exact (Complex.ofReal_log (by linarith : (0 : ℝ) ≤ (q : ℝ))).symm
  have hd1 : HasDerivAt (fun w : ℂ => DirichletCharacter.completedLFunction χ (1 - w))
      (deriv (DirichletCharacter.completedLFunction χ) (1 - s) * (-1)) s := by
    have h := (DirichletCharacter.differentiable_completedLFunction hne (1 - s)).hasDerivAt
    exact h.comp s ((hasDerivAt_id s).const_sub 1)
  have hdpow : HasDerivAt (fun w : ℂ => (q : ℂ) ^ (w - 1 / 2))
      ((q : ℂ) ^ (s - 1 / 2) * Complex.log (q : ℂ)) s := by
    have h := ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_cpow (Or.inl hq0)
    simpa using h
  have hdΛ : HasDerivAt (fun w : ℂ => DirichletCharacter.rootNumber χ *
      DirichletCharacter.completedLFunction (star χ) w)
      (DirichletCharacter.rootNumber χ *
        deriv (DirichletCharacter.completedLFunction (star χ)) s) s :=
    ((DirichletCharacter.differentiable_completedLFunction hstar s).hasDerivAt).const_mul
      (DirichletCharacter.rootNumber χ)
  have hd2 : HasDerivAt (fun w : ℂ => (q : ℂ) ^ (w - 1 / 2) *
      (DirichletCharacter.rootNumber χ * DirichletCharacter.completedLFunction (star χ) w))
      ((q : ℂ) ^ (s - 1 / 2) * Complex.log (q : ℂ) *
          (DirichletCharacter.rootNumber χ * DirichletCharacter.completedLFunction (star χ) s) +
        (q : ℂ) ^ (s - 1 / 2) *
          (DirichletCharacter.rootNumber χ *
            deriv (DirichletCharacter.completedLFunction (star χ)) s)) s := hdpow.mul hdΛ
  have hd1' : HasDerivAt (fun w : ℂ => (q : ℂ) ^ (w - 1 / 2) *
      (DirichletCharacter.rootNumber χ * DirichletCharacter.completedLFunction (star χ) w))
      (deriv (DirichletCharacter.completedLFunction χ) (1 - s) * (-1)) s := by
    rw [← hfe]
    exact hd1
  have huniq := hd1'.unique hd2
  have hval : DirichletCharacter.completedLFunction χ (1 - s) =
      (q : ℂ) ^ (s - 1 / 2) *
        (DirichletCharacter.rootNumber χ * DirichletCharacter.completedLFunction (star χ) s) :=
    congrFun hfe s
  rw [logDeriv_apply, logDeriv_apply, hval]
  have hnum : deriv (DirichletCharacter.completedLFunction χ) (1 - s) =
      -((q : ℂ) ^ (s - 1 / 2) * Complex.log (q : ℂ) *
          (DirichletCharacter.rootNumber χ * DirichletCharacter.completedLFunction (star χ) s) +
        (q : ℂ) ^ (s - 1 / 2) *
          (DirichletCharacter.rootNumber χ *
            deriv (DirichletCharacter.completedLFunction (star χ)) s)) := by
    linear_combination -huniq
  rw [hnum, hlogq]
  have key : ∀ P L E Λ0 Λ1 : ℂ, P ≠ 0 → E ≠ 0 → Λ0 ≠ 0 →
      -(P * L * (E * Λ0) + P * (E * Λ1)) / (P * (E * Λ0)) = -L - Λ1 / Λ0 := by
    intro P L E Λ0 Λ1 hP hE hΛ0
    field_simp
    ring
  exact key _ _ _ _ _ hpow hrn hΛ

private lemma logDeriv_completedLFunction_one_sub_conj370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {w : ℂ}
    (hΛ : DirichletCharacter.completedLFunction χ w ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) (1 - starRingEnd ℂ w) =
      -((Real.log (q : ℝ) : ℝ) : ℂ) -
        starRingEnd ℂ (logDeriv (DirichletCharacter.completedLFunction χ) w) := by
  have hΛ' : DirichletCharacter.completedLFunction (star χ) (starRingEnd ℂ w) ≠ 0 := by
    rw [completedLFunction_star_conj370 χ hne w]
    simpa using hΛ
  rw [logDeriv_completedLFunction_one_sub370 hχ hne hΛ',
    logDeriv_completedLFunction_star_conj370 χ hne w]

private lemma differentiableAt_Gammaℝ370 {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  unfold Complex.Gammaℝ
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hp := ((hasDerivAt_id s).neg.div_const 2).const_cpow (Or.inl hpi)
  have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m heq
    have hr := congrArg Complex.re heq
    simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re,
      Complex.div_ofNat_re] at hr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num at hr
    linarith
  have hdG := (Complex.differentiableAt_Gamma (s / 2) hne).hasDerivAt.comp s
    ((hasDerivAt_id s).div_const 2)
  exact hp.differentiableAt.mul hdG.differentiableAt

private lemma analyticAt_LFunction370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    AnalyticAt ℂ (DirichletCharacter.LFunction χ) s :=
  (DirichletCharacter.differentiable_LFunction hne).differentiableOn.analyticOnNhd
    isOpen_univ s (Set.mem_univ s)

private lemma analyticAt_completedLFunction370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) s :=
  (DirichletCharacter.differentiable_completedLFunction hne).differentiableOn.analyticOnNhd
    isOpen_univ s (Set.mem_univ s)

private lemma analyticAt_gammaFactor370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  rcases χ.even_or_odd with hχ | hχ
  · have hfun : DirichletCharacter.gammaFactor χ = Gammaℝ :=
      funext fun z => hχ.gammaFactor_def z
    have hdiff : DifferentiableOn ℂ (DirichletCharacter.gammaFactor χ) {w : ℂ | 0 < w.re} := by
      rw [hfun]
      intro w hw
      exact (differentiableAt_Gammaℝ370 hw).differentiableWithinAt
    exact (hdiff.analyticOnNhd hopen) s hs
  · have hfun : DirichletCharacter.gammaFactor χ = fun z : ℂ => Gammaℝ (z + 1) :=
      funext fun z => hχ.gammaFactor_def z
    have hdiff : DifferentiableOn ℂ (DirichletCharacter.gammaFactor χ) {w : ℂ | 0 < w.re} := by
      rw [hfun]
      intro w hw
      have hwre : 0 < w.re := hw
      have hG : DifferentiableAt ℂ Gammaℝ (w + 1) :=
        differentiableAt_Gammaℝ370 (by simp only [Complex.add_re, Complex.one_re]; linarith)
      exact (hG.comp w (differentiableAt_id.add_const 1)).differentiableWithinAt
    exact (hdiff.analyticOnNhd hopen) s hs

private lemma completedLFunction_ne_zero_of_one_le_re370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith
  have hN : q ≠ 1 := by
    intro hN1
    cases hN1
    exact hne (Subsingleton.elim _ _)
  have hΓ : DirichletCharacter.gammaFactor χ s ≠ 0 := gammaFactor_ne_zero370 χ hs0
  have hL : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hs
  rw [completedLFunction_eq_LFunction_mul_gammaFactor370 χ hN hΓ]
  exact mul_ne_zero hL hΓ

private lemma completedLFunction_ne_zero_of_re_nonpos370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {s : ℂ} (hs : s.re ≤ 0) : DirichletCharacter.completedLFunction χ s ≠ 0 := by
  intro hzero
  let t : ℂ := 1 - s
  have ht_re : 1 ≤ t.re := by change 1 ≤ 1 - s.re; linarith
  have hFE := hχ.completedLFunction_one_sub t
  have h1mt : (1 : ℂ) - t = s := by dsimp [t]; ring
  rw [h1mt, hzero] at hFE
  have hpow : (q : ℂ) ^ (t - 1 / 2) ≠ 0 := by
    apply cpow_ne_zero_iff.mpr
    left
    exact_mod_cast NeZero.ne q
  have hrn : DirichletCharacter.rootNumber χ ≠ 0 := rootNumber_ne_zero370 hχ hne
  have hΛinv : DirichletCharacter.completedLFunction χ⁻¹ t = 0 := by
    rcases mul_eq_zero.mp hFE.symm with h | h
    · rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd h1 hpow
      · exact absurd h2 hrn
    · exact h
  exact completedLFunction_ne_zero_of_one_le_re370 χ⁻¹ (inv_ne_one.mpr hne) ht_re hΛinv

private lemma completedLFunction_zero_re_mem_strip370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {ρ : ℂ} (hzero : DirichletCharacter.completedLFunction χ ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra h
    exact completedLFunction_ne_zero_of_re_nonpos370 hχ hne (le_of_not_gt h) hzero
  · by_contra h
    exact completedLFunction_ne_zero_of_one_le_re370 χ hne (le_of_not_gt h) hzero

private lemma completedLFunction_zero_iff370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ s = 0 ↔
      DirichletCharacter.LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  have hN : q ≠ 1 := by
    intro hN1
    cases hN1
    exact hne (Subsingleton.elim _ _)
  constructor
  · intro hzero
    obtain ⟨hre0, hre1⟩ := completedLFunction_zero_re_mem_strip370 hχ hne hzero
    have hL : DirichletCharacter.LFunction χ s = 0 := by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN),
        hzero, zero_div]
    exact ⟨hL, hre0, hre1⟩
  · rintro ⟨hL, hre0, hre1⟩
    have hΓ : DirichletCharacter.gammaFactor χ s ≠ 0 :=
      gammaFactor_ne_zero370 χ (by linarith)
    rw [completedLFunction_eq_LFunction_mul_gammaFactor370 χ hN hΓ, hL, zero_mul]

private lemma completedLFunction_mem_LZeros370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (s : ℂ) :
    (DirichletCharacter.completedLFunction χ s = 0 ∧ |s.im| ≤ T) ↔ s ∈ LZeros χ T := by
  rw [completedLFunction_zero_iff370 hχ hne]
  constructor
  · rintro ⟨⟨hL, hre0, hre1⟩, hT⟩
    exact ⟨hL, hre0, hre1, hT⟩
  · rintro ⟨hL, hre0, hre1, hT⟩
    exact ⟨⟨hL, hre0, hre1⟩, hT⟩

private lemma analyticOrderAt_LFunction_ne_top370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (ρ : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
  intro htop
  have hev : ∀ᶠ z in nhds ρ, DirichletCharacter.LFunction χ z = 0 :=
    analyticOrderAt_eq_top.mp htop
  have hEq : Set.EqOn (DirichletCharacter.LFunction χ) 0 (Set.univ : Set ℂ) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => analyticAt_LFunction370 χ hne z)
      isPreconnected_univ (Set.mem_univ ρ) hev
  have h2 : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by norm_num)
  exact h2 (hEq (Set.mem_univ (2 : ℂ)))

private lemma analyticOrderAt_completedLFunction_eq370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {ρ : ℂ} (hre : 0 < ρ.re) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ =
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
  have hN : q ≠ 1 := by
    intro hN1
    cases hN1
    exact hne (Subsingleton.elim _ _)
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[nhds ρ]
      (DirichletCharacter.LFunction χ * DirichletCharacter.gammaFactor χ) := by
    filter_upwards [hopen.mem_nhds hre] with w hw
    have hΓ : DirichletCharacter.gammaFactor χ w ≠ 0 := gammaFactor_ne_zero370 χ hw
    exact completedLFunction_eq_LFunction_mul_gammaFactor370 χ hN hΓ
  have hΓρ : DirichletCharacter.gammaFactor χ ρ ≠ 0 := gammaFactor_ne_zero370 χ hre
  have hΓan : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) ρ :=
    analyticAt_gammaFactor370 χ hre
  have hLan : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    analyticAt_LFunction370 χ hne ρ
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hLan hΓan,
    hΓan.analyticOrderAt_eq_zero.mpr hΓρ, add_zero]

private lemma analyticOrderAt_completedLFunction_ne_top370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {ρ : ℂ} (hre : 0 < ρ.re) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ ⊤ := by
  rw [analyticOrderAt_completedLFunction_eq370 χ hne hre]
  exact analyticOrderAt_LFunction_ne_top370 χ hne ρ

private lemma analyticOrderNatAt_completedLFunction_eq_LMult370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {ρ : ℂ} (hre : 0 < ρ.re) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ = LMult χ ρ := by
  unfold LMult analyticOrderNatAt
  rw [analyticOrderAt_completedLFunction_eq370 χ hne hre]

private lemma analyticOrderAt_completedLFunction_ne_top_univ370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (ρ : ℂ) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ ⊤ := by
  intro htop
  have hev : ∀ᶠ z in nhds ρ, DirichletCharacter.completedLFunction χ z = 0 :=
    analyticOrderAt_eq_top.mp htop
  have hEq : Set.EqOn (DirichletCharacter.completedLFunction χ) 0 (Set.univ : Set ℂ) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => analyticAt_completedLFunction370 χ hne z)
      isPreconnected_univ (Set.mem_univ ρ) hev
  have h2 : DirichletCharacter.completedLFunction χ (2 : ℂ) ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re370 χ hne (by norm_num)
  exact h2 (hEq (Set.mem_univ (2 : ℂ)))

private lemma completedLFunction_ne_zero_on_border370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ}
    (hT : 0 ≤ T) (hgood : ∀ ρ ∈ LZeros χ T, ρ.im ≠ T ∧ ρ.im ≠ -T)
    {z : ℂ} (hz : z ∈ RectangleBorder (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ)) :
    DirichletCharacter.completedLFunction χ z ≠ 0 := by
  intro hzero
  have hre := completedLFunction_zero_re_mem_strip370 hχ hne hzero
  have hxrect := rectangleBorder_subset_rectangle (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ) hz
  have him : |z.im| ≤ T := by
    apply abs_le.mpr
    rw [mem_Rect (by norm_num) (by linarith)] at hxrect
    exact ⟨hxrect.2.2.1, hxrect.2.2.2⟩
  have hxL : z ∈ LZeros χ T := (completedLFunction_mem_LZeros370 hχ hne z).mp ⟨hzero, him⟩
  obtain ⟨⟨h | h⟩ | h⟩ | h := hz
  · have himEq : z.im = -T := by simpa using h.2
    exact (hgood z hxL).2 himEq
  · have hreEq : z.re = -1 := by simpa using h.1
    linarith [hre.1]
  · have himEq : z.im = T := by simpa using h.2
    exact (hgood z hxL).1 himEq
  · have hreEq : z.re = 2 := by simpa using h.1
    linarith [hre.2]

private lemma rectangle_winding370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ}
    (hT : 0 ≤ T)
    (hgood : ∀ ρ ∈ LZeros χ T, ρ.im ≠ T ∧ ρ.im ≠ -T)
    (hfin : (LZeros χ T).Finite) :
    RectangleIntegral' (logDeriv (DirichletCharacter.completedLFunction χ))
      (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ) =
      ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℂ) := by
  classical
  let R : Set ℂ := Rectangle (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ)
  let P : Finset ℂ := hfin.toFinset
  have horder (z : ℂ) : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) z =
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z : ℤ) := by
    have htop := analyticOrderAt_completedLFunction_ne_top_univ370 χ hne z
    rw [(analyticAt_completedLFunction370 χ hne z).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [analyticOrderNatAt, ← hn, ENat.toNat_natCast]
    simp
  have hmero (z : ℂ) : MeromorphicAt (logDeriv (DirichletCharacter.completedLFunction χ)) z := by
    exact (analyticAt_completedLFunction370 χ hne z).meromorphicAt.deriv.div
      (analyticAt_completedLFunction370 χ hne z).meromorphicAt
  have hsimple : HasSimplePolesOn (logDeriv (DirichletCharacter.completedLFunction χ)) R := by
    intro z hz
    by_cases ho : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) z = 0
    · exact (WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by norm_num)).trans
        (meromorphicOrderAt_logDeriv_nonneg
          (analyticAt_completedLFunction370 χ hne z).meromorphicAt ho)
    · rw [meromorphicOrderAt_logDeriv_eq_neg_one
        (analyticAt_completedLFunction370 χ hne z).meromorphicAt ho (by rw [horder z]; simp)]
      norm_num
  have hpole_mem {z : ℂ} (hzR : z ∈ R) (hp : meromorphicOrderAt
      (logDeriv (DirichletCharacter.completedLFunction χ)) z < 0) : z ∈ LZeros χ T := by
    have hzero : DirichletCharacter.completedLFunction χ z = 0 := by
      by_contra hn
      have ho : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) z = 0 := by
        rw [(analyticAt_completedLFunction370 χ hne z).meromorphicOrderAt_eq,
          analyticOrderAt_eq_zero.mpr (Or.inr hn)]
        simp
      exact (not_lt_of_ge (meromorphicOrderAt_logDeriv_nonneg
        (analyticAt_completedLFunction370 χ hne z).meromorphicAt ho)) hp
    have him : |z.im| ≤ T := by
      apply abs_le.mpr
      have hzR' := hzR
      change z ∈ Rectangle (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ) at hzR'
      rw [mem_Rect (by norm_num) (by linarith)] at hzR'
      exact ⟨hzR'.2.2.1, hzR'.2.2.2⟩
    exact (completedLFunction_mem_LZeros370 hχ hne z).mp ⟨hzero, him⟩
  have hzRe : (-1 : ℝ) ≤ 2 := by norm_num
  have hzIm : -T ≤ T := by linarith
  have hres := RectangleIntegral'_eq_sumResiduesIn
    (f := logDeriv (DirichletCharacter.completedLFunction χ))
    (z := (⟨-1, -T⟩ : ℂ)) (w := (⟨2, T⟩ : ℂ)) hzRe hzIm
    (fun z _ => hmero z)
    (by
      apply Set.disjoint_left.mpr
      intro z hz hp
      have ho : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) z = 0 := by
        rw [(analyticAt_completedLFunction370 χ hne z).meromorphicOrderAt_eq,
          analyticOrderAt_eq_zero.mpr
            (Or.inr (completedLFunction_ne_zero_on_border370 hχ hne hT hgood hz))]
        simp
      exact (not_lt_of_ge (meromorphicOrderAt_logDeriv_nonneg
        (analyticAt_completedLFunction370 χ hne z).meromorphicAt ho)) hp)
    (by
      apply hfin.subset
      intro z hz
      exact hpole_mem hz.1 hz.2)
    hsimple
  change RectangleIntegral' (logDeriv (DirichletCharacter.completedLFunction χ))
    (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ) = _
  rw [hres]
  have hS : R ∩ {z | meromorphicOrderAt (logDeriv (DirichletCharacter.completedLFunction χ)) z < 0} =
      (P : Set ℂ) ∩ {z | meromorphicOrderAt (logDeriv (DirichletCharacter.completedLFunction χ)) z < 0} := by
    ext z
    constructor
    · rintro ⟨hzR, hp⟩
      have hzL := hpole_mem hzR hp
      exact ⟨hfin.mem_toFinset.mpr hzL, hp⟩
    · rintro ⟨hzP, hp⟩
      have hzL := hfin.mem_toFinset.mp hzP
      have hz0 : 0 < z.re := hzL.2.1
      have hz1 : z.re < 1 := hzL.2.2.1
      have him := abs_le.mp hzL.2.2.2
      have hzR : z ∈ Rectangle (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ) := by
        rw [mem_Rect (by norm_num) (by linarith)]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      exact ⟨hzR, hp⟩
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (hmero z) (not_lt.mp hz))]
  rw [sumResiduesIn, Finset.tsum_subtype' P (fun z => residue
    (logDeriv (DirichletCharacter.completedLFunction χ)) z)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hzL := hfin.mem_toFinset.mp hρ
  have hre : 0 < ρ.re := hzL.2.1
  have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
    (completedLFunction_zero_iff370 hχ hne ρ).mpr ⟨hzL.1, hzL.2.1, hzL.2.2.1⟩
  have hord : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) ρ = (LMult χ ρ : ℤ) := by
    rw [horder ρ, analyticOrderNatAt_completedLFunction_eq_LMult370 χ hne hre]
  apply residue_eq_of_tendsto
  simpa only [logDeriv_apply, Int.cast_natCast] using
    (LeanLab.PNTPort.ExplicitPsi1.tendsto_mul_logDeriv_mero
      (analyticAt_completedLFunction370 χ hne ρ).meromorphicAt hord)

private lemma completedLFunction_ne_zero_of_goodHeight370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ}
    (hT : 0 ≤ T) (hgood : ∀ ρ ∈ LZeros χ T, ρ.im ≠ T ∧ ρ.im ≠ -T)
    {s : ℂ} (him : s.im = T ∨ s.im = -T) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  intro hz
  have hzL : s ∈ LZeros χ T := by
    apply (completedLFunction_mem_LZeros370 hχ hne s).mp
    refine ⟨hz, ?_⟩
    rcases him with h | h
    · rw [h, abs_of_nonneg hT]
    · rw [h, abs_neg, abs_of_nonneg hT]
  rcases him with h | h
  · exact (hgood s hzL).1 h
  · exact (hgood s hzL).2 h

private lemma continuousAt_logDeriv_completedLFunction370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {s : ℂ}
    (hs : DirichletCharacter.completedLFunction χ s ≠ 0) :
    ContinuousAt (logDeriv (DirichletCharacter.completedLFunction χ)) s := by
  have hA := analyticAt_completedLFunction370 χ hne s
  exact hA.deriv.continuousAt.div hA.continuousAt hs

private lemma continuous_logDeriv_completed_vertical370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {c : ℝ}
    (hnz : ∀ y : ℝ, DirichletCharacter.completedLFunction χ ((c : ℂ) + (y : ℂ) * I) ≠ 0) :
    Continuous (fun y : ℝ => logDeriv (DirichletCharacter.completedLFunction χ)
      ((c : ℂ) + (y : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hline : Continuous fun y : ℝ => (c : ℂ) + (y : ℂ) * I := by fun_prop
  exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.completedLFunction χ))
    (f := fun y : ℝ => (c : ℂ) + (y : ℂ) * I) (x := y)
    (continuousAt_logDeriv_completedLFunction370 χ hne (hnz y)) hline.continuousAt

private lemma continuous_logDeriv_completed_horizontal370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {c : ℝ}
    (hnz : ∀ x : ℝ, DirichletCharacter.completedLFunction χ ((x : ℂ) + (c : ℂ) * I) ≠ 0) :
    Continuous (fun x : ℝ => logDeriv (DirichletCharacter.completedLFunction χ)
      ((x : ℂ) + (c : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hline : Continuous fun x : ℝ => (x : ℂ) + (c : ℂ) * I := by fun_prop
  exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.completedLFunction χ))
    (f := fun x : ℝ => (x : ℂ) + (c : ℂ) * I) (x := x)
    (continuousAt_logDeriv_completedLFunction370 χ hne (hnz x)) hline.continuousAt

private lemma point_conj370 (x c : ℝ) :
    (x : ℂ) + ((-c : ℝ) : ℂ) * I = starRingEnd ℂ ((x : ℂ) + (c : ℂ) * I) := by
  apply Complex.ext <;> simp

private lemma point_fe_horizontal370 (σ c : ℝ) :
    ((1 - σ : ℝ) : ℂ) + (c : ℂ) * I =
      1 - starRingEnd ℂ ((σ : ℂ) + (c : ℂ) * I) := by
  apply Complex.ext <;> simp

private lemma point_fe_vertical370 (y : ℝ) :
    ((-1 : ℝ) : ℂ) + (y : ℂ) * I =
      1 - starRingEnd ℂ (((2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  apply Complex.ext <;> simp <;> norm_num

private lemma logDeriv_completedLFunction_conj'370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (DirichletCharacter.completedLFunction χ) (starRingEnd ℂ s) =
      starRingEnd ℂ (logDeriv (DirichletCharacter.completedLFunction (star χ)) s) := by
  have hstar : star χ ≠ 1 := by
    rw [MulChar.star_eq_inv]
    exact inv_ne_one.mpr hne
  have h := logDeriv_completedLFunction_star_conj370 (star χ) hstar s
  rwa [star_star] at h

private lemma boundary_fold370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ}
    (hT : 0 < T) (hgood : ∀ ρ ∈ LZeros χ T, ρ.im ≠ T ∧ ρ.im ≠ -T) :
    Real.pi * (RectangleIntegral' (logDeriv (DirichletCharacter.completedLFunction χ))
      (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ)).re =
      ((∫ t in (0 : ℝ)..T, (logDeriv (DirichletCharacter.completedLFunction χ)
          (2 + (t : ℂ) * I) * I).im) -
        ∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * I)).im) +
      ((∫ t in (0 : ℝ)..T, (logDeriv (DirichletCharacter.completedLFunction (star χ))
          (2 + (t : ℂ) * I) * I).im) -
        ∫ σ in (1 / 2 : ℝ)..2, (logDeriv (DirichletCharacter.completedLFunction (star χ))
          ((σ : ℂ) + (T : ℂ) * I)).im) + T * Real.log (q : ℝ) := by
  have hstar : star χ ≠ 1 := by
    rw [MulChar.star_eq_inv]
    exact inv_ne_one.mpr hne
  set F := logDeriv (DirichletCharacter.completedLFunction χ) with hF_def
  set G := logDeriv (DirichletCharacter.completedLFunction (star χ)) with hG_def
  set Lq : ℂ := ((Real.log (q : ℝ) : ℝ) : ℂ) with hLq_def
  set A : ℂ := ∫ σ in (1 / 2 : ℝ)..2, F ((σ : ℂ) + (T : ℂ) * I) with hA_def
  set A' : ℂ := ∫ σ in (1 / 2 : ℝ)..2, G ((σ : ℂ) + (T : ℂ) * I) with hA'_def
  set B : ℂ := ∫ y in (0 : ℝ)..T, F (((2 : ℝ) : ℂ) + (y : ℂ) * I) with hB_def
  set B' : ℂ := ∫ y in (0 : ℝ)..T, G (((2 : ℝ) : ℂ) + (y : ℂ) * I) with hB'_def
  have hne_right : ∀ y : ℝ,
      DirichletCharacter.completedLFunction χ (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y
    apply completedLFunction_ne_zero_of_one_le_re370 χ hne
    simp
  have hne_right' : ∀ y : ℝ,
      DirichletCharacter.completedLFunction (star χ) (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y
    apply completedLFunction_ne_zero_of_one_le_re370 (star χ) hstar
    simp
  have hne_top : ∀ x : ℝ,
      DirichletCharacter.completedLFunction χ ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro x
    exact completedLFunction_ne_zero_of_goodHeight370 hχ hne hT.le hgood (Or.inl (by simp))
  have hne_bot : ∀ x : ℝ,
      DirichletCharacter.completedLFunction χ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0 := by
    intro x
    exact completedLFunction_ne_zero_of_goodHeight370 hχ hne hT.le hgood (Or.inr (by simp))
  have hne_top' : ∀ x : ℝ,
      DirichletCharacter.completedLFunction (star χ) ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro x
    have hc := completedLFunction_star_conj370 χ hne
      (starRingEnd ℂ ((x : ℂ) + (T : ℂ) * I))
    simp only [Complex.conj_conj] at hc
    rw [hc]
    intro h
    have h2 : DirichletCharacter.completedLFunction χ (starRingEnd ℂ
        ((x : ℂ) + (T : ℂ) * I)) = 0 := by
      have hh := congrArg (starRingEnd ℂ) h
      rwa [Complex.conj_conj, map_zero] at hh
    rw [← point_conj370 x T] at h2
    exact hne_bot x h2
  have hint_right : ∀ a b : ℝ, IntervalIntegrable
      (fun y : ℝ => F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) volume a b :=
    fun a b => (continuous_logDeriv_completed_vertical370 χ hne hne_right).intervalIntegrable a b
  have hint_right' : ∀ a b : ℝ, IntervalIntegrable
      (fun y : ℝ => G (((2 : ℝ) : ℂ) + (y : ℂ) * I)) volume a b :=
    fun a b => (continuous_logDeriv_completed_vertical370 (star χ) hstar hne_right').intervalIntegrable a b
  have hint_top : ∀ a b : ℝ, IntervalIntegrable
      (fun x : ℝ => F ((x : ℂ) + (T : ℂ) * I)) volume a b :=
    fun a b => (continuous_logDeriv_completed_horizontal370 χ hne hne_top).intervalIntegrable a b
  have hint_top' : ∀ a b : ℝ, IntervalIntegrable
      (fun x : ℝ => G ((x : ℂ) + (T : ℂ) * I)) volume a b :=
    fun a b => (continuous_logDeriv_completed_horizontal370 (star χ) hstar hne_top').intervalIntegrable a b
  have hcont_conj_top : Continuous fun σ : ℝ => starRingEnd ℂ (F ((σ : ℂ) + (T : ℂ) * I)) :=
    Complex.continuous_conj.comp (continuous_logDeriv_completed_horizontal370 χ hne hne_top)
  have hcont_conj_right : Continuous fun y : ℝ =>
      starRingEnd ℂ (F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    Complex.continuous_conj.comp (continuous_logDeriv_completed_vertical370 χ hne hne_right)
  have hTopL : (∫ x in (-1 : ℝ)..(1 / 2 : ℝ), F ((x : ℂ) + (T : ℂ) * I)) =
      -(3 / 2 : ℂ) * Lq - starRingEnd ℂ A := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (a := (1 / 2 : ℝ)) (b := 2)
      (fun x : ℝ => F ((x : ℂ) + (T : ℂ) * I)) 1
    have hb : (1 : ℝ) - 2 = -1 := by norm_num
    have ha : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hb, ha] at hsub
    rw [← hsub]
    have hpt : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
        F (((1 - σ : ℝ) : ℂ) + (T : ℂ) * I) =
          -Lq - starRingEnd ℂ (F ((σ : ℂ) + (T : ℂ) * I)) := by
      intro σ _
      rw [point_fe_horizontal370 σ T, hF_def, hLq_def]
      exact logDeriv_completedLFunction_one_sub_conj370 hχ hne (hne_top σ)
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const
      (hcont_conj_top.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, intervalIntegral_conj, ← hA_def]
    have hsm : ((2 : ℝ) - 1 / 2) • (-Lq) = -(3 / 2 : ℂ) * Lq := by
      rw [Complex.real_smul]
      push_cast
      ring
    rw [hsm]
  have hTop : (∫ x in (-1 : ℝ)..2, F ((x : ℂ) + (T : ℂ) * I)) =
      A - starRingEnd ℂ A - (3 / 2 : ℂ) * Lq := by
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (a := (-1 : ℝ)) (b := (1 / 2 : ℝ)) (c := 2)
      (hint_top (-1) (1 / 2)) (hint_top (1 / 2) 2)
    rw [← hadj, hTopL, ← hA_def]
    ring
  have hBotR : (∫ x in (1 / 2 : ℝ)..2, F ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) =
      starRingEnd ℂ A' := by
    rw [hA'_def, ← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro x _
    show F ((x : ℂ) + ((-T : ℝ) : ℂ) * I) =
      starRingEnd ℂ (G ((x : ℂ) + (T : ℂ) * I))
    rw [point_conj370 x T, hF_def, hG_def, logDeriv_completedLFunction_conj'370 χ hne]
  have hBotL : (∫ x in (-1 : ℝ)..(1 / 2 : ℝ),
      F ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) = -(3 / 2 : ℂ) * Lq - A' := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (a := (1 / 2 : ℝ)) (b := 2)
      (fun x : ℝ => F ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) 1
    have hb : (1 : ℝ) - 2 = -1 := by norm_num
    have ha : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hb, ha] at hsub
    rw [← hsub]
    have hpt : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
        F (((1 - σ : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) =
          -Lq - G ((σ : ℂ) + (T : ℂ) * I) := by
      intro σ _
      have hfold : F (((1 - σ : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) =
          -Lq - starRingEnd ℂ (F ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
        rw [point_fe_horizontal370 σ (-T), hF_def, hLq_def]
        exact logDeriv_completedLFunction_one_sub_conj370 hχ hne (hne_bot σ)
      rw [hfold]
      congr 1
      rw [point_conj370 σ T, hF_def, hG_def,
        logDeriv_completedLFunction_conj'370 χ hne, Complex.conj_conj]
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const
      (hint_top' (1 / 2) 2)]
    rw [intervalIntegral.integral_const, ← hA'_def]
    have hsm : ((2 : ℝ) - 1 / 2) • (-Lq) = -(3 / 2 : ℂ) * Lq := by
      rw [Complex.real_smul]
      push_cast
      ring
    rw [hsm]
  have hBot : (∫ x in (-1 : ℝ)..2, F ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) =
      starRingEnd ℂ A' - A' - (3 / 2 : ℂ) * Lq := by
    have hintF_bot : ∀ a b : ℝ, IntervalIntegrable
        (fun x : ℝ => F ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) volume a b :=
      fun a b => (continuous_logDeriv_completed_horizontal370 χ hne hne_bot).intervalIntegrable a b
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (a := (-1 : ℝ)) (b := (1 / 2 : ℝ)) (c := 2)
      (hintF_bot (-1) (1 / 2)) (hintF_bot (1 / 2) 2)
    rw [← hadj, hBotL, hBotR]
    ring
  have hRlow : (∫ y in (-T : ℝ)..0, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      starRingEnd ℂ B' := by
    have hsub := intervalIntegral.integral_comp_neg
      (a := (0 : ℝ)) (b := T)
      (fun y : ℝ => F (((2 : ℝ) : ℂ) + (y : ℂ) * I))
    rw [neg_zero] at hsub
    rw [← hsub, hB'_def, ← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro y _
    show F (((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) =
      starRingEnd ℂ (G (((2 : ℝ) : ℂ) + (y : ℂ) * I))
    rw [point_conj370 2 y, hF_def, hG_def, logDeriv_completedLFunction_conj'370 χ hne]
  have hR : (∫ y in (-T : ℝ)..T, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      starRingEnd ℂ B' + B := by
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (a := (-T : ℝ)) (b := (0 : ℝ)) (c := T)
      (hint_right (-T) 0) (hint_right 0 T)
    rw [← hadj, hRlow, ← hB_def]
  have hL : (∫ y in (-T : ℝ)..T, F (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -(2 * (T : ℂ)) * Lq - B' - starRingEnd ℂ B := by
    have hpt : ∀ y ∈ Set.uIcc (-T : ℝ) T,
        F (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
          -Lq - starRingEnd ℂ (F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) := by
      intro y _
      rw [point_fe_vertical370 y, hF_def, hLq_def]
      exact logDeriv_completedLFunction_one_sub_conj370 hχ hne (hne_right y)
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const
      (hcont_conj_right.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, intervalIntegral_conj, hR]
    have hsm : ((T : ℝ) - (-T)) • (-Lq) = -(2 * (T : ℂ)) * Lq := by
      rw [Complex.real_smul]
      push_cast
      ring
    rw [hsm, map_add, Complex.conj_conj]
    ring
  have hwind : RectangleIntegral' F (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ) =
      (1 / (2 * (Real.pi : ℂ) * I)) *
        ((starRingEnd ℂ A - A) + (starRingEnd ℂ A' - A') +
          I * (B + starRingEnd ℂ B) + I * (B' + starRingEnd ℂ B') +
          2 * (T : ℂ) * Lq * I) := by
    change (1 / (2 * (Real.pi : ℂ) * I)) • RectangleIntegral F
      (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ) = _
    unfold RectangleIntegral HIntegral VIntegral
    simp only [smul_eq_mul]
    rw [hBot, hL, hTop, hR]
    ring
  have hπ0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hcoef : (1 / (2 * (Real.pi : ℂ) * I)) =
      ((-(1 / (2 * Real.pi)) : ℝ) : ℂ) * I := by
    rw [div_eq_iff (by simp [Complex.I_ne_zero, hπ0] :
      (2 * (Real.pi : ℂ) * I) ≠ 0)]
    push_cast
    rw [show ((-(1 / (2 * Real.pi)) : ℂ) * I * (2 * (Real.pi : ℂ) * I)) =
        -(1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)) * (I * I) by ring]
    rw [Complex.I_mul_I]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hπ0
    field_simp
  have hre : (RectangleIntegral' F (⟨-1, -T⟩ : ℂ) (⟨2, T⟩ : ℂ)).re =
      (1 / (2 * Real.pi)) * (2 * B.re + 2 * B'.re - 2 * A.im - 2 * A'.im +
        2 * T * Real.log (q : ℝ)) := by
    rw [hwind, hcoef]
    set Y : ℂ := (starRingEnd ℂ A - A) + (starRingEnd ℂ A' - A') +
      I * (B + starRingEnd ℂ B) + I * (B' + starRingEnd ℂ B') +
      2 * (T : ℂ) * Lq * I with hY_def
    have hLq_re : Lq.re = Real.log (q : ℝ) := by rw [hLq_def]; exact Complex.ofReal_re _
    have hLq_im : Lq.im = 0 := by rw [hLq_def]; exact Complex.ofReal_im _
    have hYim : Y.im = 2 * B.re + 2 * B'.re - 2 * A.im - 2 * A'.im +
        2 * T * Real.log (q : ℝ) := by
      rw [hY_def]
      simp [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.sub_re,
        Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
        Complex.I_im, Complex.add_re, hLq_re, hLq_im]
      ring
    have hmul : ((((-(1 / (2 * Real.pi)) : ℝ) : ℂ) * I) * Y).re =
        (-(1 / (2 * Real.pi))) * (-Y.im) := by
      rw [mul_assoc]
      rw [show (((-(1 / (2 * Real.pi)) : ℝ) : ℂ) * (I * Y)).re =
          (-(1 / (2 * Real.pi))) * (I * Y).re by
        rw [Complex.mul_re]
        simp]
      rw [Complex.I_mul_re]
    rw [hmul, hYim]
    ring
  have hBre : B.re = ∫ t in (0 : ℝ)..T,
      (logDeriv (DirichletCharacter.completedLFunction χ) (2 + (t : ℂ) * I) * I).im := by
    rw [hB_def]
    have h1 := Complex.reCLM.intervalIntegral_comp_comm (hint_right 0 T)
    have h2 : (∫ y in (0 : ℝ)..T, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re =
        ∫ y in (0 : ℝ)..T, (F (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re := by
      simpa using h1.symm
    rw [h2]
    apply intervalIntegral.integral_congr
    intro t _
    show (F (((2 : ℝ) : ℂ) + (t : ℂ) * I)).re =
      (logDeriv (DirichletCharacter.completedLFunction χ) (2 + (t : ℂ) * I) * I).im
    rw [Complex.mul_I_im, hF_def]
    norm_num
  have hB're : B'.re = ∫ t in (0 : ℝ)..T,
      (logDeriv (DirichletCharacter.completedLFunction (star χ)) (2 + (t : ℂ) * I) * I).im := by
    rw [hB'_def]
    have h1 := Complex.reCLM.intervalIntegral_comp_comm (hint_right' 0 T)
    have h2 : (∫ y in (0 : ℝ)..T, G (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re =
        ∫ y in (0 : ℝ)..T, (G (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re := by
      simpa using h1.symm
    rw [h2]
    apply intervalIntegral.integral_congr
    intro t _
    show (G (((2 : ℝ) : ℂ) + (t : ℂ) * I)).re =
      (logDeriv (DirichletCharacter.completedLFunction (star χ)) (2 + (t : ℂ) * I) * I).im
    rw [Complex.mul_I_im, hG_def]
    norm_num
  have hAim : A.im = ∫ σ in (1 / 2 : ℝ)..2,
      (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im := by
    rw [hA_def]
    have h1 := Complex.imCLM.intervalIntegral_comp_comm (hint_top (1 / 2) 2)
    simpa using h1.symm
  have hA'im : A'.im = ∫ σ in (1 / 2 : ℝ)..2,
      (logDeriv (DirichletCharacter.completedLFunction (star χ)) ((σ : ℂ) + (T : ℂ) * I)).im := by
    rw [hA'_def]
    have h1 := Complex.imCLM.intervalIntegral_comp_comm (hint_top' (1 / 2) 2)
    simpa using h1.symm
  rw [hre]
  dsimp [F, G]
  rw [← hBre, ← hAim, ← hB're, ← hA'im]
  field_simp
  ring

private lemma analyticAt_digamma370 {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.digamma s := by
  have hp {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hr := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (hp hz)).differentiableWithinAt
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hg := hd.analyticAt (ho.mem_nhds hs)
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (hp hs)
  have hld : AnalyticAt ℂ (fun w => deriv Complex.Gamma w / Complex.Gamma w) s :=
    hg.deriv.div hg hΓ
  change AnalyticAt ℂ (fun w => deriv Complex.Gamma w / Complex.Gamma w) s
  exact hld

private lemma differentiableAt_digamma370 {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.digamma s :=
  (analyticAt_digamma370 hs).differentiableAt

private lemma continuousAt_digamma370 {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt Complex.digamma s :=
  (differentiableAt_digamma370 hs).continuousAt

private lemma digamma_ofReal_im_eq_zero370 {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).im = 0 := by
  have hre : 0 < ((x : ℂ)).re := by simpa using hx
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hneR : ∀ m : ℕ, x ≠ -(m : ℝ) := by
    intro m h
    apply hne m
    rw [h]
    push_cast
    ring
  have h1 : HasDerivAt (fun y : ℝ => Complex.Gamma (y : ℂ))
      (deriv Complex.Gamma (x : ℂ)) x :=
    (Complex.differentiableAt_Gamma _ hne).hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => ((Real.Gamma y : ℝ) : ℂ))
      ((deriv Real.Gamma x : ℝ) : ℂ) x :=
    (Real.differentiableAt_Gamma hneR).hasDerivAt.ofReal_comp
  have hfun : (fun y : ℝ => Complex.Gamma (y : ℂ)) =
      fun y : ℝ => ((Real.Gamma y : ℝ) : ℂ) := by
    funext y
    exact Complex.Gamma_ofReal y
  rw [hfun] at h1
  have hd : deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) :=
    h1.unique h2
  have hg : Complex.Gamma (x : ℂ) = ((Real.Gamma x : ℝ) : ℂ) := Complex.Gamma_ofReal x
  rw [Complex.digamma_def, logDeriv_apply, hd, hg]
  rw [show ((deriv Real.Gamma x : ℝ) : ℂ) / ((Real.Gamma x : ℝ) : ℂ) =
    (((deriv Real.Gamma x / Real.Gamma x : ℝ)) : ℂ) by push_cast; ring]
  exact Complex.ofReal_im _

private lemma logDeriv_Gammaℝ370 {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
      (1 / 2) * Complex.digamma (s / 2) := by
  have hhalf : HasDerivAt (fun w : ℂ => w / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id s).div_const (2 : ℂ)
  have hhalf_re : 0 < (s / 2).re := by
    rw [Complex.div_re]
    simp
    positivity
  have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re, Complex.div_re, Complex.div_ofNat_re] at hr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num at hr
    linarith
  have hΓ_ne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hhalf_re
  let g1 : ℂ → ℂ := fun w => (Real.pi : ℂ) ^ (-w / 2)
  let g2 : ℂ → ℂ := fun w => Complex.Gamma (w / 2)
  have hπne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hg1_ne : g1 s ≠ 0 := by
    dsimp [g1]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hπne)
  have hg2_ne : g2 s ≠ 0 := hΓ_ne
  have hΓR_eq : Gammaℝ = fun w => g1 w * g2 w := by
    funext w
    rw [Gammaℝ_def]
  have hneghalf : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2 : ℂ) s := by
    have hid : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) s := (hasDerivAt_id s).neg
    simpa using hid.div_const (2 : ℂ)
  have hg1_diff : DifferentiableAt ℂ g1 s := by
    dsimp [g1]
    exact (hneghalf.const_cpow (Or.inl hπne)).differentiableAt
  have hΓ_da : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma (s / 2) hne
  have hg2_diff : DifferentiableAt ℂ g2 s := by
    dsimp [g2]
    exact hΓ_da.comp s hhalf.differentiableAt
  rw [hΓR_eq]
  change logDeriv (g1 * g2) s = _
  rw [logDeriv_mul s hg1_ne hg2_ne hg1_diff hg2_diff]
  have hlog1 : logDeriv g1 s = -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) := by
    dsimp [g1]
    have hcpow : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s :=
      hneghalf.const_cpow (Or.inl hπne)
    rw [logDeriv_apply, hcpow.deriv]
    have hbase_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hπne)
    have hlogπ : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      rw [← Complex.ofReal_log Real.pi_pos.le]
    rw [hlogπ]
    field_simp
  have hlog2 : logDeriv g2 s = (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    dsimp [g2]
    have hcomp : HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2))
        (deriv Complex.Gamma (s / 2) * (1 / 2)) s := hΓ_da.hasDerivAt.comp s hhalf
    rw [logDeriv_apply, hcomp.deriv, Complex.digamma, logDeriv_apply]
    field_simp
  rw [hlog1, hlog2]

private lemma logDeriv_gammaFactor_even370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.Even) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) + (1 / 2) * Complex.digamma (s / 2) := by
  have hfun : DirichletCharacter.gammaFactor χ = Gammaℝ :=
    funext fun z => hχ.gammaFactor_def z
  rw [hfun]
  exact logDeriv_Gammaℝ370 hs

private lemma logDeriv_gammaFactor_odd370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.Odd) {s : ℂ} (hs : -1 < s.re) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
        (1 / 2) * Complex.digamma ((s + 1) / 2) := by
  have hfun : DirichletCharacter.gammaFactor χ = fun z : ℂ => Gammaℝ (z + 1) :=
    funext fun z => hχ.gammaFactor_def z
  have hs1 : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hc0 := (differentiableAt_Gammaℝ370 hs1).hasDerivAt.comp s
    ((hasDerivAt_id s).add_const (1 : ℂ))
  have hc : HasDerivAt (fun z : ℂ => Gammaℝ (z + 1)) (deriv Gammaℝ (s + 1)) s := by
    simpa [Function.comp_def] using hc0
  rw [hfun, logDeriv_apply, hc.deriv,
    show deriv Gammaℝ (s + 1) / Gammaℝ (s + 1) = logDeriv Gammaℝ (s + 1) from
      (logDeriv_apply _ _).symm,
    logDeriv_Gammaℝ370 hs1]

private lemma logDeriv_completedLFunction_split370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {s : ℂ}
    (h0 : 0 < s.re) (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
  have hN : q ≠ 1 := by
    intro hN1
    cases hN1
    exact hne (Subsingleton.elim _ _)
  have hΓ : DirichletCharacter.gammaFactor χ s ≠ 0 := gammaFactor_ne_zero370 χ h0
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hEv : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      fun w => DirichletCharacter.LFunction χ w * DirichletCharacter.gammaFactor χ w := by
    filter_upwards [hopen.mem_nhds h0] with w hw
    have hΓw : DirichletCharacter.gammaFactor χ w ≠ 0 := gammaFactor_ne_zero370 χ hw
    exact completedLFunction_eq_LFunction_mul_gammaFactor370 χ hN hΓw
  have hcongr : logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (fun w => DirichletCharacter.LFunction χ w *
        DirichletCharacter.gammaFactor χ w) s := by
    rw [logDeriv_apply, logDeriv_apply, hEv.deriv_eq, hEv.eq_of_nhds]
  rw [hcongr]
  exact logDeriv_mul (f := DirichletCharacter.LFunction χ)
    (g := DirichletCharacter.gammaFactor χ) s hL hΓ
    (analyticAt_LFunction370 χ hne s).differentiableAt
    (analyticAt_gammaFactor370 χ h0).differentiableAt

private lemma continuousAt_logDeriv_LFunction370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s ≠ 0) :
    ContinuousAt (logDeriv (DirichletCharacter.LFunction χ)) s := by
  have hA := analyticAt_LFunction370 χ hne s
  exact hA.deriv.continuousAt.div hA.continuousAt hs

private lemma continuousAt_logDeriv_gammaFactor370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (h0 : 0 < s.re) :
    ContinuousAt (logDeriv (DirichletCharacter.gammaFactor χ)) s := by
  have hA := analyticAt_gammaFactor370 χ h0
  exact hA.deriv.continuousAt.div hA.continuousAt (gammaFactor_ne_zero370 χ h0)

private lemma shifted_half_re370 (c : ℝ) (s : ℂ) :
    ((s + (c : ℂ)) / 2).re = (s.re + c) / 2 := by
  rw [Complex.div_re]
  simp [Complex.add_re, Complex.ofReal_re]
  ring

private lemma continuous_digamma_line_shift370 {d c : ℝ} (h : 0 < d + c) :
    Continuous (fun t : ℝ =>
      Complex.digamma ((((d : ℝ) : ℂ) + (t : ℂ) * I + (c : ℂ)) / 2)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hre : 0 < (((((d : ℝ) : ℂ) + (t : ℂ) * I) + (c : ℂ)) / 2).re := by
    rw [shifted_half_re370]
    have hd : (((d : ℝ) : ℂ) + (t : ℂ) * I).re = d := by simp
    rw [hd]
    positivity
  have hline : Continuous (fun t : ℝ =>
      ((((d : ℝ) : ℂ) + (t : ℂ) * I) + (c : ℂ)) / 2) := by fun_prop
  exact ContinuousAt.comp (g := Complex.digamma)
    (f := fun t : ℝ => ((((d : ℝ) : ℂ) + (t : ℂ) * I) + (c : ℂ)) / 2)
    (x := t) (continuousAt_digamma370 hre) hline.continuousAt

private lemma continuousOn_digamma_horizontal_shift370 (c T : ℝ) :
    ContinuousOn (fun σ : ℝ =>
      Complex.digamma (((σ : ℂ) + (T : ℂ) * I + (c : ℂ)) / 2))
      {σ : ℝ | 0 < σ + c} := by
  intro σ hσ
  have hσ' : 0 < σ + c := hσ
  have hre : 0 < ((((σ : ℝ) : ℂ) + (T : ℂ) * I + (c : ℂ)) / 2).re := by
    rw [shifted_half_re370]
    have hs : (((σ : ℝ) : ℂ) + (T : ℂ) * I).re = σ := by simp
    rw [hs]
    positivity
  have hline : Continuous (fun σ : ℝ =>
      ((σ : ℂ) + (T : ℂ) * I + (c : ℂ)) / 2) := by fun_prop
  have hCA : ContinuousAt
      (Complex.digamma ∘ fun σ : ℝ => ((σ : ℂ) + (T : ℂ) * I + (c : ℂ)) / 2) σ :=
    ContinuousAt.comp (g := Complex.digamma)
      (f := fun σ : ℝ => ((σ : ℂ) + (T : ℂ) * I + (c : ℂ)) / 2)
      (x := σ) (continuousAt_digamma370 hre) hline.continuousAt
  exact hCA.continuousWithinAt

private lemma intervalIntegral_im370 {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t).im = ∫ t in a..b, (f t).im := by
  have h := Complex.imCLM.intervalIntegral_comp_comm hf
  simpa using h.symm

private lemma intervalIntegral_re370 {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t).re = ∫ t in a..b, (f t).re := by
  have h := Complex.reCLM.intervalIntegral_comp_comm hf
  simpa using h.symm

private lemma digamma_rectangle_shift370 {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
        (Complex.digamma (((2 : ℝ) + (t : ℂ) * I + (c : ℂ)) / 2)).re) -
      (∫ σ in (1 / 2 : ℝ)..2,
          (Complex.digamma (((σ : ℂ) + (T : ℂ) * I + (c : ℂ)) / 2)).im) =
      ∫ t in (0 : ℝ)..T,
        (Complex.digamma ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I + (c : ℂ)) / 2)).re := by
  let f : ℂ → ℂ := fun s => Complex.digamma ((s + (c : ℂ)) / 2)
  let z : ℂ := ((1 / 2 : ℝ) : ℂ)
  let w : ℂ := (2 : ℂ) + (T : ℂ) * I
  have hzre : z.re = 1 / 2 := by simp [z]
  have hzim : z.im = 0 := by simp [z]
  have hwre : w.re = 2 := by simp [w]
  have hwim : w.im = T := by simp [w]
  have hdiff : DifferentiableOn ℂ f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    have hsre : 1 / 2 ≤ s.re := by
      have h := hs.1
      rw [hzre, hwre, Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at h
      exact h.1
    have hre2 : 0 < ((s + (c : ℂ)) / 2).re := by rw [shifted_half_re370]; positivity
    exact ((differentiableAt_digamma370 hre2).comp s
      ((differentiableAt_id.add_const _).div_const 2)).differentiableWithinAt
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hdiff
  rw [hzre, hzim, hwre, hwim] at hcauchy
  have hIcc : Set.uIcc (1 / 2 : ℝ) 2 = Set.Icc (1 / 2 : ℝ) 2 :=
    Set.uIcc_of_le (by norm_num)
  have hsubset : Set.uIcc (1 / 2 : ℝ) 2 ⊆ {σ : ℝ | 0 < σ + c} := by
    intro y hy
    rw [hIcc] at hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy.1
    show 0 < y + c
    linarith
  have hInt_bot : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) volume (1 / 2) 2 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [hIcc] at hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
    have hre2 : 0 < ((((x : ℂ) + ((0 : ℝ) : ℂ) * I) + (c : ℂ)) / 2).re := by
      rw [shifted_half_re370]
      have hx0 : ((x : ℂ) + ((0 : ℝ) : ℂ) * I).re = x := by simp
      rw [hx0]
      positivity
    have hline : Continuous (fun x : ℝ =>
        (((x : ℂ) + ((0 : ℝ) : ℂ) * I) + (c : ℂ)) / 2) := by fun_prop
    have hCA : ContinuousAt
        (Complex.digamma ∘ fun x : ℝ =>
          (((x : ℂ) + ((0 : ℝ) : ℂ) * I) + (c : ℂ)) / 2) x :=
      ContinuousAt.comp (g := Complex.digamma)
        (f := fun x : ℝ => (((x : ℂ) + ((0 : ℝ) : ℂ) * I) + (c : ℂ)) / 2)
        (x := x) (continuousAt_digamma370 hre2) hline.continuousAt
    exact hCA.continuousWithinAt
  have hInt_top : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I)) volume (1 / 2) 2 := by
    apply ContinuousOn.intervalIntegrable
    exact ((continuousOn_digamma_horizontal_shift370 c T).mono hsubset)
  have hInt_right : IntervalIntegrable
      (fun y : ℝ => f (((2 : ℝ) : ℂ) + (y : ℂ) * I)) volume 0 T :=
    (continuous_digamma_line_shift370 (show (0 : ℝ) < 2 + c by linarith)).intervalIntegrable 0 T
  have hInt_left : IntervalIntegrable
      (fun y : ℝ => f (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) volume 0 T :=
    (continuous_digamma_line_shift370
      (show (0 : ℝ) < 1 / 2 + c by linarith)).intervalIntegrable 0 T
  have him := congrArg Complex.im hcauchy
  rw [Complex.sub_im, Complex.add_im, Complex.sub_im, Complex.zero_im,
    smul_eq_mul, smul_eq_mul, Complex.I_mul_im, Complex.I_mul_im,
    intervalIntegral_im370 hInt_bot, intervalIntegral_im370 hInt_top,
    intervalIntegral_re370 hInt_right, intervalIntegral_re370 hInt_left] at him
  have hbot0 : (∫ x in (1 / 2 : ℝ)..2,
      (f ((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) ?_,
      intervalIntegral.integral_const]
    · simp
    · intro x hx
      rw [hIcc] at hx
      have hxpos : 0 < (x + c) / 2 := by
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
        positivity
      have harg : ((x : ℂ) + ((0 : ℝ) : ℂ) * I + (c : ℂ)) / 2 =
          (((x + c) / 2 : ℝ) : ℂ) := by push_cast; ring
      show (f ((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im = 0
      dsimp [f]
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at harg ⊢
      rw [harg]
      exact digamma_ofReal_im_eq_zero370 hxpos
  rw [hbot0] at him
  have hgoal : (∫ y in (0 : ℝ)..T, (f (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re) -
      (∫ x in (1 / 2 : ℝ)..2, (f ((x : ℂ) + (T : ℂ) * I)).im) =
      ∫ y in (0 : ℝ)..T, (f (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re := by
    linarith
  have e_right : (∫ y in (0 : ℝ)..T, (f (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re) =
      ∫ t in (0 : ℝ)..T,
        (Complex.digamma (((2 : ℝ) + (t : ℂ) * I + (c : ℂ)) / 2)).re := by
    apply intervalIntegral.integral_congr
    intro t _
    rfl
  have e_top : (∫ x in (1 / 2 : ℝ)..2, (f ((x : ℂ) + (T : ℂ) * I)).im) =
      ∫ σ in (1 / 2 : ℝ)..2,
        (Complex.digamma (((σ : ℂ) + (T : ℂ) * I + (c : ℂ)) / 2)).im := by
    apply intervalIntegral.integral_congr
    intro σ _
    rfl
  have e_left : (∫ y in (0 : ℝ)..T, (f (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re) =
      ∫ t in (0 : ℝ)..T,
        (Complex.digamma ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I + (c : ℂ)) / 2)).re := by
    apply intervalIntegral.integral_congr
    intro t _
    rfl
  rw [e_right, e_top, e_left] at hgoal
  exact hgoal

private lemma left_edge_shift370 (c : ℝ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
        (Complex.digamma ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I + (c : ℂ)) / 2)).re) =
      2 * ∫ u in (0 : ℝ)..(T / 2),
          (Complex.digamma ((((1 + 2 * c) / 4 : ℝ) : ℂ) + (u : ℂ) * I)).re := by
  have hpt : ∀ t : ℝ,
      (Complex.digamma ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I + (c : ℂ)) / 2)).re =
      (fun u : ℝ =>
          (Complex.digamma ((((1 + 2 * c) / 4 : ℝ) : ℂ) + (u : ℂ) * I)).re)
        (t / 2) := by
    intro t
    simp only []
    congr 2
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  rw [intervalIntegral.integral_comp_div
    (fun u : ℝ =>
      (Complex.digamma ((((1 + 2 * c) / 4 : ℝ) : ℂ) + (u : ℂ) * I)).re)
    (two_ne_zero)]
  norm_num [smul_eq_mul]

private lemma gamma_ld_mul_I_im370 (r : ℝ) (z : ℂ) :
    ((-(1 / 2 : ℂ) * (r : ℂ) + (1 / 2) * z) * I).im =
      -r / 2 + 1 / 2 * z.re := by
  have h : (-(1 / 2 : ℂ) * (r : ℂ) + (1 / 2) * z) =
      ((-(r / 2) : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * z := by push_cast; ring
  rw [h, Complex.mul_I_im, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  ring

private lemma gamma_ld_im370 (r : ℝ) (z : ℂ) :
    (-(1 / 2 : ℂ) * (r : ℂ) + (1 / 2) * z).im = 1 / 2 * z.im := by
  have h : (-(1 / 2 : ℂ) * (r : ℂ) + (1 / 2) * z) =
      ((-(r / 2) : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * z := by push_cast; ring
  rw [h, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]
  ring

private lemma gammaArc_eval_core370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {c : ℝ} (hc : 0 ≤ c) (T : ℝ)
    (hV : (∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im) =
      ∫ t in (0 : ℝ)..T, (-(Real.log Real.pi) / 2 +
        (1 / 2 : ℝ) * (Complex.digamma (((2 : ℝ) + (t : ℂ) * I + (c : ℂ)) / 2)).re))
    (hH : (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im) =
      ∫ σ in (1 / 2 : ℝ)..2, (1 / 2 : ℝ) * (Complex.digamma
        (((σ : ℂ) + (T : ℂ) * I + (c : ℂ)) / 2)).im) :
    (∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im) -
      (∫ σ in (1 / 2 : ℝ)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im) =
      -(T / 2) * Real.log Real.pi +
        ∫ u in (0 : ℝ)..(T / 2),
          (Complex.digamma ((((1 + 2 * c) / 4 : ℝ) : ℂ) + (u : ℂ) * I)).re := by
  rw [hV, hH]
  have hcψ : Continuous (fun t : ℝ => (1 / 2 : ℝ) *
      (Complex.digamma (((2 : ℝ) + (t : ℂ) * I + (c : ℂ)) / 2)).re) := by
    apply Continuous.mul continuous_const
    apply Complex.continuous_re.comp
    exact continuous_digamma_line_shift370 (show (0 : ℝ) < 2 + c by linarith)
  have hcc : Continuous (fun _ : ℝ => -(Real.log Real.pi) / 2) := continuous_const
  rw [intervalIntegral.integral_add (hcc.intervalIntegrable 0 T)
    (hcψ.intervalIntegrable 0 T)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hrect := digamma_rectangle_shift370 hc T
  have hleft := left_edge_shift370 c T
  simp only [smul_eq_mul, sub_zero]
  have hmain : (∫ t in (0 : ℝ)..T,
      (Complex.digamma (((2 : ℝ) + (t : ℂ) * I + (c : ℂ)) / 2)).re) -
      (∫ σ in (1 / 2 : ℝ)..2,
          (Complex.digamma (((σ : ℂ) + (T : ℂ) * I + (c : ℂ)) / 2)).im) =
      2 * ∫ u in (0 : ℝ)..(T / 2),
          (Complex.digamma ((((1 + 2 * c) / 4 : ℝ) : ℂ) + (u : ℂ) * I)).re := by
    rw [hrect, hleft]
  linarith

private lemma gammaArc_even370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.Even) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im) -
      (∫ σ in (1 / 2 : ℝ)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im) =
      -(T / 2) * Real.log Real.pi +
        ∫ u in (0 : ℝ)..(T / 2),
          (Complex.digamma (1 / 4 + (u : ℂ) * I)).re := by
  have hV : (∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im) =
      ∫ t in (0 : ℝ)..T, (-(Real.log Real.pi) / 2 +
        (1 / 2 : ℝ) * (Complex.digamma (((2 : ℝ) + (t : ℂ) * I +
          (((0 : ℝ)) : ℂ)) / 2)).re) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    have hre0 : ((2 : ℂ) + (t : ℂ) * I).re = 2 := by simp
    have hre : 0 < ((2 : ℂ) + (t : ℂ) * I).re := by rw [hre0]; norm_num
    rw [logDeriv_gammaFactor_even370 hχ hre,
      show ((2 : ℂ) + (t : ℂ) * I) / 2 =
        ((2 : ℝ) + (t : ℂ) * I + (((0 : ℝ)) : ℂ)) / 2 by push_cast; ring,
      gamma_ld_mul_I_im370]
  have hH : (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im) =
      ∫ σ in (1 / 2 : ℝ)..2, (1 / 2 : ℝ) * (Complex.digamma
        (((σ : ℂ) + (T : ℂ) * I + (((0 : ℝ)) : ℂ)) / 2)).im := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only []
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hσ
    have hre0 : ((σ : ℂ) + (T : ℂ) * I).re = σ := by simp
    have hre : 0 < ((σ : ℂ) + (T : ℂ) * I).re := by rw [hre0]; linarith [hσ.1]
    rw [logDeriv_gammaFactor_even370 hχ hre,
      show ((σ : ℂ) + (T : ℂ) * I) / 2 =
        ((σ : ℝ) + (T : ℂ) * I + (((0 : ℝ)) : ℂ)) / 2 by push_cast; ring,
      gamma_ld_im370]
  have h := gammaArc_eval_core370 χ (c := 0) le_rfl T hV hH
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  simp only []
  norm_num

private lemma gammaArc_odd370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.Odd) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im) -
      (∫ σ in (1 / 2 : ℝ)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im) =
      -(T / 2) * Real.log Real.pi +
        ∫ u in (0 : ℝ)..(T / 2),
          (Complex.digamma (3 / 4 + (u : ℂ) * I)).re := by
  have hV : (∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im) =
      ∫ t in (0 : ℝ)..T, (-(Real.log Real.pi) / 2 +
        (1 / 2 : ℝ) * (Complex.digamma (((2 : ℝ) + (t : ℂ) * I +
          (((1 : ℝ)) : ℂ)) / 2)).re) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    have hre0 : ((2 : ℂ) + (t : ℂ) * I).re = 2 := by simp
    have hre : (-1 : ℝ) < ((2 : ℂ) + (t : ℂ) * I).re := by rw [hre0]; norm_num
    rw [logDeriv_gammaFactor_odd370 hχ hre,
      show (((2 : ℂ) + (t : ℂ) * I) + 1) / 2 =
        ((2 : ℝ) + (t : ℂ) * I + (((1 : ℝ)) : ℂ)) / 2 by push_cast; ring,
      gamma_ld_mul_I_im370]
  have hH : (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im) =
      ∫ σ in (1 / 2 : ℝ)..2, (1 / 2 : ℝ) * (Complex.digamma
        (((σ : ℂ) + (T : ℂ) * I + (((1 : ℝ)) : ℂ)) / 2)).im := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only []
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hσ
    have hre0 : ((σ : ℂ) + (T : ℂ) * I).re = σ := by simp
    have hre : (-1 : ℝ) < ((σ : ℂ) + (T : ℂ) * I).re := by rw [hre0]; linarith [hσ.1]
    rw [logDeriv_gammaFactor_odd370 hχ hre,
      show (((σ : ℂ) + (T : ℂ) * I) + 1) / 2 =
        ((σ : ℝ) + (T : ℂ) * I + (((1 : ℝ)) : ℂ)) / 2 by push_cast; ring,
      gamma_ld_im370]
  have h := gammaArc_eval_core370 χ (c := 1) (by norm_num) T hV hH
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  simp only []
  norm_num

private lemma gammaArc_scaled370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    2 / Real.pi * ((∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im) -
      (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im)) =
      gammaPhase370 (parity370 χ) T - T / Real.pi * Real.log Real.pi := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [gammaArc_even370 hχ]
    have hp : parity370 χ = 0 := by simp [parity370, hχ]
    rw [hp]
    have he : (1 / 4 + 0 / 2 : ℝ) = 1 / 4 := by norm_num
    unfold gammaPhase370
    rw [he]
    field_simp
    have hi : (∫ u in (0 : ℝ)..(T / 2),
        (Complex.digamma (1 / 4 + (u : ℂ) * I)).re) =
        ∫ t in (0 : ℝ)..(T / 2),
          (Complex.digamma (((1 / 4 : ℝ) : ℂ) + I * (t : ℂ))).re := by
      apply intervalIntegral.integral_congr
      intro u _
      apply congrArg Complex.re
      push_cast
      ring
    rw [← hi]
    simp only [mul_comm] <;> ring
  · rw [gammaArc_odd370 hχ]
    have hp : parity370 χ = 1 := by simp [parity370, hχ, hχ.not_even]
    rw [hp]
    have he : (1 / 4 + 1 / 2 : ℝ) = 3 / 4 := by norm_num
    unfold gammaPhase370
    rw [he]
    field_simp
    have hi : (∫ u in (0 : ℝ)..(T / 2),
        (Complex.digamma (3 / 4 + (u : ℂ) * I)).re) =
        ∫ t in (0 : ℝ)..(T / 2),
          (Complex.digamma (((3 / 4 : ℝ) : ℂ) + I * (t : ℂ))).re := by
      apply intervalIntegral.integral_congr
      intro u _
      apply congrArg Complex.re
      push_cast
      ring
    rw [← hi]
    simp only [mul_comm] <;> ring

private lemma completedArc_split370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ}
    (hT : 0 < T) (hgood : ∀ ρ ∈ LZeros χ T, ρ.im ≠ T ∧ ρ.im ≠ -T) :
    (∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.completedLFunction χ) (2 + (t : ℂ) * I) * I).im) -
      (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im) =
      ((∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.LFunction χ) (2 + (t : ℂ) * I) * I).im) -
        ∫ σ in (1 / 2 : ℝ)..2,
          (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im) +
      ((∫ t in (0 : ℝ)..T,
        (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im) -
        ∫ σ in (1 / 2 : ℝ)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im) := by
  have hN : q ≠ 1 := by
    intro hN1
    cases hN1
    exact hne (Subsingleton.elim _ _)
  have hL_vertical : ∀ t : ℝ,
      DirichletCharacter.LFunction χ (((2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
    simp
  have hL_horizontal : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro σ hσ1 hσ2
    have hcomp : DirichletCharacter.completedLFunction χ ((σ : ℂ) + (T : ℂ) * I) ≠ 0 :=
      completedLFunction_ne_zero_of_goodHeight370 hχ hne hT.le hgood (Or.inl (by simp))
    have hsre : 0 < σ := by linarith [hσ1]
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ _ (Or.inr hN)]
    exact div_ne_zero hcomp (gammaFactor_ne_zero370 χ (by simpa using hsre))
  have hpt_v : ∀ t : ℝ,
      (logDeriv (DirichletCharacter.completedLFunction χ) (2 + (t : ℂ) * I) * I).im =
        (logDeriv (DirichletCharacter.LFunction χ) (2 + (t : ℂ) * I) * I).im +
        (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im := by
    intro t
    have h0 : 0 < ((2 : ℂ) + (t : ℂ) * I).re := by simp
    rw [logDeriv_completedLFunction_split370 χ hne h0 (hL_vertical t),
      add_mul, Complex.add_im]
  have hpt_h : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
      (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im =
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im +
        (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hσ
    have h0 : 0 < ((σ : ℂ) + (T : ℂ) * I).re := by simp; linarith [hσ.1]
    rw [logDeriv_completedLFunction_split370 χ hne h0 (hL_horizontal σ hσ.1 hσ.2),
      Complex.add_im]
  have hiL_v : IntervalIntegrable (fun t : ℝ =>
      (logDeriv (DirichletCharacter.LFunction χ) (2 + (t : ℂ) * I) * I).im)
      volume 0 T := by
    apply Continuous.intervalIntegrable
    apply Complex.continuous_im.comp
    apply Continuous.mul _ continuous_const
    rw [continuous_iff_continuousAt]
    intro t
    have hline : Continuous fun t : ℝ => (2 : ℂ) + (t : ℂ) * I := by fun_prop
    exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.LFunction χ))
      (f := fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) (x := t)
      (continuousAt_logDeriv_LFunction370 χ hne (hL_vertical t)) hline.continuousAt
  have hiG_v : IntervalIntegrable (fun t : ℝ =>
      (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im)
      volume 0 T := by
    apply Continuous.intervalIntegrable
    apply Complex.continuous_im.comp
    apply Continuous.mul _ continuous_const
    rw [continuous_iff_continuousAt]
    intro t
    have h0 : 0 < ((2 : ℂ) + (t : ℂ) * I).re := by simp
    have hline : Continuous fun t : ℝ => (2 : ℂ) + (t : ℂ) * I := by fun_prop
    exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.gammaFactor χ))
      (f := fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) (x := t)
      (continuousAt_logDeriv_gammaFactor370 χ h0) hline.continuousAt
  have hIcc : Set.uIcc (1 / 2 : ℝ) 2 = Set.Icc (1 / 2 : ℝ) 2 :=
    Set.uIcc_of_le (by norm_num)
  have hiL_h : IntervalIntegrable (fun σ : ℝ =>
      (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im)
      volume (1 / 2) 2 := by
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    rw [hIcc] at hσ
    have hline : Continuous fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I := by fun_prop
    have hCA : ContinuousAt (fun σ : ℝ =>
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im) σ := by
      apply Complex.continuous_im.continuousAt.comp
      exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.LFunction χ))
        (f := fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I) (x := σ)
        (continuousAt_logDeriv_LFunction370 χ hne (hL_horizontal σ hσ.1 hσ.2))
        hline.continuousAt
    exact hCA.continuousWithinAt
  have hiG_h : IntervalIntegrable (fun σ : ℝ =>
      (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im)
      volume (1 / 2) 2 := by
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    rw [hIcc] at hσ
    have h0 : 0 < ((σ : ℂ) + (T : ℂ) * I).re := by simp; linarith [hσ.1]
    have hline : Continuous fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I := by fun_prop
    have hCA : ContinuousAt (fun σ : ℝ =>
        (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im) σ := by
      apply Complex.continuous_im.continuousAt.comp
      exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.gammaFactor χ))
        (f := fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I) (x := σ)
        (continuousAt_logDeriv_gammaFactor370 χ h0) hline.continuousAt
    exact hCA.continuousWithinAt
  have hIcc' : Set.uIcc (1 / 2 : ℝ) 2 = Set.Icc (1 / 2 : ℝ) 2 :=
    Set.uIcc_of_le (by norm_num)
  rw [intervalIntegral.integral_congr (fun t _ => hpt_v t),
    intervalIntegral.integral_congr hpt_h,
    intervalIntegral.integral_add hiL_v hiG_v,
    intervalIntegral.integral_add hiL_h hiG_h]
  ring

private lemma logDeriv_LFunction_star_conj370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (DirichletCharacter.LFunction (star χ)) (starRingEnd ℂ s) =
      starRingEnd ℂ (logDeriv (DirichletCharacter.LFunction χ) s) := by
  have hfun : DirichletCharacter.LFunction (star χ) =
      fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)) := by
    funext z
    have h := LFunction_star_conj370 χ hne (starRingEnd ℂ z)
    rwa [Complex.conj_conj] at h
  have hd : deriv (DirichletCharacter.LFunction (star χ)) (starRingEnd ℂ s) =
      starRingEnd ℂ (deriv (DirichletCharacter.LFunction χ) s) := by
    rw [hfun]
    exact deriv_conj_conj' (DirichletCharacter.LFunction χ) s
  rw [logDeriv_apply, logDeriv_apply, hd, LFunction_star_conj370 χ hne s]
  exact (map_div₀ (starRingEnd ℂ) _ _).symm

private lemma logDeriv_LFunction_conj'370 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (DirichletCharacter.LFunction χ) (starRingEnd ℂ s) =
      starRingEnd ℂ (logDeriv (DirichletCharacter.LFunction (star χ)) s) := by
  have hstar : star χ ≠ 1 := by
    rw [MulChar.star_eq_inv]
    exact inv_ne_one.mpr hne
  have h := logDeriv_LFunction_star_conj370 (star χ) hstar s
  rwa [star_star] at h

private lemma argument_eq_sum_upper_arcs370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ}
    (hT : 0 < T) (hgood : ∀ ρ ∈ LZeros χ T, ρ.im ≠ T ∧ ρ.im ≠ -T) :
    argument370 χ T =
      (1 / Real.pi) *
        (((∫ t in (0 : ℝ)..T,
            (logDeriv (DirichletCharacter.LFunction χ) (2 + (t : ℂ) * I) * I).im) -
          ∫ σ in (1 / 2 : ℝ)..2,
            (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im) +
        ((∫ t in (0 : ℝ)..T,
            (logDeriv (DirichletCharacter.LFunction (star χ)) (2 + (t : ℂ) * I) * I).im) -
          ∫ σ in (1 / 2 : ℝ)..2,
            (logDeriv (DirichletCharacter.LFunction (star χ)) ((σ : ℂ) + (T : ℂ) * I)).im)) := by
  have hstar : star χ ≠ 1 := by
    rw [MulChar.star_eq_inv]
    exact inv_ne_one.mpr hne
  have hN : q ≠ 1 := by
    intro hN1
    cases hN1
    exact hne (Subsingleton.elim _ _)
  set F := logDeriv (DirichletCharacter.LFunction χ) with hF_def
  set G := logDeriv (DirichletCharacter.LFunction (star χ)) with hG_def
  set A : ℂ := ∫ σ in (1 / 2 : ℝ)..2, F ((σ : ℂ) + (T : ℂ) * I) with hA_def
  set A' : ℂ := ∫ σ in (1 / 2 : ℝ)..2, G ((σ : ℂ) + (T : ℂ) * I) with hA'_def
  set B : ℂ := ∫ y in (0 : ℝ)..T, F (((2 : ℝ) : ℂ) + (y : ℂ) * I) with hB_def
  set B' : ℂ := ∫ y in (0 : ℝ)..T, G (((2 : ℝ) : ℂ) + (y : ℂ) * I) with hB'_def
  have hne_right : ∀ y : ℝ,
      DirichletCharacter.LFunction χ (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
    simp
  have hne_right' : ∀ y : ℝ,
      DirichletCharacter.LFunction (star χ) (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re (star χ) (Or.inl hstar)
    simp
  have hne_top : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 2 →
      DirichletCharacter.LFunction χ ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro x hx1 hx2
    intro hzero
    have hcomp : DirichletCharacter.completedLFunction χ ((x : ℂ) + (T : ℂ) * I) ≠ 0 :=
      completedLFunction_ne_zero_of_goodHeight370 hχ hne hT.le hgood (Or.inl (by simp))
    by_cases hxge : 1 ≤ x
    · exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simpa using hxge)) hzero
    · have hxre : ((x : ℂ) + (T : ℂ) * I).re = x := by simp
      have hre : 0 < ((x : ℂ) + (T : ℂ) * I).re ∧
          ((x : ℂ) + (T : ℂ) * I).re < 1 := by
        rw [hxre]
        exact ⟨by linarith, lt_of_not_ge hxge⟩
      exact hcomp ((completedLFunction_zero_iff370 hχ hne _).mpr ⟨hzero, hre.1, hre.2⟩)
  have hne_bot : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 2 →
      DirichletCharacter.LFunction χ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0 := by
    intro x hx1 hx2
    intro hzero
    have hcomp : DirichletCharacter.completedLFunction χ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0 :=
      completedLFunction_ne_zero_of_goodHeight370 hχ hne hT.le hgood (Or.inr (by simp))
    by_cases hxge : 1 ≤ x
    · exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simpa using hxge)) hzero
    · have hxre : ((x : ℂ) + ((-T : ℝ) : ℂ) * I).re = x := by simp
      have hre : 0 < ((x : ℂ) + ((-T : ℝ) : ℂ) * I).re ∧
          ((x : ℂ) + ((-T : ℝ) : ℂ) * I).re < 1 := by
        rw [hxre]
        exact ⟨by linarith, lt_of_not_ge hxge⟩
      exact hcomp ((completedLFunction_zero_iff370 hχ hne _).mpr ⟨hzero, hre.1, hre.2⟩)
  have hne_top' : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 2 →
      DirichletCharacter.LFunction (star χ) ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro x hx1 hx2
    have hc := LFunction_star_conj370 χ hne (starRingEnd ℂ ((x : ℂ) + (T : ℂ) * I))
    simp only [Complex.conj_conj] at hc
    rw [hc]
    intro h
    have h2 : DirichletCharacter.LFunction χ (starRingEnd ℂ
        ((x : ℂ) + (T : ℂ) * I)) = 0 := by
      have hh := congrArg (starRingEnd ℂ) h
      rwa [Complex.conj_conj, map_zero] at hh
    rw [← point_conj370 x T] at h2
    exact hne_bot x hx1 hx2 h2
  have hint_right : ∀ a b : ℝ, IntervalIntegrable
      (fun y : ℝ => F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) volume a b := by
    intro a b
    have hline : Continuous (fun y : ℝ => F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) := by
      rw [continuous_iff_continuousAt]
      intro y
      have hl : Continuous fun y : ℝ => ((2 : ℝ) : ℂ) + (y : ℂ) * I := by fun_prop
      exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.LFunction χ))
        (f := fun y : ℝ => ((2 : ℝ) : ℂ) + (y : ℂ) * I) (x := y)
        (continuousAt_logDeriv_LFunction370 χ hne (hne_right y)) hl.continuousAt
    exact hline.intervalIntegrable a b
  have hint_right' : ∀ a b : ℝ, IntervalIntegrable
      (fun y : ℝ => G (((2 : ℝ) : ℂ) + (y : ℂ) * I)) volume a b := by
    intro a b
    have hline : Continuous (fun y : ℝ => G (((2 : ℝ) : ℂ) + (y : ℂ) * I)) := by
      rw [continuous_iff_continuousAt]
      intro y
      have hl : Continuous fun y : ℝ => ((2 : ℝ) : ℂ) + (y : ℂ) * I := by fun_prop
      exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.LFunction (star χ)))
        (f := fun y : ℝ => ((2 : ℝ) : ℂ) + (y : ℂ) * I) (x := y)
        (continuousAt_logDeriv_LFunction370 (star χ) hstar (hne_right' y)) hl.continuousAt
    exact hline.intervalIntegrable a b
  have hint_top : IntervalIntegrable
      (fun x : ℝ => F ((x : ℂ) + (T : ℂ) * I)) volume (1 / 2) 2 := by
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hσ
    have hline : Continuous fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I := by fun_prop
    have hCA : ContinuousAt (fun σ : ℝ =>
        logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I)) σ := by
      exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.LFunction χ))
        (f := fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I) (x := σ)
        (continuousAt_logDeriv_LFunction370 χ hne (hne_top σ hσ.1 hσ.2))
        hline.continuousAt
    exact hCA.continuousWithinAt
  have hint_top' : IntervalIntegrable
      (fun x : ℝ => G ((x : ℂ) + (T : ℂ) * I)) volume (1 / 2) 2 := by
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hσ
    have hline : Continuous fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I := by fun_prop
    have hCA : ContinuousAt (fun σ : ℝ =>
        logDeriv (DirichletCharacter.LFunction (star χ)) ((σ : ℂ) + (T : ℂ) * I)) σ := by
      exact ContinuousAt.comp (g := logDeriv (DirichletCharacter.LFunction (star χ)))
        (f := fun σ : ℝ => (σ : ℂ) + (T : ℂ) * I) (x := σ)
        (continuousAt_logDeriv_LFunction370 (star χ) hstar (hne_top' σ hσ.1 hσ.2))
        hline.continuousAt
    exact hCA.continuousWithinAt
  have hBotR : (∫ x in (1 / 2 : ℝ)..2, F ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) =
      starRingEnd ℂ A' := by
    rw [hA'_def, ← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro x _
    show F ((x : ℂ) + ((-T : ℝ) : ℂ) * I) =
      starRingEnd ℂ (G ((x : ℂ) + (T : ℂ) * I))
    rw [point_conj370 x T, hF_def, hG_def, logDeriv_LFunction_conj'370 χ hne]
  have hRlow : (∫ y in (-T : ℝ)..0, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      starRingEnd ℂ B' := by
    have hsub := intervalIntegral.integral_comp_neg
      (a := (0 : ℝ)) (b := T)
      (fun y : ℝ => F (((2 : ℝ) : ℂ) + (y : ℂ) * I))
    rw [neg_zero] at hsub
    rw [← hsub, hB'_def, ← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro y _
    show F (((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) =
      starRingEnd ℂ (G (((2 : ℝ) : ℂ) + (y : ℂ) * I))
    rw [point_conj370 2 y, hF_def, hG_def, logDeriv_LFunction_conj'370 χ hne]
  have hR : (∫ y in (-T : ℝ)..T, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      starRingEnd ℂ B' + B := by
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (a := (-T : ℝ)) (b := (0 : ℝ)) (c := T)
      (hint_right (-T) 0) (hint_right 0 T)
    rw [← hadj, hRlow, ← hB_def]
  have hBre : B.re = ∫ t in (0 : ℝ)..T,
      (logDeriv (DirichletCharacter.LFunction χ) (2 + (t : ℂ) * I) * I).im := by
    rw [hB_def]
    have h1 := Complex.reCLM.intervalIntegral_comp_comm (hint_right 0 T)
    have h2 : (∫ y in (0 : ℝ)..T, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re =
        ∫ y in (0 : ℝ)..T, (F (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re := by
      simpa using h1.symm
    rw [h2]
    apply intervalIntegral.integral_congr
    intro t _
    show (F (((2 : ℝ) : ℂ) + (t : ℂ) * I)).re =
      (logDeriv (DirichletCharacter.LFunction χ) (2 + (t : ℂ) * I) * I).im
    rw [Complex.mul_I_im, hF_def]
    norm_num
  have hB're : B'.re = ∫ t in (0 : ℝ)..T,
      (logDeriv (DirichletCharacter.LFunction (star χ)) (2 + (t : ℂ) * I) * I).im := by
    rw [hB'_def]
    have h1 := Complex.reCLM.intervalIntegral_comp_comm (hint_right' 0 T)
    have h2 : (∫ y in (0 : ℝ)..T, G (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re =
        ∫ y in (0 : ℝ)..T, (G (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re := by
      simpa using h1.symm
    rw [h2]
    apply intervalIntegral.integral_congr
    intro t _
    show (G (((2 : ℝ) : ℂ) + (t : ℂ) * I)).re =
      (logDeriv (DirichletCharacter.LFunction (star χ)) (2 + (t : ℂ) * I) * I).im
    rw [Complex.mul_I_im, hG_def]
    norm_num
  have hAim : A.im = ∫ σ in (1 / 2 : ℝ)..2,
      (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im := by
    rw [hA_def]
    have h1 := Complex.imCLM.intervalIntegral_comp_comm hint_top
    simpa using h1.symm
  have hA'im : A'.im = ∫ σ in (1 / 2 : ℝ)..2,
      (logDeriv (DirichletCharacter.LFunction (star χ)) ((σ : ℂ) + (T : ℂ) * I)).im := by
    rw [hA'_def]
    have h1 := Complex.imCLM.intervalIntegral_comp_comm hint_top'
    simpa using h1.symm
  have h3 : (∫ σ in (2 : ℝ)..(1/2), F ((σ : ℂ) + (T : ℂ) * I)) = -A := by
    rw [hA_def, intervalIntegral.integral_symm]
  have hR2 : (∫ y in (-T : ℝ)..T, F ((2 : ℂ) + (y : ℂ) * I)) = starRingEnd ℂ B' + B := by
    simpa using hR
  have hBre' : B.re = ∫ t in (0 : ℝ)..T, (F ((2 : ℂ) + (t : ℂ) * I) * I).im := by
    simpa using hBre
  have hB're' : B'.re = ∫ t in (0 : ℝ)..T, (G ((2 : ℂ) + (t : ℂ) * I) * I).im := by
    simpa using hB're
  have hAim' : A.im = ∫ σ in (1 / 2 : ℝ)..2, (F ((σ : ℂ) + (T : ℂ) * I)).im := by
    simpa using hAim
  have hA'im' : A'.im = ∫ σ in (1 / 2 : ℝ)..2, (G ((σ : ℂ) + (T : ℂ) * I)).im := by
    simpa using hA'im
  unfold argument370
  rw [← hF_def]
  simp only [sub_eq_add_neg, ofReal_neg, neg_mul] at hBotR ⊢
  rw [hBotR, hR2, h3]
  rw [← hAim', ← hA'im', ← hB're', ← hBre']
  simp only [Complex.add_im, Complex.add_re, Complex.sub_im, Complex.sub_re,
    Complex.conj_im, Complex.conj_re, Complex.I_mul_im, Complex.I_mul_re,
    Complex.neg_im, Complex.neg_re]
  ring

/-! ### Route to `primitive_count_identity370` at good heights (this chat, OMOS lomos 20260707) -/

private lemma factorsThrough_star370 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {d : ℕ}
    (h : DirichletCharacter.FactorsThrough χ d) :
    DirichletCharacter.FactorsThrough (star χ) d := by
  obtain ⟨hd, χ₀, hχ₀⟩ := h
  refine ⟨hd, star χ₀, ?_⟩
  rw [hχ₀]
  ext a
  rw [MulChar.star_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, MulChar.star_apply]

private lemma isPrimitive_star370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) : (star χ).IsPrimitive := by
  have hset : DirichletCharacter.conductorSet (star χ) =
      DirichletCharacter.conductorSet χ := by
    ext d
    exact ⟨fun hd => by
      have h' := factorsThrough_star370 (χ := star χ) hd
      rwa [star_star] at h', factorsThrough_star370⟩
  rw [DirichletCharacter.isPrimitive_def] at hχ ⊢
  have hc : DirichletCharacter.conductor (star χ) = DirichletCharacter.conductor χ := by
    simp only [DirichletCharacter.conductor, hset]
  rw [hc, hχ]

private lemma parity_star370 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    parity370 (star χ) = parity370 χ := by
  have hiff : (star χ).Even ↔ χ.Even := by
    show (star χ) (-1) = 1 ↔ χ (-1) = 1
    rw [MulChar.star_apply]
    constructor
    · intro h
      have h' := congrArg (starRingEnd ℂ) h
      simpa using h'
    · intro h
      rw [h]
      simp
  unfold parity370
  by_cases h : χ.Even
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]

private lemma goodHeight_star370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {T : ℝ}
    (hgood : ∀ ρ ∈ LZeros χ T, ρ.im ≠ T ∧ ρ.im ≠ -T) :
    ∀ ρ ∈ LZeros (star χ) T, ρ.im ≠ T ∧ ρ.im ≠ -T := by
  intro ρ hρ
  obtain ⟨hzero, hre1, hre2, him⟩ := hρ
  have hconj : starRingEnd ℂ ρ ∈ LZeros χ T := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := LFunction_star_conj370 χ hne (starRingEnd ℂ ρ)
      rw [Complex.conj_conj] at h
      rw [h] at hzero
      simpa using hzero
    · simpa using hre1
    · simpa using hre2
    · simpa using him
  obtain ⟨h1, h2⟩ := hgood _ hconj
  exact ⟨fun hh => h2 (by simp [hh]), fun hh => h1 (by simp [hh])⟩

/-- Divide a count identity through by `Real.pi`. -/
private lemma pi_cancel370 (T S A G Lq Lpi : ℝ) :
    Real.pi * S = Real.pi * A + (Real.pi * G - T * Lpi) + T * Lq →
      S = T / Real.pi * (Lq - Lpi) + G + A := by
  intro hS
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp
  linarith

/-- Trudgian page 3, display 2.3, at a good height: the count is the conductor
term plus the Gamma phase plus the contour argument. -/
private lemma count_identity_good370 {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ}
    (hT : 0 < T) (hgood : ∀ ρ ∈ LZeros χ T, ρ.im ≠ T ∧ ρ.im ≠ -T)
    (hfin : (LZeros χ T).Finite) :
    (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) =
      T / Real.pi * Real.log (q / Real.pi) + gammaPhase370 (parity370 χ) T +
        argument370 χ T := by
  classical
  have hstar : star χ ≠ 1 := by
    rw [MulChar.star_eq_inv]
    exact inv_ne_one.mpr hne
  have hgood' := goodHeight_star370 hne hgood
  have hprim' := isPrimitive_star370 hχ
  set LFc : ℝ := (∫ t in (0 : ℝ)..T,
      (logDeriv (DirichletCharacter.LFunction χ) (2 + (t : ℂ) * I) * I).im) -
      (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * I)).im) with hLFc
  set Gc : ℝ := (∫ t in (0 : ℝ)..T,
      (logDeriv (DirichletCharacter.gammaFactor χ) (2 + (t : ℂ) * I) * I).im) -
      (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * I)).im) with hGc
  set LFs : ℝ := (∫ t in (0 : ℝ)..T,
      (logDeriv (DirichletCharacter.LFunction (star χ)) (2 + (t : ℂ) * I) * I).im) -
      (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.LFunction (star χ)) ((σ : ℂ) + (T : ℂ) * I)).im) with hLFs
  set Gs : ℝ := (∫ t in (0 : ℝ)..T,
      (logDeriv (DirichletCharacter.gammaFactor (star χ)) (2 + (t : ℂ) * I) * I).im) -
      (∫ σ in (1 / 2 : ℝ)..2,
        (logDeriv (DirichletCharacter.gammaFactor (star χ)) ((σ : ℂ) + (T : ℂ) * I)).im) with hGs
  have hfold := boundary_fold370 hχ hne hT hgood
  rw [rectangle_winding370 hχ hne hT.le hgood hfin] at hfold
  have hSre : (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℂ)).re =
      ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ) := by
    simp
  rw [hSre] at hfold
  rw [completedArc_split370 hχ hne hT hgood,
    completedArc_split370 (χ := star χ) hprim' hstar hT hgood'] at hfold
  have e1 : Real.pi * (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) =
      ((LFc + Gc) + ((LFs + Gs) + T * Real.log (q : ℝ))) := by
    rw [hLFc, hGc, hLFs, hGs]
    linarith [hfold]
  have hgam : ∀ X Y L : ℝ, 2 / Real.pi * X = Y - T / Real.pi * L →
      X = Real.pi / 2 * Y - T / 2 * L := by
    intro X Y L hX
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at hX
    field_simp
    linarith
  have eGc : Gc = Real.pi / 2 * gammaPhase370 (parity370 χ) T - T / 2 * Real.log Real.pi := by
    rw [hGc]
    exact hgam _ _ _ (gammaArc_scaled370 χ T)
  have eGs : Gs = Real.pi / 2 * gammaPhase370 (parity370 χ) T - T / 2 * Real.log Real.pi := by
    rw [hGs]
    have h := gammaArc_scaled370 (star χ) T
    rw [parity_star370 χ] at h
    exact hgam _ _ _ h
  have e2 : LFc + LFs = Real.pi * argument370 χ T := by
    have hcancel : ∀ Z : ℝ, Real.pi * ((1 / Real.pi) * Z) = Z := by
      intro Z
      rw [one_div, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
    have h := argument_eq_sum_upper_arcs370 hχ hne hT hgood
    rw [h]
    exact (hcancel (LFc + LFs)).symm
  have hmain : Real.pi * (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) =
      Real.pi * argument370 χ T +
        (Real.pi * gammaPhase370 (parity370 χ) T - T * Real.log Real.pi) +
          T * Real.log (q : ℝ) := by
    linarith [e1, e2, eGc, eGs]
  rw [Real.log_div (by exact_mod_cast NeZero.ne q) Real.pi_ne_zero]
  exact pi_cancel370 T _ _ _ _ _ hmain
/-- LEAF. The argument principle separates the elementary conductor term,
the continuous Gamma phase and the right-limit L-function argument.
Trudgian page 3, display 2.3. The right limit implements the inclusive count on page 1.
This is an exact identity and supplies no estimate for either phase.
-/
theorem primitive_count_identity370 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T)
    (hfin : (LZeros χ T).Finite) :
    Tendsto (argument370 χ) (𝓝[>] T) (𝓝 (argumentRight370 χ T)) ∧
    (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) =
      T / Real.pi * Real.log (q / Real.pi) +
      gammaPhase370 (parity370 χ) T + argumentRight370 χ T := by
  classical
  have hT0 : (0 : ℝ) < T := by linarith
  have ha : parity370 χ = 0 ∨ parity370 χ = 1 := by
    unfold parity370
    split_ifs <;> simp
  have ha0 : (0 : ℝ) ≤ parity370 χ := by
    rcases ha with h | h <;> rw [h] <;> norm_num
  have hfin1 : (LZeros χ (T + 1)).Finite := LZeros_finite χ (T + 1)
  set H : Finset ℝ := hfin1.toFinset.image (fun ρ => |ρ.im|) with hH
  have hHmem : ∀ ρ ∈ LZeros χ (T + 1), |ρ.im| ∈ H := by
    intro ρ hρ
    exact Finset.mem_image.mpr ⟨ρ, (Set.Finite.mem_toFinset hfin1).mpr hρ, rfl⟩
  have key : ∀ t : ℝ, t ≤ T + 1 → T < t → (∀ s ∈ H, T < s → t < s) →
      (∀ ρ ∈ LZeros χ t, ρ.im ≠ t ∧ ρ.im ≠ -t) ∧ LZeros χ t = LZeros χ T := by
    intro t ht1 ht hbound
    have hsub : LZeros χ t ⊆ LZeros χ (T + 1) := by
      rintro ρ ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, h4.trans ht1⟩
    have hle : ∀ ρ ∈ LZeros χ t, |ρ.im| ≤ T := by
      intro ρ hρ
      by_contra hc
      have hgt : T < |ρ.im| := lt_of_not_ge hc
      have hb := hbound _ (hHmem ρ (hsub hρ)) hgt
      linarith [hρ.2.2.2]
    refine ⟨fun ρ hρ => ⟨?_, ?_⟩, ?_⟩
    · intro hh
      have h := hle ρ hρ
      have ht0 : (0 : ℝ) < t := by linarith
      rw [hh, abs_of_pos ht0] at h
      linarith
    · intro hh
      have h := hle ρ hρ
      have ht0 : (0 : ℝ) < t := by linarith
      rw [hh, abs_neg, abs_of_pos ht0] at h
      linarith
    · ext ρ
      constructor
      · intro hρ
        exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hle ρ hρ⟩
      · intro hρ
        exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans (le_of_lt ht)⟩
  obtain ⟨ε, hε0, hε⟩ : ∃ ε > 0, ∀ t : ℝ, T < t → t < T + ε →
      (∀ ρ ∈ LZeros χ t, ρ.im ≠ t ∧ ρ.im ≠ -t) ∧ LZeros χ t = LZeros χ T := by
    rcases (H.filter (fun s => T < s)).eq_empty_or_nonempty with hemp | hne
    · refine ⟨1, one_pos, fun t ht1 ht2 => key t (by linarith) ht1 ?_⟩
      intro s hs hTs
      have hmem : s ∈ H.filter (fun s => T < s) := Finset.mem_filter.mpr ⟨hs, hTs⟩
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty s)
    · obtain ⟨m, hmF, hmin⟩ := Finset.exists_min_image (H.filter (fun s => T < s)) id hne
      rw [Finset.mem_filter] at hmF
      have hTm : T < m := hmF.2
      have hm1 : m ≤ T + 1 := by
        obtain ⟨ρ, hρ, hρm⟩ := Finset.mem_image.mp hmF.1
        have hρ' : ρ ∈ LZeros χ (T + 1) := (Set.Finite.mem_toFinset hfin1).mp hρ
        rw [← hρm]
        exact hρ'.2.2.2
      refine ⟨(m - T) / 2, by linarith, fun t ht1 ht2 => key t (by linarith) ht1 ?_⟩
      intro s hs hTs
      have hsF : s ∈ H.filter (fun s => T < s) := Finset.mem_filter.mpr ⟨hs, hTs⟩
      have hle' : m ≤ s := hmin s hsF
      linarith
  have hev : ∀ t : ℝ, T < t → t < T + ε → argument370 χ t =
      (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) -
        (t / Real.pi * Real.log ((q : ℝ) / Real.pi) + gammaPhase370 (parity370 χ) t) := by
    intro t ht ht2
    obtain ⟨hgood_t, hset⟩ := hε t ht ht2
    have hsum : (∑ ρ ∈ (LZeros_finite χ t).toFinset, (LMult χ ρ : ℝ)) =
        ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ) := by
      congr 1
      ext ρ
      simp only [Set.Finite.mem_toFinset]
      rw [hset]
    have hid := count_identity_good370 hχ hne (by linarith : (0 : ℝ) < t) hgood_t
      (LZeros_finite χ t)
    rw [hsum] at hid
    linarith [hid]
  have hcont : ContinuousAt (fun t : ℝ =>
      (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) -
        (t / Real.pi * Real.log ((q : ℝ) / Real.pi) + gammaPhase370 (parity370 χ) t)) T := by
    refine ContinuousAt.sub continuousAt_const ?_
    refine ContinuousAt.add ?_ ?_
    · exact ContinuousAt.mul (continuousAt_id.div_const Real.pi) continuousAt_const
    · exact (gamma_phase_deriv370 ha0 T).continuousAt
  have hlim : Tendsto (argument370 χ) (𝓝[>] T)
      (𝓝 ((∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) -
        (T / Real.pi * Real.log ((q : ℝ) / Real.pi) + gammaPhase370 (parity370 χ) T))) := by
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show T < T + ε by linarith)] with t ht
    exact (hev t ht.1 ht.2).symm
  have hAR : argumentRight370 χ T = (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) -
      (T / Real.pi * Real.log ((q : ℝ) / Real.pi) + gammaPhase370 (parity370 χ) T) := by
    unfold argumentRight370
    exact hlim.limUnder_eq
  refine ⟨?_, ?_⟩
  · rw [hAR]
    exact hlim
  · rw [hAR]
    ring


/-- LEAF. Backlund and Jensen control the right-limit contour argument.
Trudgian pages 4 to 9, displays 2.8, 3.9 and 4.3 to 4.12.
The displayed budget is loosened to reserve 2 for the separate Gamma error.
This bounds only L-function argument variation, without a zero-count main term.
-/
theorem primitive_argument_bound370 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    |argumentRight370 χ T| ≤ 0.5 * Real.log (q * T) + 15.7 := by
  sorry

/-- The leading conductor and Gamma terms combine into the published main term.
Trudgian page 3, displays 2.3 and 2.5. This is logarithm algebra only.
-/
theorem count_main_terms370 {q T : ℝ} (hq : 0 < q) (hT : 0 < T) :
    T / Real.pi * Real.log (q / Real.pi) +
      T / Real.pi * Real.log (T / (2 * Real.exp 1)) =
      T / Real.pi * Real.log (q * T / (2 * Real.pi * Real.exp 1)) := by
  rw [Real.log_div hq.ne' Real.pi_ne_zero,
    Real.log_div hT.ne' (by positivity),
    Real.log_div (by positivity : q * T ≠ 0) (by positivity),
    Real.log_mul hq.ne' hT.ne',
    Real.log_mul (by positivity : 2 * Real.pi ≠ 0) (Real.exp_ne_zero 1),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero 1)]
  ring

/-- The rounded Rosser error fits in the primitive principal error budget.
Helfgott page 38 display 4.26, principal case, using the rounded Rosser constants.
The numerical comparison is derived here and has no zero-count hypothesis.
-/
theorem rosser_primitive_budget370 {T : ℝ} (hT : Real.exp 1 ≤ T) :
    2 * (0.14 * Real.log T + 0.45 * Real.log (Real.log T) + 1.6) + 7 / 4 ≤
      0.5 * Real.log T + 17.7 := by
  have ht0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hl : 1 ≤ Real.log T := (Real.le_log_iff_exp_le ht0).mpr hT
  have hll : Real.log (Real.log T) ≤ Real.log T / 5 + 1 := by
    have hh := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log T / 5)
    rw [Real.log_div (by linarith : Real.log T ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)] at hh
    linarith [Real.log_five_lt_d9]
  linarith

/-- At heights from one to three the principal count main term has absolute value at most 4.
Helfgott page 38 display 4.26, the elementary low-height term at modulus one.
This statement contains no assertion about zeros.
-/
theorem principal_small_main370 {T : ℝ} (hT : 1 ≤ T) (hT3 : T ≤ 3) :
    |T / Real.pi * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤ 4 := by
  have ht0 : 0 < T := by linarith
  have hl0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl2 : Real.log T ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos ht0
    linarith
  have hlog2pi : 1 ≤ Real.log (2 * Real.pi) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have hlog2pi3 : Real.log (2 * Real.pi) ≤ 3 := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * Real.pi)
      (show 2 * Real.pi ≤ 8 by linarith [Real.pi_lt_four])
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
      norm_num
    rw [h8] at hh
    linarith [Real.log_two_lt_d9]
  have hdenlog : Real.log (2 * Real.pi * Real.exp 1) = Real.log (2 * Real.pi) + 1 := by
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero 1), Real.log_exp]
  have hf : 0 ≤ T / Real.pi := by positivity
  have hf1 : T / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  rw [Real.log_div ht0.ne' (by positivity), hdenlog, abs_mul,
    abs_of_nonneg hf, abs_of_nonpos (by linarith : Real.log T - (Real.log (2 * Real.pi) + 1) ≤ 0)]
  nlinarith

/-- The principal character count follows from the existing zeta count inputs.
Helfgott pages 37 and 38, displays 4.25 and 4.26, principal primitive case.
This remains CONDITIONAL ON rosser_strict193 through the rounded zeta bounds.
-/
theorem principal_count370 {T : ℝ} (hT : 1 ≤ T)
    (hfin : (LZeros (1 : DirichletCharacter ℂ 1) T).Finite) :
    |(∑ ρ ∈ hfin.toFinset, (LMult (1 : DirichletCharacter ℂ 1) ρ : ℝ)) -
      T / Real.pi * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        0.5 * Real.log T + 17.7 := by
  classical
  have hset : LZeros (1 : DirichletCharacter ℂ 1) T = zetaZeros T := by
    ext z
    simp only [LZeros, zetaZeros, Set.mem_ofPred_eq, DirichletCharacter.LFunction_modOne_eq]
  have hmult (z : ℂ) : LMult (1 : DirichletCharacter ℂ 1) z = zetaMult z := by
    unfold LMult zetaMult
    rw [DirichletCharacter.LFunction_modOne_eq]
  have hsum : (∑ ρ ∈ hfin.toFinset, (LMult (1 : DirichletCharacter ℂ 1) ρ : ℝ)) =
      ∑ ρ ∈ (zetaZeros_finite T).toFinset, (zetaMult ρ : ℝ) := by
    simp_rw [hmult]
    congr 1
    ext z
    simp only [Set.Finite.mem_toFinset]
    rw [hset]
  rw [hsum]
  have ht0 : 0 < T := by linarith
  have hl0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hden0 : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  have hdenlog : Real.log (2 * Real.pi * Real.exp 1) = Real.log (2 * Real.pi) + 1 := by
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero 1), Real.log_exp]
  have hmain : T / Real.pi * Real.log (T / (2 * Real.pi * Real.exp 1)) =
      2 * (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7/8) - 7/4 := by
    rw [Real.log_div ht0.ne' hden0.ne', hdenlog,
      Real.log_div ht0.ne' (by positivity)]
    field_simp
    <;> ring
  by_cases he : Real.exp 1 ≤ T
  · have hp : (zetaZerosPos T).Finite := by
      apply (zetaZeros_finite T).subset
      intro z hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1,
        by rw [abs_of_pos hz.2.2.2.1]; exact hz.2.2.2.2⟩
    have hreal (z : ℂ) (hz : z ∈ zetaZeros T) : z.im ≠ 0 := by
      intro hh
      have heq : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hh]
      have hn := (LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg hz.2.1 hz.2.2.1).2
      rw [heq, hz.1] at hn
      norm_num at hn
    have hb := zeta_count_both193 (zetaZeros_finite T) hp hreal
    have hu := rvm_upper he hp
    have hlo := rvm_lower he hp
    have hbudget := rosser_primitive_budget370 he
    rw [hmain, hb, abs_le]
    constructor <;> linarith
  · have ht3 : T ≤ 3 := by linarith [lt_of_not_ge he, Real.exp_one_lt_d9]
    have hzero : zetaZeros T = ∅ := by
      have hsub : zetaZeros T ⊆ zetaZeros 4 := by
        intro z hz
        exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans (by linarith)⟩
      rw [zetaZeros_four_eq_empty193] at hsub
      exact Set.eq_empty_of_subset_empty hsub
    have hfinzero : (zetaZeros_finite T).toFinset = ∅ := by
      ext z
      simp only [Set.Finite.mem_toFinset, Finset.notMem_empty, iff_false]
      rw [hzero]
      exact Set.notMem_empty z
    rw [hfinzero, Finset.sum_empty, zero_sub, abs_neg]
    have hbudget := principal_small_main370 hT ht3
    linarith

/-- The nonprincipal count follows by adding the two independent phase budgets.
Trudgian page 3, displays 2.3 to 2.6. Helfgott page 38, display 4.26.
CONDITIONAL ON the three OPEN analytic leaves in this file.
-/
theorem nonprincipal_count370 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T)
    (hfin : (LZeros χ T).Finite) :
    |(∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) -
      T / Real.pi * Real.log (q * T / (2 * Real.pi * Real.exp 1))| ≤
        0.5 * Real.log (q * T) + 17.7 := by
  classical
  have ha : (parity370 χ) = 0 ∨
      (parity370 χ) = 1 := by
    unfold parity370
    split_ifs <;> simp
  have hg := gamma_phase_error370 ha hT
  have hl := primitive_argument_bound370 χ hχ hne hT
  have hi := (primitive_count_identity370 χ hχ hne hT hfin).2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have ht0 : 0 < T := by linarith
  rw [hi, ← count_main_terms370 hq0 ht0]
  have he : T / Real.pi * Real.log (↑q / Real.pi) +
      gammaPhase370 (parity370 χ) T + argumentRight370 χ T -
      (T / Real.pi * Real.log (↑q / Real.pi) +
       T / Real.pi * Real.log (T / (2 * Real.exp 1))) =
      (gammaPhase370 (parity370 χ) T -
       T / Real.pi * Real.log (T / (2 * Real.exp 1))) + argumentRight370 χ T := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

/-- Exactly the statement of primitive_zero_count193, supplied without editing its file.
Helfgott pages 37 and 38, displays 4.25 and 4.26.
CONDITIONAL ON the three new phase leaves and the existing Rosser input.
-/
theorem primitive_zero_count370 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hfin : (LZeros χ T).Finite) :
    |(∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) -
      T / Real.pi * Real.log (q * T / (2 * Real.pi * Real.exp 1))| ≤
        0.5 * Real.log (q * T) + 17.7 := by
  by_cases hχ1 : χ = 1
  · subst χ
    have hq : q = 1 := by
      have hh := (DirichletCharacter.isPrimitive_def _).mp hχ
      simpa only [DirichletCharacter.conductor_one] using hh.symm
    subst q
    simpa only [Nat.cast_one, one_mul] using principal_count370 hT hfin
  · exact nonprincipal_count370 χ hχ hχ1 hT hfin


/-! Concrete instances. The phase and count inequalities remain conditional as labeled above. -/

example : parity370 (1 : DirichletCharacter ℂ 1) = 0 := by
  classical
  have he : (1 : DirichletCharacter ℂ 1).Even := by
    change (1 : DirichletCharacter ℂ 1) (-1) = 1
    rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  simp [parity370, he]
example : Continuous (fun t : ℝ =>
    (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I)).re) := by
  simpa using gamma_integrand_continuous370 (a := 0) (by norm_num)
example : HasDerivAt (gammaPhase370 0)
    ((Complex.digamma ((1 / 4 : ℂ) + (1 / 2 : ℂ) * I)).re / Real.pi) 1 := by
  simpa using gamma_phase_deriv370 (a := 0) (by norm_num) 1
example : gammaPhase370 0 0 = 0 := by simp [gammaPhase370]
example : argument370 (1 : DirichletCharacter ℂ 1) 0 = 0 := by
  unfold argument370
  simp only [neg_zero, ofReal_zero, zero_mul, sub_zero, add_zero,
    intervalIntegral.integral_same, mul_zero, zero_add]
  rw [intervalIntegral.integral_symm]
  simp
example : gammaCorrection370 0 1 =
    (1 / 4 : ℝ) * Real.log (5 / 4) - (1 / 4 : ℝ) * Real.arctan 2 := by
  norm_num [gammaCorrection370]
  ring
example : IntervalIntegrable (fun t : ℝ =>
    (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I)).re) volume 0 (1 / 2) := by
  simpa using gamma_phase_integrable370 (a := 0) (by norm_num) 1
example : |gammaCorrection370 0 1| ≤ 9 / 16 + Real.pi / 8 :=
  gamma_correction_bound370 (by norm_num) (by norm_num) (by norm_num)
example : |gammaCorrection370 1 1| ≤ 9 / 16 + Real.pi / 8 :=
  gamma_correction_bound370 (by norm_num) (by norm_num) (by norm_num)
example : 2 * (0.14 * Real.log 3 + 0.45 * Real.log (Real.log 3) + 1.6) + 7 / 4 ≤
    0.5 * Real.log 3 + 17.7 :=
  rosser_primitive_budget370 (by linarith [Real.exp_one_lt_d9])
example : |(1 : ℝ) / Real.pi * Real.log (1 / (2 * Real.pi * Real.exp 1))| ≤ 4 :=
  principal_small_main370 (by norm_num) (by norm_num)
example : (0 : ℝ) = 0 ∨ (0 : ℝ) = 1 := Or.inl rfl
example : (1 : ℝ) = 0 ∨ (1 : ℝ) = 1 := Or.inr rfl
example : (3 : ℝ) / Real.pi * Real.log (3 / Real.pi) +
    3 / Real.pi * Real.log (3 / (2 * Real.exp 1)) =
      3 / Real.pi * Real.log (3 * 3 / (2 * Real.pi * Real.exp 1)) :=
  count_main_terms370 (by norm_num) (by norm_num)
example : (1 : DirichletCharacter ℂ 1).IsPrimitive ∧
    (1 : ℝ) ≤ 1 ∧ (LZeros (1 : DirichletCharacter ℂ 1) 1).Finite :=
  ⟨DirichletCharacter.isPrimitive_one_level_one, le_rfl, LZeros_finite _ _⟩
example : ∃ χ : DirichletCharacter ℂ 3,
    χ.IsPrimitive ∧ χ ≠ 1 ∧ (1 : ℝ) ≤ 1 ∧ (LZeros χ 1).Finite := by
  obtain ⟨e⟩ := DirichletCharacter.mulEquiv_units ℂ 3
  let χ := e.symm (-1)
  have hne : χ ≠ 1 := by
    intro hh
    have hh' := congrArg e hh
    simp only [χ, MulEquiv.apply_symm_apply, map_one] at hh'
    have hc := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hh'
    exact (by decide : (-1 : ZMod 3) ≠ 1) hc
  have hprim : χ.IsPrimitive := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp χ.conductor_dvd_level with h | h
    · exact False.elim (hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
    · exact h
  exact ⟨χ, hprim, hne, le_rfl, LZeros_finite _ _⟩

end LeanLab.DERZ1997.Decomp370a
