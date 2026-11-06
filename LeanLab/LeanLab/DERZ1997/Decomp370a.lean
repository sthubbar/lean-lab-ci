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

/-- LEAF. Explicit Stirling remainder for the continuous Gamma phase.
Trudgian page 3, displays 2.4 and 2.5, scaled by twice the reciprocal of pi.
This isolates the analytic remainder before the elementary norm rounding.
-/
theorem gamma_stirling_raw370 {a T : ℝ} (ha : a = 0 ∨ a = 1) (hT : 1 ≤ T) :
    |gammaPhase370 a T - T / Real.pi * Real.log (T / (2 * Real.exp 1)) -
      2 / Real.pi * gammaCorrection370 a T| ≤
        1 / (3 * Real.pi * ‖(((1 / 4 + a / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)‖) := by
  sorry

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
  sorry

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
