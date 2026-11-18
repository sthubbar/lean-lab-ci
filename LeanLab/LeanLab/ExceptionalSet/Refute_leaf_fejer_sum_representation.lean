import LeanLab.ExceptionalSet.Decomp523a

/-!
Refutation of the statement `leaf_fejer_sum_representation` of
`SPLIT_leaf_one_sided_majorant.lean`, exactly as it is written there.

The right side of that statement integrates, over `t` in the unit interval, a
function of `x - t` that has period one, so it does not depend on `x`.  The
left side is a truncated cosine sum, which does depend on `x`.

Counterexample: `H = 2`, `a = 0`, `b = 1/2`, `s = 0`, with `F` forced by the
hypothesis.  Then `F 1 = 0`, `F 0 = 12 * I0` where `I0` is the integral over
`0..1/2` of `eC (-y)`, and `2 * pi * I * I0 = 2`, so `F 0` is not zero.  The
left side at `x` is the real part of `F 0 * eC x`; at `x = 0, 1/4, 1/2` these
are `re (F 0)`, `-im (F 0)`, `-re (F 0)`.  If all three equal the same number,
then `F 0 = 0`, a contradiction.  In numbers, at `x = 1/4` the left side is
`12 / pi` and the right side is `0`.

This file only refutes the statement as written.  It says nothing about the
intended identity, in which the indicator would be evaluated at `t` rather
than at `x - t`.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp523a

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-! ## Private helpers, re-proved from the split file -/

/-- `eC` has unit modulus. -/
private lemma norm_eC_one (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have h : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- Continuity of the phase function. -/
private lemma continuous_eC_neg_mul (k : ℕ) : Continuous fun y : ℝ => eC (-((k : ℝ) * y)) := by
  unfold eC
  fun_prop

/-- The phase has an exponential form of the expected shape. -/
private lemma eC_neg_mul_eq_exp (k : ℕ) (y : ℝ) :
    eC (-((k : ℝ) * y)) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) * y : ℝ) : ℂ)) := by
  unfold eC
  congr 1
  push_cast
  ring

/-- Derivative of the phase. -/
private lemma hasDerivAt_eC_neg_mul (k : ℕ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => eC (-((k : ℝ) * z)))
      (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y))) y := by
  have h1 : HasDerivAt (fun z : ℝ => (((-(k : ℝ)) * z : ℝ) : ℂ)) (((-(k : ℝ)) : ℝ) : ℂ) y := by
    have hbase := ((hasDerivAt_id (x := y)).const_mul (-(k : ℝ))).ofReal_comp
    simpa using hbase
  have h2 : HasDerivAt (fun z : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) * z : ℝ) : ℂ))
      ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) : ℝ) : ℂ)) y := h1.const_mul _
  have h3 := h2.cexp
  have hfun : (fun z : ℝ => eC (-((k : ℝ) * z))) =
      (fun x : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) * x : ℝ) : ℂ))) := by
    funext z
    exact eC_neg_mul_eq_exp k z
  have hval : (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y))) =
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) * y : ℝ) : ℂ)) *
        ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) : ℝ) : ℂ))) := by
    rw [eC_neg_mul_eq_exp]
    push_cast
    ring
  rw [hfun, hval]
  exact h3

/-- Scaling the integral of the phase returns the difference of two unit phases. -/
private lemma mul_integral_eC (k : ℕ) (α β : ℝ) :
    (2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * ∫ y in α..β, eC (-((k : ℝ) * y))
      = eC (-((k : ℝ) * α)) - eC (-((k : ℝ) * β)) := by
  have hcont := continuous_eC_neg_mul k
  have hFTC : ∫ y in α..β, (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y)))
      = eC (-((k : ℝ) * β)) - eC (-((k : ℝ) * α)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun z : ℝ => eC (-((k : ℝ) * z)))
      (f' := fun y : ℝ => -(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y)))
      (fun y _ => hasDerivAt_eC_neg_mul k y)
      ((continuous_const.mul hcont).intervalIntegrable _ _)
  have hsplit : ∫ y in α..β, (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y)))
      = (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ))) * ∫ y in α..β, eC (-((k : ℝ) * y)) :=
    intervalIntegral.integral_const_mul _ _
  rw [hsplit] at hFTC
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * ∫ y in α..β, eC (-((k : ℝ) * y))
      = -((-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ))) * ∫ y in α..β, eC (-((k : ℝ) * y))) := by
    ring
  rw [h2, hFTC]
  ring

/-- Integrability of an indicator times the phase. -/
private lemma intervalIntegrable_ind_mul_eC (k : ℕ) (p : ℝ → Prop) [DecidablePred p]
    (hp : MeasurableSet {y : ℝ | p y}) (A B : ℝ) :
    IntervalIntegrable (fun y : ℝ => (if p y then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
      MeasureTheory.volume A B := by
  classical
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => (if p y then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
      (MeasureTheory.volume.restrict (Set.uIoc A B)) :=
    ((Measurable.ite hp measurable_const measurable_const).mul
      (continuous_eC_neg_mul k).measurable).aestronglyMeasurable
  refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => (2 : ℂ)) intervalIntegrable_const hmeas ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  have hA : ‖(if p y then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> simp
  have hB : ‖eC (-((k : ℝ) * y))‖ = 1 := norm_eC_one _
  have hle : ‖(if p y then (1 : ℂ) else 0) * eC (-((k : ℝ) * y))‖ ≤ 2 := by
    rw [norm_mul, hB, mul_one]
    linarith
  simpa using hle

/-! ## Special values of the phase -/

/-- The phase at zero. -/
private lemma eC_zero_val : eC 0 = 1 := by
  unfold eC
  simp

/-- The phase at one quarter. -/
private lemma eC_quarter : eC (1 / 4) = Complex.I := by
  have h : eC (1 / 4) = Complex.exp (((Real.pi : ℂ) / 2) * Complex.I) := by
    unfold eC
    congr 1
    push_cast
    ring
  rw [h, Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

/-- The phase at one half. -/
private lemma eC_half : eC (1 / 2) = -1 := by
  have h : eC (1 / 2) = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    unfold eC
    congr 1
    push_cast
    ring
  rw [h, Complex.exp_pi_mul_I]

/-- The phase at minus one half. -/
private lemma eC_neg_half : eC (-(1 / 2)) = -1 := by
  have h : eC (-(1 / 2)) = Complex.exp (-((Real.pi : ℂ) * Complex.I)) := by
    unfold eC
    congr 1
    push_cast
    ring
  rw [h, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-! ## The right side does not depend on the point -/

/-- Integer frequencies make the phase one periodic. -/
private lemma eC_succ_mul_add_one (k : ℕ) (u : ℝ) :
    eC (((k : ℝ) + 1) * (u + 1)) = eC (((k : ℝ) + 1) * u) := by
  have h := Complex.exp_nat_mul_two_pi_mul_I (k + 1)
  have e1 : eC (((k : ℝ) + 1) * (u + 1)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((((k : ℝ) + 1) * u : ℝ) : ℂ) +
        ((k + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    unfold eC
    congr 1
    push_cast
    ring
  have e2 : eC (((k : ℝ) + 1) * u) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((((k : ℝ) + 1) * u : ℝ) : ℂ)) := by
    unfold eC
    rfl
  rw [e1, e2, Complex.exp_add, h, mul_one]

/-- The integral over a period of a reflected translate of a one periodic
function is the integral over the period. -/
private lemma integral_sub_of_periodic (g : ℝ → ℝ) (hg : Function.Periodic g 1) (x : ℝ) :
    (∫ t in (0 : ℝ)..1, g (x - t)) = ∫ u in (0 : ℝ)..1, g u := by
  rw [intervalIntegral.integral_comp_sub_left (fun u => g u) x]
  have h := hg.intervalIntegral_add_eq (x - 1) 0
  rw [sub_add_cancel, zero_add] at h
  rw [sub_zero]
  exact h

/-- The smoothed term of the right side is the same at every point. -/
private lemma fejer_term_indep (a b s : ℝ) (H : ℕ) (x : ℝ) :
    (∫ t in (0 : ℝ)..1,
        (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
          (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
      = ∫ u in (0 : ℝ)..1,
        (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * u)‖ ^ 2 *
          (if Int.fract (u - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0) := by
  refine integral_sub_of_periodic
    (fun u => (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * u)‖ ^ 2 *
      (if Int.fract (u - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) ?_ x
  intro u
  have h1 : ∀ k : ℕ, eC (((k : ℝ) + 1) * (u + 1)) = eC (((k : ℝ) + 1) * u) :=
    fun k => eC_succ_mul_add_one k u
  have h2 : Int.fract (u + 1 - (a - s)) = Int.fract (u - (a - s)) := by
    rw [show u + 1 - (a - s) = (u - (a - s)) + 1 by ring, Int.fract_add_one]
  simp only [h1, h2]

/-! ## The first Fourier coefficient of the half period indicator -/

/-- The first coefficient integral reduces to the phase integral over the half period. -/
private lemma coeff_half_eq :
    (∫ y in (0 : ℝ)..1,
        (if Int.fract y < (1 / 2 : ℝ) then (1 : ℂ) else 0) * eC (-(((1 : ℕ) : ℝ) * y)))
      = ∫ y in (0 : ℝ)..(1 / 2), eC (-(((1 : ℕ) : ℝ) * y)) := by
  have hp : MeasurableSet {y : ℝ | Int.fract y < (1 / 2 : ℝ)} :=
    measurableSet_lt measurable_fract measurable_const
  have hi1 := intervalIntegrable_ind_mul_eC 1 (fun y : ℝ => Int.fract y < (1 / 2 : ℝ)) hp 0 (1 / 2)
  have hi2 := intervalIntegrable_ind_mul_eC 1 (fun y : ℝ => Int.fract y < (1 / 2 : ℝ)) hp (1 / 2) 1
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hA : (∫ y in (0 : ℝ)..(1 / 2),
        (if Int.fract y < (1 / 2 : ℝ) then (1 : ℂ) else 0) * eC (-(((1 : ℕ) : ℝ) * y)))
      = ∫ y in (0 : ℝ)..(1 / 2), eC (-(((1 : ℕ) : ℝ) * y)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro y hy
    rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hy
    obtain ⟨hy0, hy1⟩ := hy
    have hfract : Int.fract y = y := by
      rw [Int.fract_eq_self]
      constructor <;> linarith
    have hcond : Int.fract y < (1 / 2 : ℝ) := by
      rw [hfract]
      exact hy1
    simp only [hcond, ite_true, one_mul]
  have hB : (∫ y in (1 / 2 : ℝ)..1,
        (if Int.fract y < (1 / 2 : ℝ) then (1 : ℂ) else 0) * eC (-(((1 : ℕ) : ℝ) * y))) = 0 := by
    have hcong : (∫ y in (1 / 2 : ℝ)..1,
          (if Int.fract y < (1 / 2 : ℝ) then (1 : ℂ) else 0) * eC (-(((1 : ℕ) : ℝ) * y)))
        = ∫ y in (1 / 2 : ℝ)..1, (0 : ℂ) := by
      apply intervalIntegral.integral_congr_uIoo
      intro y hy
      rw [Set.uIoo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hy
      obtain ⟨hy0, hy1⟩ := hy
      have hfract : Int.fract y = y := by
        rw [Int.fract_eq_self]
        constructor <;> linarith
      have hcond : ¬ (Int.fract y < (1 / 2 : ℝ)) := by
        rw [hfract]
        exact not_lt.mpr hy0.le
      simp only [hcond, ite_false, zero_mul]
    rw [hcong, intervalIntegral.integral_zero]
  rw [hA, hB, add_zero]

/-- The first coefficient integral is not zero. -/
private lemma coeff_half_ne_zero :
    (∫ y in (0 : ℝ)..1,
        (if Int.fract y < (1 / 2 : ℝ) then (1 : ℂ) else 0) * eC (-(((1 : ℕ) : ℝ) * y))) ≠ 0 := by
  intro h0
  have hm := mul_integral_eC 1 0 (1 / 2)
  rw [← coeff_half_eq, h0, mul_zero] at hm
  have e0 : eC (-(((1 : ℕ) : ℝ) * 0)) = 1 := by
    rw [show -(((1 : ℕ) : ℝ) * 0) = 0 by ring]
    exact eC_zero_val
  have e1 : eC (-(((1 : ℕ) : ℝ) * (1 / 2))) = -1 := by
    rw [show -(((1 : ℕ) : ℝ) * (1 / 2)) = -(1 / 2) by push_cast; ring]
    exact eC_neg_half
  rw [e0, e1] at hm
  norm_num at hm

/-- The coefficient integral in the shape the refuted statement produces. -/
private lemma coeff_shape_ne_zero :
    (∫ y in (0 : ℝ)..1,
        (if Int.fract (y - ((0 : ℝ) - 0)) < (1 / 2 : ℝ) - 0 + 2 * 0 then (1 : ℂ) else 0) *
          eC (-((((0 : ℕ) : ℝ) + 1) * y))) ≠ 0 := by
  have hcongr : (∫ y in (0 : ℝ)..1,
        (if Int.fract (y - ((0 : ℝ) - 0)) < (1 / 2 : ℝ) - 0 + 2 * 0 then (1 : ℂ) else 0) *
          eC (-((((0 : ℕ) : ℝ) + 1) * y)))
      = ∫ y in (0 : ℝ)..1,
        (if Int.fract y < (1 / 2 : ℝ) then (1 : ℂ) else 0) * eC (-(((1 : ℕ) : ℝ) * y)) := by
    apply intervalIntegral.integral_congr
    intro y _
    have h1 : y - ((0 : ℝ) - 0) = y := by ring
    have h2 : (1 / 2 : ℝ) - 0 + 2 * 0 = 1 / 2 := by ring
    have h3 : (((0 : ℕ) : ℝ) + 1) * y = ((1 : ℕ) : ℝ) * y := by push_cast; ring
    simp only
    rw [h1, h2, h3]
  rw [hcongr]
  exact coeff_half_ne_zero

/-! ## The refutation -/

/-- The statement of `leaf_fejer_sum_representation` is false as written.
Counterexample: `H = 2`, `a = 0`, `b = 1/2`, `s = 0`, with the coefficient
family forced by the hypothesis.  The right side is the same at every point,
because it integrates a one periodic function of `x - t` over a period, while
the left side is the real part of `F 0 * eC x` with `F 0` not zero, so it
takes different values at `x = 0`, `x = 1/4` and `x = 1/2`.  At `x = 1/4` the
left side is `12 / pi` and the right side is `0`. -/
theorem leaf_fejer_sum_representation_false :
    ¬ (∀ (a b s : ℝ) (H : ℕ), 1 ≤ H → ∀ (x : ℝ) (F : ℕ → ℂ),
    (∀ h, F h =
      (2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))) •
        ∫ y in (0 : ℝ)..1,
          (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℂ) else 0) *
            eC (-(((h : ℝ) + 1) * y))) →
    (∑ h ∈ Finset.range H, (F h * eC (((h : ℝ) + 1) * x)).re) =
      12 * (∫ t in (0 : ℝ)..1,
        (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
          (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
      - 12 * (∫ y in (0 : ℝ)..1,
          (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))) := by
  intro hall
  -- the coefficient integrals and the forced coefficient family
  set J : ℕ → ℂ := fun h => ∫ y in (0 : ℝ)..1,
    (if Int.fract (y - ((0 : ℝ) - 0)) < (1 / 2 : ℝ) - 0 + 2 * 0 then (1 : ℂ) else 0) *
      eC (-(((h : ℝ) + 1) * y)) with hJ
  set G : ℕ → ℂ := fun h => (2 * 12 * (1 - ((h : ℝ) + 1) / ((2 : ℕ) : ℝ))) • J h with hG
  have hJ0 : J 0 ≠ 0 := coeff_shape_ne_zero
  have hG1 : G 1 = 0 := by
    have hc : (2 * 12 * (1 - (((1 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) : ℝ) = 0 := by norm_num
    rw [hG]
    simp only
    rw [hc, zero_smul]
  have hG0 : G 0 = (12 : ℝ) • J 0 := by
    have hc : (2 * 12 * (1 - (((0 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) : ℝ) = 12 := by norm_num
    rw [hG]
    simp only
    rw [hc]
  -- the statement at an arbitrary point, with the right side made constant
  have hx : ∀ x : ℝ, (G 0 * eC x).re =
      12 * (∫ u in (0 : ℝ)..1,
        (1 / ((2 : ℕ) : ℝ)) * ‖∑ k ∈ Finset.range 2, eC (((k : ℝ) + 1) * u)‖ ^ 2 *
          (if Int.fract (u - ((0 : ℝ) - 0)) < (1 / 2 : ℝ) - 0 + 2 * 0 then (1 : ℝ) else 0))
      - 12 * (∫ y in (0 : ℝ)..1,
          (if Int.fract (y - ((0 : ℝ) - 0)) < (1 / 2 : ℝ) - 0 + 2 * 0 then (1 : ℝ) else 0)) := by
    intro x
    have h := hall 0 (1 / 2) 0 2 (by norm_num) x G (fun h => rfl)
    rw [fejer_term_indep, Finset.sum_range_succ, Finset.sum_range_one, hG1, zero_mul,
      Complex.zero_re, add_zero] at h
    rw [show (((0 : ℕ) : ℝ) + 1) * x = x by push_cast; ring] at h
    exact h
  have h0 := hx 0
  have h1 := hx (1 / 4)
  have h2 := hx (1 / 2)
  rw [eC_zero_val, mul_one] at h0
  rw [eC_quarter, Complex.mul_I_re] at h1
  rw [eC_half, mul_neg, mul_one, Complex.neg_re] at h2
  have hre : (G 0).re = 0 := by linarith
  have him : (G 0).im = 0 := by linarith
  have hz : G 0 = 0 := Complex.ext hre him
  rw [hG0] at hz
  rcases smul_eq_zero.mp hz with h12 | hJz
  · norm_num at h12
  · exact hJ0 hJz

end LeanLab.ExceptionalSet.Decomp523a
