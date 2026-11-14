import Mathlib
import LeanLab.RamareSaouter2003.Decomp563a

/-!
Backlund pp. 346 and 347 displays 8 through 12 and p. 368.
Use five Euler correction terms and the tenth Bernoulli remainder.
The printed two-term majorant is not used.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp563d
open Real Complex MeasureTheory Polynomial

/-- Backlund p. 367, the same finite H sum as the sealed source file. -/
noncomputable def boundaryH (σ : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc (1 : ℕ) 9, (1 : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 50 * I)) +
    1 / (2 * (10 : ℂ) ^ ((σ : ℂ) + 50 * I))

/-- Backlund p. 346 display 11, the rising factorial in the remainder. -/
noncomputable def rising (s : ℂ) (m : ℕ) : ℂ :=
  ∏ j ∈ Finset.range m, (s + j)

/-- Backlund p. 346 display 8 iterated to order ten, the unshifted periodic Bernoulli polynomial.
The symmetric variable is fract x times one minus fract x. -/
noncomputable def periodicB10 (x : ℝ) : ℝ :=
  let q := Int.fract x * (1 - Int.fract x)
  5 / 66 - (3 / 2) * q ^ 2 - 3 * q ^ 3 - (5 / 2) * q ^ 4 - q ^ 5

/-- Backlund p. 346, the higher-order kernel agrees with Mathlib's Bernoulli normalization. -/
theorem periodicB10_eq_mathlib (x : ℝ) :
    periodicB10 x = Polynomial.eval₂ (Rat.castHom ℝ) (Int.fract x) (Polynomial.bernoulli 10) := by
  have hpoly : Polynomial.bernoulli 10 =
      (Polynomial.X ^ 10 - 5 * Polynomial.X ^ 9 + Polynomial.C (15 / 2) * Polynomial.X ^ 8 -
        7 * Polynomial.X ^ 6 + 5 * Polynomial.X ^ 4 - Polynomial.C (3 / 2) * Polynomial.X ^ 2 +
        Polynomial.C (5 / 66) : ℚ[X]) := by
    have h3 : _root_.bernoulli 3 = (0 : ℚ) := by decide +kernel
    have h4 : _root_.bernoulli 4 = (-1 / 30 : ℚ) := by decide +kernel
    have h5 : _root_.bernoulli 5 = (0 : ℚ) := by decide +kernel
    have h6 : _root_.bernoulli 6 = (1 / 42 : ℚ) := by decide +kernel
    have h7 : _root_.bernoulli 7 = (0 : ℚ) := by decide +kernel
    have h8 : _root_.bernoulli 8 = (-1 / 30 : ℚ) := by decide +kernel
    have h9 : _root_.bernoulli 9 = (0 : ℚ) := by decide +kernel
    have h10 : _root_.bernoulli 10 = (5 / 66 : ℚ) := by decide +kernel
    norm_num [Polynomial.bernoulli, Finset.sum_range_succ, h3, h4, h5, h6, h7, h8, h9, h10, Nat.choose]
    simp only [← Polynomial.C_mul_X_pow_eq_monomial]
    norm_num [Polynomial.C_ofNat]
    ring
  rw [hpoly]
  norm_num [periodicB10]
  ring

/-- Backlund p. 346 display 11, the uniform tenth Bernoulli bound. -/
theorem periodicB10_bound (x : ℝ) : |periodicB10 x| ≤ (5 / 66 : ℝ) := by
  let q := Int.fract x * (1 - Int.fract x)
  have hq0 : 0 ≤ q := mul_nonneg (Int.fract_nonneg _) (by linarith [Int.fract_lt_one x])
  have hq1 : q ≤ 1 / 4 := by dsimp [q]; nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
  have h2 := pow_le_pow_left₀ hq0 hq1 2
  have h3 := pow_le_pow_left₀ hq0 hq1 3
  have h4 := pow_le_pow_left₀ hq0 hq1 4
  have h5 := pow_le_pow_left₀ hq0 hq1 5
  change |5 / 66 - (3 / 2) * q ^ 2 - 3 * q ^ 3 - (5 / 2) * q ^ 4 - q ^ 5| ≤ _
  apply abs_le.mpr
  constructor
  · norm_num at h2 h3 h4 h5
    linarith
  · linarith [sq_nonneg q, pow_nonneg hq0 3, pow_nonneg hq0 4, pow_nonneg hq0 5]

/-- Backlund p. 368, the pole and all five finite Euler correction terms. -/
noncomputable def correction (s : ℂ) : ℂ :=
  (10 : ℂ) ^ (1 - s) / (s - 1) + s / (12 * (10 : ℂ) ^ (s + 1)) -
    rising s 3 / (720 * (10 : ℂ) ^ (s + 3)) +
    rising s 5 / (30240 * (10 : ℂ) ^ (s + 5)) -
    rising s 7 / (1209600 * (10 : ℂ) ^ (s + 7)) +
    rising s 9 / (47900160 * (10 : ℂ) ^ (s + 9))

section
set_option maxHeartbeats 2000000

private theorem pb_continuous (n : ℕ) (hn : 2 ≤ n) :
    Continuous fun x : ℝ => bernoulliFun n (Int.fract x) :=
  (continuous_bernoulliFun n).continuousOn.comp_fract''
    (bernoulliFun_endpoints_eq_of_ne_one (by omega : n ≠ 1)).symm

private theorem pb_hasDerivWithinAt (n : ℕ) (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => bernoulliFun (n + 1) (Int.fract y))
      (((n : ℝ) + 1) * bernoulliFun n (Int.fract x)) (Set.Ioi x) x := by
  have h := HasDerivAt.comp_hasDerivWithinAt x (hasDerivAt_bernoulliFun (n + 1) (Int.fract x))
    (LeanLab.RamareSaouter2003.Decomp563a.hasDerivWithinAt_fract537 x)
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

private theorem pb_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖bernoulliFun n (Int.fract x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_bernoulliFun n).continuousOn
  exact ⟨C, (norm_nonneg _).trans (hC 0 (by norm_num)),
    fun x => hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩⟩

private theorem pb_integrable (n : ℕ) (hn : 2 ≤ n) (N : ℕ) (hN : 1 ≤ N) {a : ℂ}
    (ha : a.re < -1) :
    IntegrableOn (fun x : ℝ => (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ a)
      (Set.Ioi (N : ℝ)) := by
  obtain ⟨C, _hC0, hC⟩ := pb_bound n hn
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcp : IntegrableOn (fun x : ℝ => (x : ℂ) ^ a) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt ha hNR
  have hmble : AEStronglyMeasurable (fun x : ℝ => (bernoulliFun n (Int.fract x) : ℂ))
      (volume.restrict (Set.Ioi (N : ℝ))) :=
    (Complex.continuous_ofReal.measurable.comp (pb_continuous n hn).measurable).aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Ioi (N : ℝ))),
      ‖(bernoulliFun n (Int.fract x) : ℂ)‖ ≤ C := by
    filter_upwards with x
    simpa using hC x
  exact (hcp.bdd_mul hmble hbdd).congr (ae_of_all _ (fun x => by ring))

/-! ## One integration-by-parts step -/

private theorem pb_ibp_interval (n : ℕ) (hn : 2 ≤ n) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M)
    {s : ℂ} (hs : 0 < s.re) :
    ∫ x in (N : ℝ)..(M : ℝ), (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n))
      = (bernoulliFun (n + 1) (Int.fract ((M : ℝ))) : ℂ) * ((M : ℂ) ^ (-(s + n))) / ((n : ℂ) + 1)
        - (bernoulliFun (n + 1) (Int.fract ((N : ℝ))) : ℂ) * ((N : ℂ) ^ (-(s + n))) / ((n : ℂ) + 1)
        + (s + n) / ((n : ℂ) + 1) *
            ∫ x in (N : ℝ)..(M : ℝ),
              (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hne : (-(s + (n : ℂ)) : ℂ) ≠ 0 := by
    intro h
    have h0 : (-(s + (n : ℂ))).re = 0 := by rw [h]; simp
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re] at h0
    linarith
  have hden : ((n : ℂ) + 1) ≠ 0 := by
    intro h
    have h1 : ((n : ℂ) + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at h1
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    linarith
  have hpos : ∀ x ∈ Set.uIcc (N : ℝ) (M : ℝ), x ≠ 0 := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  have hu : ContinuousOn (fun y : ℝ => (bernoulliFun (n + 1) (Int.fract y) : ℂ))
      (Set.uIcc (N : ℝ) (M : ℝ)) :=
    (Complex.continuous_ofReal.comp (pb_continuous (n + 1) (by omega))).continuousOn
  have huu' : ∀ x ∈ Set.Ioo (min (N : ℝ) (M : ℝ)) (max (N : ℝ) (M : ℝ)),
      HasDerivWithinAt (fun y : ℝ => (bernoulliFun (n + 1) (Int.fract y) : ℂ))
        (((n : ℂ) + 1) * (bernoulliFun n (Int.fract x) : ℂ)) (Set.Ioi x) x := by
    intro x _
    have h := (pb_hasDerivWithinAt n x).ofReal_comp
    convert h using 1
    push_cast
    ring
  have hv : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (-(s + n))) (Set.uIcc (N : ℝ) (M : ℝ)) := by
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hpos x hx))).continuousWithinAt
  have hvv' : ∀ x ∈ Set.Ioo (min (N : ℝ) (M : ℝ)) (max (N : ℝ) (M : ℝ)),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-(s + (n : ℂ))))
        ((-(s + (n : ℂ))) * ((x : ℂ) ^ (-(s + n + 1)))) (Set.Ioi x) x := by
    intro x hx
    rw [min_eq_left hNMR, max_eq_right hNMR] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1, hNR]
    have hd : HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-(s + (n : ℂ))))
        ((-(s + (n : ℂ))) * ((x : ℂ) ^ (-(s + (n : ℂ)) - 1))) (Set.Ioi x) x :=
      (hasDerivAt_ofReal_cpow_const hx0 hne).hasDerivWithinAt
    refine hd.congr_deriv ?_
    rw [show -(s + (n : ℂ)) - 1 = -(s + (n : ℂ) + 1) from by ring]
  have hu' : IntervalIntegrable
      (fun y : ℝ => ((n : ℂ) + 1) * (bernoulliFun n (Int.fract y) : ℂ)) volume (N : ℝ) (M : ℝ) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp (pb_continuous n hn))).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun y : ℝ => (-(s + (n : ℂ))) * ((y : ℂ) ^ (-(s + n + 1))))
      volume (N : ℝ) (M : ℝ) := by
    refine ContinuousOn.intervalIntegrable
      (u := fun y : ℝ => (-(s + (n : ℂ))) * ((y : ℂ) ^ (-(s + n + 1)))) ?_
    intro x hx
    exact ((Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hpos x hx))).const_mul _).continuousWithinAt
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hu hv huu' hvv' hu' hv'
  have hleft : ∫ x in (N : ℝ)..(M : ℝ),
      (bernoulliFun (n + 1) (Int.fract x) : ℂ) * ((-(s + (n : ℂ))) * ((x : ℂ) ^ (-(s + n + 1))))
      = (-(s + (n : ℂ))) * ∫ x in (N : ℝ)..(M : ℝ),
            (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hleft] at key
  have hmid : ∫ x in (N : ℝ)..(M : ℝ),
      (((n : ℂ) + 1) * (bernoulliFun n (Int.fract x) : ℂ)) * (x : ℂ) ^ (-(s + n))
      = ((n : ℂ) + 1) * ∫ x in (N : ℝ)..(M : ℝ),
            (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hmid] at key
  have hkey2 : ((n : ℂ) + 1) *
        (∫ x in (N : ℝ)..(M : ℝ), (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n)))
      = (bernoulliFun (n + 1) (Int.fract ((M : ℝ))) : ℂ) * ((M : ℂ) ^ (-(s + n)))
        - (bernoulliFun (n + 1) (Int.fract ((N : ℝ))) : ℂ) * ((N : ℂ) ^ (-(s + n)))
        + (s + (n : ℂ)) * ∫ x in (N : ℝ)..(M : ℝ),
            (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1)) := by
    linear_combination key
  have hgoal : (∫ x in (N : ℝ)..(M : ℝ),
        (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n)))
      = ((bernoulliFun (n + 1) (Int.fract ((M : ℝ))) : ℂ) * ((M : ℂ) ^ (-(s + n)))
        - (bernoulliFun (n + 1) (Int.fract ((N : ℝ))) : ℂ) * ((N : ℂ) ^ (-(s + n)))
        + (s + (n : ℂ)) * ∫ x in (N : ℝ)..(M : ℝ),
            (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1))) / ((n : ℂ) + 1) := by
    rw [eq_div_iff hden]
    linear_combination hkey2
  rw [hgoal]
  field_simp

/-! ## The integral over `(N, ∞)` -/

/-- The kernel at a natural number is the Bernoulli number. -/
private theorem pb_natCast (n k : ℕ) :
    (bernoulliFun n (Int.fract ((k : ℝ))) : ℂ) = ((_root_.bernoulli n : ℚ) : ℂ) := by
  rw [Int.fract_natCast, bernoulliFun_eval_zero]
  push_cast
  ring

private theorem pb_boundary_tendsto (n : ℕ) (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun m : ℕ =>
      (bernoulliFun (n + 1) (Int.fract ((m : ℝ))) : ℂ) * ((m : ℂ) ^ (-(s + (n : ℂ)))))
      Filter.atTop (nhds 0) := by
  have hc := Complex.cpow_tendsto (s := s + (n : ℂ) + 1) (show (1 : ℝ) < (s + (n : ℂ) + 1).re by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith)
  have hM0 : Filter.Tendsto (fun m : ℕ => ((m : ℂ) ^ (-(s + (n : ℂ))))) Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr (fun m => ?_) hc
    rw [show 1 - (s + (n : ℂ) + 1) = -(s + (n : ℂ)) from by ring]
  have hconst : ∀ m : ℕ,
      (bernoulliFun (n + 1) (Int.fract ((m : ℝ))) : ℂ) = ((_root_.bernoulli (n + 1) : ℚ) : ℂ) :=
    fun m => pb_natCast (n + 1) m
  simp only [hconst]
  simpa using hM0.const_mul (((_root_.bernoulli (n + 1) : ℚ) : ℂ))

private theorem pb_ibp_Ioi (n : ℕ) (hn : 2 ≤ n) (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ∫ x in Set.Ioi (N : ℝ), (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n))
      = -((bernoulliFun (n + 1) (Int.fract ((N : ℝ))) : ℂ) * ((N : ℂ) ^ (-(s + n))) / ((n : ℂ) + 1))
        + (s + n) / ((n : ℂ) + 1) *
            ∫ x in Set.Ioi (N : ℝ),
              (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1)) := by
  set F : ℕ → ℂ := fun m => ∫ x in (N : ℝ)..((m : ℝ)),
    (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n)) with hF
  set G : ℕ → ℂ := fun m => ∫ x in (N : ℝ)..((m : ℝ)),
    (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1)) with hG
  set B : ℕ → ℂ := fun m =>
    (bernoulliFun (n + 1) (Int.fract ((m : ℝ))) : ℂ) * ((m : ℂ) ^ (-(s + (n : ℂ)))) with hB
  set c2 : ℂ := (bernoulliFun (n + 1) (Int.fract ((N : ℝ))) : ℂ) * ((N : ℂ) ^ (-(s + (n : ℂ))))
    with hc2
  have hlim_F : Filter.Tendsto F Filter.atTop
      (nhds (∫ x in Set.Ioi (N : ℝ), (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n)))) := by
    rw [hF]
    exact intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := Filter.atTop)
      (b := fun m : ℕ => ((m : ℝ)))
      (f := fun x : ℝ => (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n)))
      ((N : ℝ)) (pb_integrable n hn N hN (a := -(s + (n : ℂ))) (by
        have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re]
        linarith)) tendsto_natCast_atTop_atTop
  have hlim_G : Filter.Tendsto G Filter.atTop
      (nhds (∫ x in Set.Ioi (N : ℝ),
        (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1)))) := by
    rw [hG]
    exact intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := Filter.atTop)
      (b := fun m : ℕ => ((m : ℝ)))
      (f := fun x : ℝ => (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1)))
      ((N : ℝ)) (pb_integrable (n + 1) (by omega) N hN (a := -(s + (n : ℂ) + 1)) (by
        have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
        linarith)) tendsto_natCast_atTop_atTop
  have hlim_B : Filter.Tendsto B Filter.atTop (nhds 0) := pb_boundary_tendsto n N hs
  have hlim_c : Filter.Tendsto (fun m : ℕ => B m / ((n : ℂ) + 1) - c2 / ((n : ℂ) + 1)
        + (s + (n : ℂ)) / ((n : ℂ) + 1) * G m)
      Filter.atTop (nhds (0 / ((n : ℂ) + 1) - c2 / ((n : ℂ) + 1)
        + (s + (n : ℂ)) / ((n : ℂ) + 1) *
          (∫ x in Set.Ioi (N : ℝ),
            (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1))))) :=
    ((hlim_B.div_const _).sub_const _).add (hlim_G.const_mul _)
  have heq : F =ᶠ[Filter.atTop] (fun m : ℕ => B m / ((n : ℂ) + 1) - c2 / ((n : ℂ) + 1)
        + (s + (n : ℂ)) / ((n : ℂ) + 1) * G m) := by
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    rw [hF, hB, hG, hc2]
    exact pb_ibp_interval n hn N m hN hm hs
  have hfin : (∫ x in Set.Ioi (N : ℝ), (bernoulliFun n (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n)))
      = 0 / ((n : ℂ) + 1) - c2 / ((n : ℂ) + 1)
        + (s + (n : ℂ)) / ((n : ℂ) + 1) *
          (∫ x in Set.Ioi (N : ℝ),
            (bernoulliFun (n + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + n + 1))) :=
    tendsto_nhds_unique hlim_F (hlim_c.congr' heq.symm)
  rw [hfin, hc2]
  ring

/-! ## The doubling step and the general identity -/

/-- One doubling step of the remainder: iterating `pb_ibp_Ioi` from `2k` to `2k+2`. -/
private theorem pb_rem_step (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) {s : ℂ}
    (hs : 0 < s.re) :
    (∏ i ∈ Finset.range (2 * k), (s + (i : ℂ))) / (((2 * k).factorial : ℕ) : ℂ) *
        (∫ x in Set.Ioi (N : ℝ),
          (bernoulliFun (2 * k) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((2 * k : ℕ) : ℂ))))
      = -((((_root_.bernoulli (2 * k + 2) : ℚ) : ℂ)) / (((2 * k + 2).factorial : ℕ) : ℂ) *
            (∏ i ∈ Finset.range (2 * k + 1), (s + (i : ℂ))) *
            (N : ℂ) ^ (-(s + ((2 * k : ℕ) : ℂ) + 1)))
        + (∏ i ∈ Finset.range (2 * k + 2), (s + (i : ℂ))) / (((2 * k + 2).factorial : ℕ) : ℂ) *
            (∫ x in Set.Ioi (N : ℝ),
              (bernoulliFun (2 * k + 2) (Int.fract x) : ℂ) *
                (x : ℂ) ^ (-(s + ((2 * k + 2 : ℕ) : ℂ)))) := by
  have hcast2 : ((2 * k + 1 : ℕ) : ℂ) = ((2 * k : ℕ) : ℂ) + 1 := by push_cast; ring
  have hcast3 : ((2 * k + 2 : ℕ) : ℂ) = ((2 * k : ℕ) : ℂ) + 2 := by push_cast; ring
  have hnn : (2 * k + 1) + 1 = 2 * k + 2 := by ring
  have hc3 : ((2 * k : ℕ) : ℂ) + 1 + 1 = ((2 * k + 2 : ℕ) : ℂ) := by push_cast; ring
  have hassoc : (s + ((2 * k : ℕ) : ℂ)) + 1 = s + (((2 * k : ℕ) : ℂ) + 1) := by ring
  have hexp2 : -((s + ((2 * k : ℕ) : ℂ)) + 1 + 1) = -(s + ((2 * k + 2 : ℕ) : ℂ)) := by
    push_cast; ring
  have h1 := pb_ibp_Ioi (2 * k) (by omega) N hN hs
  have h2 := pb_ibp_Ioi (2 * k + 1) (by omega) N hN hs
  rw [hcast2, hnn, hc3, ← hassoc, hexp2] at h2
  rw [pb_natCast (2 * k + 2) N] at h2
  have hb1 : (bernoulliFun (2 * k + 1) (Int.fract ((N : ℝ))) : ℂ) = 0 := by
    rw [pb_natCast]
    have hodd : Odd (2 * k + 1) := ⟨k, by ring⟩
    rw [_root_.bernoulli_eq_zero_of_odd hodd (by omega)]
    simp
  rw [hb1] at h1
  simp only [zero_mul, zero_div, neg_zero, zero_add] at h1
  rw [h1, h2]
  have eP1 : (∏ i ∈ Finset.range (2 * k + 1), (s + (i : ℂ)))
      = (∏ i ∈ Finset.range (2 * k), (s + (i : ℂ))) * (s + ((2 * k : ℕ) : ℂ)) :=
    Finset.prod_range_succ _ _
  have eP2 : (∏ i ∈ Finset.range (2 * k + 2), (s + (i : ℂ)))
      = (∏ i ∈ Finset.range (2 * k), (s + (i : ℂ))) * (s + ((2 * k : ℕ) : ℂ)) *
          (s + ((2 * k : ℕ) : ℂ) + 1) := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring, Finset.prod_range_succ,
      Finset.prod_range_succ]
    simp only [hcast2]
    ring
  have hf2 : (((2 * k + 2).factorial : ℕ) : ℂ)
      = (((2 * k).factorial : ℕ) : ℂ) * (((2 * k : ℕ) : ℂ) + 1) * (((2 * k : ℕ) : ℂ) + 2) := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [eP2, eP1, hf2]
  simp only [hcast2, hcast3]
  have hD1 : (((2 * k).factorial : ℕ) : ℂ) ≠ 0 := by
    have h : ((2 * k).factorial : ℕ) ≠ 0 := Nat.factorial_ne_zero _
    exact_mod_cast h
  have hD2 : ((2 * k : ℕ) : ℂ) + 1 ≠ 0 := by
    have h : ((2 * k : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    intro hh
    exact h (by exact_mod_cast congrArg Complex.re hh)
  have hD3 : ((2 * k : ℕ) : ℂ) + 2 ≠ 0 := by
    have h : ((2 * k : ℕ) : ℝ) + 2 ≠ 0 := by positivity
    intro hh
    exact h (by exact_mod_cast congrArg Complex.re hh)
  field_simp

/-- The general order-`2m` Euler summation identity with the periodic Bernoulli remainder. -/
private theorem em_general (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∀ m : ℕ, 1 ≤ m →
      riemannZeta s -
          ((∑ k ∈ Finset.Icc (1 : ℕ) N, (1 : ℂ) / (k : ℂ) ^ s) - 1 / (2 * (N : ℂ) ^ s))
        = (N : ℂ) ^ (1 - s) / (s - 1)
          + (∑ j ∈ Finset.range m,
              (((_root_.bernoulli (2 * j + 2) : ℚ) : ℂ) / (((2 * j + 2).factorial : ℕ) : ℂ) *
                (∏ i ∈ Finset.range (2 * j + 1), (s + (i : ℂ))) *
                (N : ℂ) ^ (-(s + (((2 * j + 1 : ℕ)) : ℂ)))))
          - ((∏ i ∈ Finset.range (2 * m), (s + (i : ℂ))) / (((2 * m).factorial : ℕ) : ℂ) *
              ∫ x in Set.Ioi (N : ℝ),
                (bernoulliFun (2 * m) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((2 * m : ℕ) : ℂ)))) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have hz := LeanLab.RamareSaouter2003.Decomp563a.em_q_zeta537 N hN hs hs1
    rw [hz]
    have hset : Finset.range (N + 1) = insert 0 (Finset.Icc (1 : ℕ) N) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      simp at hs
    have hsum : (∑ n ∈ Finset.range (N + 1), (1 : ℂ) / (n : ℂ) ^ s)
        = ∑ k ∈ Finset.Icc (1 : ℕ) N, (1 : ℂ) / (k : ℂ) ^ s := by
      rw [hset, Finset.sum_insert (by simp)]
      simp [Complex.zero_cpow hs0]
    rw [hsum]
    have hc1 : (∑ j ∈ Finset.range 1,
        (((_root_.bernoulli (2 * j + 2) : ℚ) : ℂ) / (((2 * j + 2).factorial : ℕ) : ℂ) *
          (∏ i ∈ Finset.range (2 * j + 1), (s + (i : ℂ))) *
          (N : ℂ) ^ (-(s + (((2 * j + 1 : ℕ)) : ℂ)))))
        = s * (1 / 12) * (N : ℂ) ^ (-(s + 1)) := by
      rw [Finset.sum_range_one, _root_.bernoulli_two, Finset.prod_range_one]
      norm_num
      all_goals try ring
      all_goals simp
    rw [hc1]
    have hN0 : (N : ℂ) ≠ 0 := by
      have h : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have h' : (N : ℝ) ≠ 0 := ne_of_gt h
      exact_mod_cast h'
    have hhalf : -((N : ℂ) ^ (-s)) / 2 + 1 / (2 * (N : ℂ) ^ s) = 0 := by
      rw [Complex.cpow_neg N s, one_div, mul_inv]
      ring
    have hpole : (-((N : ℂ) ^ (1 - s))) / (1 - s) = (N : ℂ) ^ (1 - s) / (s - 1) := by
      have h1s : (1 : ℂ) - s ≠ 0 := by
        intro h
        exact hs1 (by linear_combination -h)
      field_simp
      ring
    have hI2 : (∫ x in Set.Ioi (N : ℝ),
          (bernoulliFun 2 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((2 : ℕ) : ℂ))))
        = 2 * ∫ x in Set.Ioi (N : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      rw [bernoulliFun_two]
      push_cast
      ring
    have hprod : (∏ i ∈ Finset.range (2 * 1), (s + (i : ℂ))) = s * (s + 1) := by
      rw [show 2 * 1 = 1 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_one]
      push_cast
      ring
    have hfac : (((2 * 1).factorial : ℕ) : ℂ) = 2 := by norm_num
    have hIp : (∏ i ∈ Finset.range (2 * 1), (s + (i : ℂ))) / (((2 * 1).factorial : ℕ) : ℂ) *
        (∫ x in Set.Ioi (N : ℝ),
          (bernoulliFun (2 * 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((2 * 1 : ℕ) : ℂ))))
        = s * (s + 1) *
          ∫ x in Set.Ioi (N : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)) := by
      rw [hprod, hfac, hI2]
      ring
    rw [hIp]
    linear_combination hpole + hhalf
  | succ k hk ih =>
    have h2k : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h2k]
    have hstep := pb_rem_step k hk N hN hs
    have hpow : -(s + ((2 * k : ℕ) : ℂ) + 1) = -(s + (((2 * k + 1 : ℕ)) : ℂ)) := by
      push_cast; ring
    rw [hpow] at hstep
    rw [Finset.sum_range_succ]
    linear_combination ih - hstep

/-- The concrete order-ten identity at `N = 10`, in multiplicative shape. -/
private theorem em_concrete {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s -
        ((∑ n ∈ Finset.Icc (1 : ℕ) 9, (1 : ℂ) / (n : ℂ) ^ s) + 1 / (2 * (10 : ℂ) ^ s))
      = (10 : ℂ) ^ (1 - s) / (s - 1) + s * (1 / 12) * (10 : ℂ) ^ (-(s + 1))
        - (∏ i ∈ Finset.range 3, (s + (i : ℂ))) * (1 / 720) * (10 : ℂ) ^ (-(s + 3))
        + (∏ i ∈ Finset.range 5, (s + (i : ℂ))) * (1 / 30240) * (10 : ℂ) ^ (-(s + 5))
        - (∏ i ∈ Finset.range 7, (s + (i : ℂ))) * (1 / 1209600) * (10 : ℂ) ^ (-(s + 7))
        + (∏ i ∈ Finset.range 9, (s + (i : ℂ))) * (1 / 47900160) * (10 : ℂ) ^ (-(s + 9))
        - (∏ i ∈ Finset.range 10, (s + (i : ℂ))) / 3628800 *
            (∫ x in Set.Ioi (10 : ℝ),
              (bernoulliFun 10 (Int.fract x) : ℂ) / (x : ℂ) ^ (s + 10)) := by
  have h10 : (10 : ℂ) ≠ 0 := by norm_num
  have h := em_general 10 (by norm_num) hs hs1 5 (by norm_num)
  have hten : ((10 : ℕ) : ℂ) = (10 : ℂ) := by norm_num
  rw [hten] at h
  have hIoi : ((10 : ℕ) : ℝ) = (10 : ℝ) := by norm_num
  rw [hIoi] at h
  have h25 : (2 * 5 : ℕ) = 10 := by norm_num
  rw [h25] at h
  have hsum10 : (∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℂ) / (k : ℂ) ^ s) - 1 / (2 * (10 : ℂ) ^ s)
      = (∑ n ∈ Finset.Icc (1 : ℕ) 9, (1 : ℂ) / (n : ℂ) ^ s) + 1 / (2 * (10 : ℂ) ^ s) := by
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 9 + 1) _]
    norm_num
    try ring
  rw [hsum10] at h
  have hrem : (∫ x in Set.Ioi (10 : ℝ),
        (bernoulliFun 10 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + (10 : ℂ))))
      = ∫ x in Set.Ioi (10 : ℝ), (bernoulliFun 10 (Int.fract x) : ℂ) / (x : ℂ) ^ (s + 10) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (x : ℂ) ≠ 0 := by
      have hx' : (0 : ℝ) < x := by
        have h10x : (10 : ℝ) < x := hx
        linarith
      have : (x : ℝ) ≠ 0 := ne_of_gt hx'
      exact_mod_cast this
    rw [Complex.cpow_neg, div_eq_mul_inv]
    try ring
  rw [hrem] at h
  have e0 : (((_root_.bernoulli (2 * 0 + 2) : ℚ) : ℂ) / (((2 * 0 + 2).factorial : ℕ) : ℂ) *
        (∏ i ∈ Finset.range (2 * 0 + 1), (s + (i : ℂ))) *
        (10 : ℂ) ^ (-(s + (((2 * 0 + 1 : ℕ)) : ℂ))))
      = s * (1 / 12) * (10 : ℂ) ^ (-(s + 1)) := by
    rw [_root_.bernoulli_two, Finset.prod_range_one]
    norm_num
    all_goals try ring
  have e1 : (((_root_.bernoulli (2 * 1 + 2) : ℚ) : ℂ) / (((2 * 1 + 2).factorial : ℕ) : ℂ) *
        (∏ i ∈ Finset.range (2 * 1 + 1), (s + (i : ℂ))) *
        (10 : ℂ) ^ (-(s + (((2 * 1 + 1 : ℕ)) : ℂ))))
      = -((∏ i ∈ Finset.range 3, (s + (i : ℂ))) * (1 / 720) * (10 : ℂ) ^ (-(s + 3))) := by
    have hB : _root_.bernoulli 4 = (-1 / 30 : ℚ) := by decide +kernel
    rw [hB]
    norm_num
    all_goals try ring
  have e2 : (((_root_.bernoulli (2 * 2 + 2) : ℚ) : ℂ) / (((2 * 2 + 2).factorial : ℕ) : ℂ) *
        (∏ i ∈ Finset.range (2 * 2 + 1), (s + (i : ℂ))) *
        (10 : ℂ) ^ (-(s + (((2 * 2 + 1 : ℕ)) : ℂ))))
      = (∏ i ∈ Finset.range 5, (s + (i : ℂ))) * (1 / 30240) * (10 : ℂ) ^ (-(s + 5)) := by
    have hB : _root_.bernoulli 6 = (1 / 42 : ℚ) := by decide +kernel
    rw [hB]
    norm_num
    all_goals try ring
  have e3 : (((_root_.bernoulli (2 * 3 + 2) : ℚ) : ℂ) / (((2 * 3 + 2).factorial : ℕ) : ℂ) *
        (∏ i ∈ Finset.range (2 * 3 + 1), (s + (i : ℂ))) *
        (10 : ℂ) ^ (-(s + (((2 * 3 + 1 : ℕ)) : ℂ))))
      = -((∏ i ∈ Finset.range 7, (s + (i : ℂ))) * (1 / 1209600) * (10 : ℂ) ^ (-(s + 7))) := by
    have hB : _root_.bernoulli 8 = (-1 / 30 : ℚ) := by decide +kernel
    rw [hB]
    norm_num
    all_goals try ring
  have e4 : (((_root_.bernoulli (2 * 4 + 2) : ℚ) : ℂ) / (((2 * 4 + 2).factorial : ℕ) : ℂ) *
        (∏ i ∈ Finset.range (2 * 4 + 1), (s + (i : ℂ))) *
        (10 : ℂ) ^ (-(s + (((2 * 4 + 1 : ℕ)) : ℂ))))
      = (∏ i ∈ Finset.range 9, (s + (i : ℂ))) * (1 / 47900160) * (10 : ℂ) ^ (-(s + 9)) := by
    have hB : _root_.bernoulli 10 = (5 / 66 : ℚ) := by decide +kernel
    rw [hB]
    norm_num
    all_goals try ring
  have hsum5 : (∑ j ∈ Finset.range 5,
        (((_root_.bernoulli (2 * j + 2) : ℚ) : ℂ) / (((2 * j + 2).factorial : ℕ) : ℂ) *
          (∏ i ∈ Finset.range (2 * j + 1), (s + (i : ℂ))) *
          (10 : ℂ) ^ (-(s + (((2 * j + 1 : ℕ)) : ℂ)))))
      = s * (1 / 12) * (10 : ℂ) ^ (-(s + 1))
        - (∏ i ∈ Finset.range 3, (s + (i : ℂ))) * (1 / 720) * (10 : ℂ) ^ (-(s + 3))
        + (∏ i ∈ Finset.range 5, (s + (i : ℂ))) * (1 / 30240) * (10 : ℂ) ^ (-(s + 5))
        - (∏ i ∈ Finset.range 7, (s + (i : ℂ))) * (1 / 1209600) * (10 : ℂ) ^ (-(s + 7))
        + (∏ i ∈ Finset.range 9, (s + (i : ℂ))) * (1 / 47900160) * (10 : ℂ) ^ (-(s + 9)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, e0, e1, e2, e3, e4]
    all_goals try ring
  rw [hsum5] at h
  have hfac : (((2 * 5).factorial : ℕ) : ℂ) = 3628800 := by norm_num
  rw [hfac] at h
  linear_combination h

end

/-- LEAF. Backlund p. 346 display 8 iterated to five correction terms.
This derived refinement uses the standard unshifted tenth Bernoulli
polynomial. The finite H sum is subtracted explicitly. -/
theorem euler10_identity (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    let s : ℂ := (σ : ℂ) + 50 * I
    riemannZeta s - boundaryH σ = correction s - rising s 10 / 3628800 *
      ∫ x : ℝ in Set.Ioi (10 : ℝ), (periodicB10 x : ℂ) / (x : ℂ) ^ (s + 10) := by
  dsimp only
  set s : ℂ := (σ : ℂ) + 50 * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs : 0 < s.re := by rw [hsre]; linarith [hσ.1]
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [hsdef] at him
  have hint : (∫ x : ℝ in Set.Ioi (10 : ℝ), (periodicB10 x : ℂ) / (x : ℂ) ^ (s + 10))
      = ∫ x : ℝ in Set.Ioi (10 : ℝ),
          (bernoulliFun 10 (Int.fract x) : ℂ) / (x : ℂ) ^ (s + 10) := by
    have hcast : (algebraMap ℚ ℝ) = Rat.castHom ℝ := RingHom.ext_rat _ _
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [periodicB10_eq_mathlib, Polynomial.eval₂_eq_eval_map]
    simp only [bernoulliFun, hcast]
  rw [hint]
  simp only [boundaryH]
  rw [← hsdef]
  rw [em_concrete hs hs1]
  have hconv : ∀ (a c w : ℂ), a / (c * (10 : ℂ) ^ w) = a * c⁻¹ * (10 : ℂ) ^ (-w) := by
    intro a c w
    rw [div_eq_mul_inv, mul_inv, Complex.cpow_neg]
    ring
  simp only [correction, rising, hconv]
  ring

/-- Backlund p. 368, uniform complex rising-factorial control. -/
theorem rising_norm_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (m : ℕ) (b : ℝ) (hb : 0 ≤ b) (hmb : 2500 + (m : ℝ) ^ 2 ≤ b ^ 2) :
    ‖rising ((σ : ℂ) + 50 * I) m‖ ≤ b ^ m := by
  unfold rising
  rw [norm_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range m, b := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hcast : (j : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hjm)
      have hnon : 0 ≤ σ + j := by linarith [hσ.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have hmax : σ + j ≤ m := by linarith [hσ.2]
      have he : (σ : ℂ) + 50 * I + j = (((σ + j : ℝ) : ℂ) + 50 * I) := by push_cast; ring
      rw [he]
      change ‖(((σ + j : ℝ) : ℂ)) + ((50 : ℝ) : ℂ) * I‖ ≤ b
      rw [Complex.norm_add_mul_I]
      apply (Real.sqrt_le_iff).mpr
      exact ⟨hb, by nlinarith⟩
    _ = b ^ m := by simp

/-- Backlund p. 368, the tenth Bernoulli integrand has an integrable real majorant. -/
theorem tenth_kernel_bound (σ x : ℝ) (hσ : 1 / 2 ≤ σ) (hx : 1 ≤ x) :
    ‖(periodicB10 x : ℂ) / (x : ℂ) ^ (((σ : ℂ) + 50 * I) + 10)‖ ≤
      (5 / 66 : ℝ) * x ^ (-(21 / 2 : ℝ)) := by
  have hxpos : 0 < x := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero]
  rw [div_eq_mul_inv, ← Real.rpow_neg hxpos.le]
  exact mul_le_mul (periodicB10_bound x)
    (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (Real.rpow_nonneg hxpos.le _) (by norm_num)

/-- Backlund p. 368, the exact elementary integral for the sharper remainder. -/
theorem tenth_majorant_integral :
    (∫ x : ℝ in Set.Ioi (10 : ℝ), (5 / 66 : ℝ) * x ^ (-(21 / 2 : ℝ))) =
      (5 / 66 : ℝ) / ((19 / 2) * (10 : ℝ) ^ 9 * Real.sqrt 10) := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(21 / 2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 10)]
  have hp : (10 : ℝ) ^ (-(21 / 2 : ℝ) + 1) = 1 / ((10 : ℝ) ^ 9 * Real.sqrt 10) := by
    rw [show -(21 / 2 : ℝ) + 1 = -(9 + 1 / 2) by norm_num, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10),
      Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
    rw [← Real.sqrt_eq_rpow]
    norm_num [one_div]
  rw [hp]
  norm_num
  ring

/-- Backlund p. 368, a rational lower bound for every complex power denominator. -/
theorem power_norm_lower (σ : ℝ) (hσ : 1 / 2 ≤ σ) (m : ℕ) :
    (79 / 25 : ℝ) * (10 : ℝ) ^ m ≤
      ‖(10 : ℂ) ^ (((σ : ℂ) + 50 * I) + m)‖ := by
  have hr : (79 / 25 : ℝ) ≤ Real.sqrt 10 := Real.le_sqrt_of_sq_le (by norm_num)
  have hp : Real.sqrt 10 ≤ (10 : ℝ) ^ σ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ
  change _ ≤ ‖(((10 : ℝ) : ℂ)) ^ (((σ : ℂ) + 50 * I) + m)‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 10)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.natCast_re]
  calc
    _ ≤ (10 : ℝ) ^ σ * (10 : ℝ) ^ m := mul_le_mul_of_nonneg_right (hr.trans hp) (by positivity)
    _ = _ := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 10), Real.rpow_natCast]

/-- Backlund p. 368, one finite Euler correction controlled by rational data. -/
theorem finite_term_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (m : ℕ) (b c : ℝ) (hb : 0 ≤ b) (hc : 0 < c) (hmb : 2500 + (m : ℝ) ^ 2 ≤ b ^ 2) :
    ‖rising ((σ : ℂ) + 50 * I) m /
        ((c : ℂ) * (10 : ℂ) ^ (((σ : ℂ) + 50 * I) + m))‖ ≤
      b ^ m / (c * (79 / 25 : ℝ) * (10 : ℝ) ^ m) := by
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have hp := power_norm_lower σ hσ.1 m
  have hn := rising_norm_bound σ hσ m b hb hmb
  have hd : 0 < c * (79 / 25 : ℝ) * (10 : ℝ) ^ m := by positivity
  apply div_le_div₀ (by positivity) hn hd
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hp hc.le

/-- Backlund p. 368, cancellation between the pole term and the first Euler term. -/
theorem pole_first_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖(10 : ℂ) ^ (1 - ((σ : ℂ) + 50 * I)) / (((σ : ℂ) + 50 * I) - 1) +
      ((σ : ℂ) + 50 * I) / (12 * (10 : ℂ) ^ (((σ : ℂ) + 50 * I) + 1))‖ ≤ 0.069 := by
  let s : ℂ := (σ : ℂ) + 50 * I
  have hs : s - 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [s] at hi
  have h10 : (10 : ℂ) ≠ 0 := by norm_num
  have he : (10 : ℂ) ^ (1 - s) / (s - 1) + s / (12 * (10 : ℂ) ^ (s + 1)) =
      ((10 : ℂ) ^ s)⁻¹ * ((s * (s - 1) + 1200) / (120 * (s - 1))) := by
    rw [show 1 - s = -s + 1 by ring, Complex.cpow_add _ _ h10,
      Complex.cpow_add _ _ h10, Complex.cpow_neg, Complex.cpow_one]
    field_simp
    ring
  have hr : (s * (s - 1) + 1200).re = σ ^ 2 - σ - 1300 := by simp [s, Complex.mul_re]; ring
  have hi : (s * (s - 1) + 1200).im = 50 * (2 * σ - 1) := by simp [s, Complex.mul_im]; ring
  have hsq : -1 / 4 ≤ σ ^ 2 - σ ∧ σ ^ 2 - σ ≤ 0 := by
    constructor <;> nlinarith [hσ.1, hσ.2, sq_nonneg (σ - 1 / 2)]
  have hnum : ‖s * (s - 1) + 1200‖ ≤ (1302 : ℝ) := by
    have hre : |(s * (s - 1) + 1200).re| ≤ (1301 : ℝ) := by rw [hr]; exact abs_le.mpr ⟨by linarith [hsq.1], by linarith [hsq.2]⟩
    have him : |(s * (s - 1) + 1200).im| ≤ (50 : ℝ) := by rw [hi]; exact abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hR := sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1301) |>.mpr hre
    have hI := sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 50) |>.mpr him
    rw [sq_abs] at hR hI
    have hnorm := Complex.sq_norm (s * (s - 1) + 1200)
    rw [Complex.normSq_apply] at hnorm
    nlinarith [norm_nonneg (s * (s - 1) + 1200)]
  have hden : (50 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simpa [s] using h
  have hp := power_norm_lower σ hσ.1 0
  norm_num at hp
  change ‖(10 : ℂ) ^ (1 - s) / (s - 1) + s / (12 * (10 : ℂ) ^ (s + 1))‖ ≤ _
  rw [he, norm_mul, norm_inv, norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  have hfrac : ‖s * (s - 1) + 1200‖ / (120 * ‖s - 1‖) ≤ (1302 / 6000 : ℝ) := by
    apply div_le_div₀ (by norm_num) hnum (by norm_num : (0 : ℝ) < 6000)
    linarith
  have hinv : ‖(10 : ℂ) ^ s‖⁻¹ ≤ (25 / 79 : ℝ) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 79 / 25) hp
    simpa only [one_div, inv_div, one_mul] using hh
  have hh := mul_le_mul hinv hfrac (by positivity) (by norm_num : (0 : ℝ) ≤ 25 / 79)
  exact hh.trans (by norm_num)

/-- Backlund p. 368, all finite correction terms fit the repaired budget. -/
theorem correction_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖correction ((σ : ℂ) + 50 * I)‖ ≤ 0.196 := by
  have h0 := pole_first_bound σ hσ
  have h3 := finite_term_bound σ hσ 3 (50.1 : ℝ) 720 (by norm_num) (by norm_num) (by norm_num)
  have h5 := finite_term_bound σ hσ 5 (50.3 : ℝ) 30240 (by norm_num) (by norm_num) (by norm_num)
  have h7 := finite_term_bound σ hσ 7 (50.5 : ℝ) 1209600 (by norm_num) (by norm_num) (by norm_num)
  have h9 := finite_term_bound σ hσ 9 (50.9 : ℝ) 47900160 (by norm_num) (by norm_num) (by norm_num)
  unfold correction
  have h := (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add h0 h3)) h5)) h7)) h9)
  exact h.trans (by norm_num)

/-- Backlund p. 368, the tenth-order integral remainder fits the repaired budget. -/
theorem tenth_remainder_bound (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖rising ((σ : ℂ) + 50 * I) 10 / 3628800 *
      ∫ x : ℝ in Set.Ioi (10 : ℝ), (periodicB10 x : ℂ) /
        (x : ℂ) ^ (((σ : ℂ) + 50 * I) + 10)‖ ≤ 0.084 := by
  have hi : IntegrableOn (fun x : ℝ => (5 / 66 : ℝ) * x ^ (-(21 / 2 : ℝ))) (Set.Ioi (10 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(21 / 2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 10)).const_mul _
  have hiB := norm_integral_le_of_norm_le hi (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact tenth_kernel_bound σ x hσ.1 (by change (10 : ℝ) < x at hx; linarith))
  rw [tenth_majorant_integral] at hiB
  have hroot : (79 / 25 : ℝ) ≤ Real.sqrt 10 := Real.le_sqrt_of_sq_le (by norm_num)
  have hB : (5 / 66 : ℝ) / ((19 / 2) * (10 : ℝ) ^ 9 * Real.sqrt 10) ≤
      (5 / 66 : ℝ) / ((19 / 2) * (10 : ℝ) ^ 9 * (79 / 25)) := by gcongr
  have hprod := rising_norm_bound σ hσ 10 51 (by norm_num) (by norm_num)
  rw [norm_mul, norm_div]
  norm_num only [Complex.norm_ofNat]
  have hh := mul_le_mul (div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 3628800))
    (hiB.trans hB) (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 51 ^ 10 / 3628800)
  exact hh.trans (by norm_num)

/-- Backlund p. 368, the exact original K target with a sharper certified budget.
CONDITIONAL ON euler10_identity. The five-term and remainder budgets are proved. -/
theorem boundaryK (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I) - boundaryH σ‖ ≤ 0.281 := by
  rw [euler10_identity σ hσ]
  exact ((norm_sub_le _ _).trans (add_le_add (correction_bound σ hσ)
    (tenth_remainder_bound σ hσ))).trans (by norm_num)

end LeanLab.RamareSaouter2003.Decomp563d

#print axioms LeanLab.RamareSaouter2003.Decomp563d.periodicB10_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563d.rising_norm_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563d.tenth_kernel_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563d.tenth_majorant_integral
#print axioms LeanLab.RamareSaouter2003.Decomp563d.euler10_identity

#print axioms LeanLab.RamareSaouter2003.Decomp563d.boundaryH

#print axioms LeanLab.RamareSaouter2003.Decomp563d.rising

#print axioms LeanLab.RamareSaouter2003.Decomp563d.periodicB10

#print axioms LeanLab.RamareSaouter2003.Decomp563d.correction

#print axioms LeanLab.RamareSaouter2003.Decomp563d.power_norm_lower

#print axioms LeanLab.RamareSaouter2003.Decomp563d.finite_term_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563d.pole_first_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563d.correction_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563d.tenth_remainder_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563d.boundaryK

#print axioms LeanLab.RamareSaouter2003.Decomp563d.periodicB10_eq_mathlib
