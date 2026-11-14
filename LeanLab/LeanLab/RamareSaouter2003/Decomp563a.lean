import Mathlib
import LeanLab.PNTPort.StrongPNT.ZetaBounds

/-!
Backlund p. 346 display 8 and p. 361 display 52.
The Euler identity is separated from the complex integral norm estimate.
This file does not import Decomp537a or its descendants.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp563a
open Real Complex MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 2000000

/- The following Euler summation development reuses the proof merged on main
in commit 79b318e5c0 by OMOS DeepSeek V4.1 Flash Low. Its private helpers are
exposed under this independent namespace because importing Decomp537a is forbidden.
The source file and all of its declarations remain untouched. -/

theorem hasDerivWithinAt_fract537 (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => Int.fract y) 1 (Set.Ioi x) x := by
  have hfloor : ∀ᶠ y in 𝓝[Set.Ioi x] x, (⌊y⌋ : ℝ) = (⌊x⌋ : ℝ) := by
    have hopen : Set.Iio ((⌊x⌋ : ℝ) + 1) ∈ 𝓝 (x : ℝ) :=
      isOpen_Iio.mem_nhds (Int.lt_floor_add_one x)
    filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with y hy hyx
    have hyx' : x < y := hyx
    have h : ⌊y⌋ = ⌊x⌋ :=
      Int.floor_eq_iff.mpr ⟨by linarith [Int.floor_le x], hy⟩
    exact_mod_cast h
  have heq : (fun y : ℝ => y - (⌊x⌋ : ℝ)) =ᶠ[𝓝[Set.Ioi x] x] (fun y : ℝ => Int.fract y) := by
    filter_upwards [hfloor] with y hy
    rw [← hy]
    exact Int.self_sub_floor y
  have hpt : x - (⌊x⌋ : ℝ) = Int.fract x := Int.self_sub_floor x
  exact (heq.hasDerivWithinAt_iff hpt).mp ((hasDerivAt_id x).sub_const (⌊x⌋ : ℝ)).hasDerivWithinAt


theorem hasDerivWithinAt_q537 (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => Int.fract y ^ 2 / 2 - Int.fract y / 2 + 1 / 12)
      (Int.fract x - 1 / 2) (Set.Ioi x) x := by
  have h := hasDerivWithinAt_fract537 x
  have h2 : HasDerivWithinAt (fun y : ℝ => Int.fract y ^ 2 / 2) (Int.fract x) (Set.Ioi x) x := by
    have hp := h.pow 2
    have hd := hp.div_const 2
    convert hd using 1
    ring
  have h3 : HasDerivWithinAt (fun y : ℝ => Int.fract y / 2) (1 / 2) (Set.Ioi x) x := by
    have hd := h.div_const 2
    simpa using hd
  have h4 := (h2.sub h3).add_const (1 / 12)
  convert h4 using 1


theorem continuous_q_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 := by
  have h : ContinuousOn (fun y : ℝ => y ^ 2 / 2 - y / 2 + 1 / 12) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hf : (fun y : ℝ => y ^ 2 / 2 - y / 2 + 1 / 12) 0
      = (fun y : ℝ => y ^ 2 / 2 - y / 2 + 1 / 12) 1 := by norm_num
  simpa [Function.comp_def] using h.comp_fract'' hf

theorem abs_q_le537 (x : ℝ) :
    |Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12| ≤ 1 / 12 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have h2 : Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12
      = (Int.fract x - 1 / 2) ^ 2 / 2 - 1 / 24 := by ring
  rw [h2, abs_le]
  have h3 : (Int.fract x - 1 / 2) ^ 2 ≤ 1 / 4 := by
    nlinarith [h0, h1, mul_nonneg h0 (sub_nonneg.mpr h1.le)]
  constructor <;> nlinarith

theorem intervalIntegrable_b537 (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => ((Int.fract x - 1 / 2 : ℝ) : ℂ)) volume a b := by
  rw [intervalIntegrable_iff']
  refine Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1) ?_
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem intervalIntegrable_q537 (a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  exact (Complex.continuous_ofReal.comp continuous_q_fract537).continuousOn

theorem ibp_q537 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (hs : 0 < s.re) :
    ∫ x in a..b, ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))
      = ((Int.fract b ^ 2 / 2 - Int.fract b / 2 + 1 / 12 : ℝ) : ℂ) * (b : ℂ) ^ (-(s + 1))
        - ((Int.fract a ^ 2 / 2 - Int.fract a / 2 + 1 / 12 : ℝ) : ℂ) * (a : ℂ) ^ (-(s + 1))
        + (s + 1) * ∫ x in a..b,
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)) := by
  have hne : (-(s + 1) : ℂ) ≠ 0 := by
    intro h
    have h0 : (-(s + 1) : ℂ).re = 0 := by rw [h]; simp
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re] at h0
    linarith
  have hpos : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  have hu : ContinuousOn
      (fun y : ℝ => ((Int.fract y ^ 2 / 2 - Int.fract y / 2 + 1 / 12 : ℝ) : ℂ)) (Set.uIcc a b) :=
    (Complex.continuous_ofReal.comp continuous_q_fract537).continuousOn
  have hv : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (-(s + 1))) (Set.uIcc a b) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hpos x hx))).continuousWithinAt
  have huu' : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt
        (fun y : ℝ => ((Int.fract y ^ 2 / 2 - Int.fract y / 2 + 1 / 12 : ℝ) : ℂ))
        ((Int.fract x - 1 / 2 : ℝ) : ℂ) (Set.Ioi x) x := fun x _ =>
    (hasDerivWithinAt_q537 x).ofReal_comp
  have hvv' : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-(s + 1)))
        ((-(s + 1)) * (x : ℂ) ^ (-(s + 2))) (Set.Ioi x) x := by
    intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hd : HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-(s + 1)))
        ((-(s + 1)) * (x : ℂ) ^ (-(s + 1) - 1)) (Set.Ioi x) x :=
      (hasDerivAt_ofReal_cpow_const hx0 hne).hasDerivWithinAt
    convert hd using 1
    ring
  have hu' : IntervalIntegrable (fun x : ℝ => ((Int.fract x - 1 / 2 : ℝ) : ℂ)) volume a b :=
    intervalIntegrable_b537 a b
  have hv' : IntervalIntegrable (fun y : ℝ => (-(s + 1)) * (y : ℂ) ^ (-(s + 2))) volume a b := by
    refine ContinuousOn.intervalIntegrable (u := fun y : ℝ => (-(s + 1)) * (y : ℂ) ^ (-(s + 2))) ?_
    intro x hx
    exact ((Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hpos x hx))).const_mul
      (-(s + 1))).continuousWithinAt
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hu hv huu' hvv' hu' hv'
  have hleft : ∫ x in a..b,
      ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) *
        ((-(s + 1)) * (x : ℂ) ^ (-(s + 2)))
      = -(s + 1) * ∫ x in a..b,
          ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hleft] at key
  linear_combination key


theorem integrable_b_Ioi537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
      (Set.Ioi (N : ℝ)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcp : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ hNR
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    linarith
  have hmble : AEStronglyMeasurable
      (fun x : ℝ => (((Int.fract x : ℝ) : ℂ) - 1 / 2)) (volume.restrict (Set.Ioi (N : ℝ))) := by
    have hmeas : Measurable fun x : ℝ => (((Int.fract x : ℝ) : ℂ) - 1 / 2) :=
      (Complex.continuous_ofReal.measurable.comp measurable_fract).sub measurable_const
    exact hmeas.aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Ioi (N : ℝ))),
      ‖(((Int.fract x : ℝ) : ℂ) - 1 / 2)‖ ≤ 1 := by
    filter_upwards with x
    have h0 := Int.fract_nonneg x
    have h1 := Int.fract_lt_one x
    have he : (((Int.fract x : ℝ) : ℂ) - 1 / 2) = ((Int.fract x - 1 / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  exact (hcp.bdd_mul hmble hbdd).congr (ae_of_all _ (fun x => by ring))


theorem floor_kernel_eq537 (x : ℝ) :
    (((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - ((x : ℝ) : ℂ)) = -((((Int.fract x : ℝ)) : ℂ) - 1 / 2) := by
  have h : ((Int.fract x : ℝ)) = x - ((⌊x⌋ : ℤ) : ℝ) := Int.self_sub_floor x
  rw [h]
  push_cast
  ring

/-- The `q`-kernel is integrable against `x ^ (-(s+2))` on `Ioi N`. -/
theorem integrable_q_Ioi537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ =>
      ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)))
      (Set.Ioi (N : ℝ)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcp : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(s + 2))) (Set.Ioi (N : ℝ)) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ hNR
    simp only [Complex.neg_re, Complex.add_re]
    norm_num
    linarith
  have hmeas : AEStronglyMeasurable (fun x : ℝ =>
      ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ))
      (volume.restrict (Set.Ioi (N : ℝ))) :=
    Complex.continuous_ofReal.measurable.comp continuous_q_fract537.measurable |>.aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Ioi (N : ℝ))),
      ‖((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ)‖ ≤ 1 := by
    filter_upwards with x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_q_le537 x).trans (by norm_num)
  exact (hcp.bdd_mul hmeas hbdd).congr (ae_of_all _ (fun x => by ring))

/-- The second-order Euler Maclaurin formula on a finite interval `[N, M]`. -/
theorem em_one_interval537 (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) {s : ℂ}
    (hs : 0 < s.re) :
    ∫ x in (N : ℝ)..(M : ℝ), (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1))
      = (1 / 12) * (((M : ℝ) : ℂ) ^ (-(s + 1)) - ((N : ℝ) : ℂ) ^ (-(s + 1)))
        + (s + 1) * ∫ x in (N : ℝ)..(M : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hq := ibp_q537 (N : ℝ) (M : ℝ) hNR hNMR hs
  have hgoal : (∫ x in (N : ℝ)..(M : ℝ),
        (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
      = ∫ x in (N : ℝ)..(M : ℝ),
          ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    push_cast
    ring
  rw [hgoal, hq]
  have e1 : ((Int.fract ((M : ℝ)) ^ 2 / 2 - Int.fract ((M : ℝ)) / 2 + 1 / 12 : ℝ) : ℂ)
      = (1 / 12 : ℂ) := by rw [Int.fract_natCast]; norm_num
  have e2 : ((Int.fract ((N : ℝ)) ^ 2 / 2 - Int.fract ((N : ℝ)) / 2 + 1 / 12 : ℝ) : ℂ)
      = (1 / 12 : ℂ) := by rw [Int.fract_natCast]; norm_num
  rw [e1, e2]
  ring

/-- The `b`-kernel integral on `Ioi N` in terms of the `q`-kernel. -/
theorem em_one_Ioi537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Set.Ioi (N : ℝ), (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
      = -(1 / 12) * ((N : ℝ) : ℂ) ^ (-(s + 1))
        + (s + 1) * (∫ x in Set.Ioi (N : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))) := by
  have hlim_b := intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := Filter.atTop)
    (b := fun n : ℕ => ((n : ℝ)))
    (f := fun x : ℝ => (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
    ((N : ℝ)) (integrable_b_Ioi537 N hN hs) tendsto_natCast_atTop_atTop
  have hlim_q := intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := Filter.atTop)
    (b := fun n : ℕ => ((n : ℝ)))
    (f := fun x : ℝ =>
      ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)))
    ((N : ℝ)) (integrable_q_Ioi537 N hN hs) tendsto_natCast_atTop_atTop
  have hM : Tendsto (fun M : ℕ => (((M : ℝ) : ℂ)) ^ (-(s + 1))) Filter.atTop (𝓝 0) := by
    have h := Complex.cpow_tendsto (s := s + 2)
      (show (1 : ℝ) < (s + 2).re by simp only [Complex.add_re]; norm_num; linarith)
    refine h.congr (fun M => ?_)
    push_cast
    congr 1
    ring
  have hlim_c : Tendsto (fun M : ℕ =>
      (1 / 12) * ((((M : ℝ) : ℂ)) ^ (-(s + 1)) - ((N : ℝ) : ℂ) ^ (-(s + 1)))
        + (s + 1) * (∫ x in (N : ℝ)..((M : ℝ)),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))))
      Filter.atTop
      (𝓝 ((1 / 12) * (0 - ((N : ℝ) : ℂ) ^ (-(s + 1)))
        + (s + 1) * (∫ x in Set.Ioi (N : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))))) :=
    ((hM.sub_const _).const_mul _).add (hlim_q.const_mul _)
  have heq : (fun M : ℕ => ∫ x in (N : ℝ)..((M : ℝ)),
      (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
      =ᶠ[Filter.atTop] (fun M : ℕ =>
      (1 / 12) * ((((M : ℝ) : ℂ)) ^ (-(s + 1)) - ((N : ℝ) : ℂ) ^ (-(s + 1)))
        + (s + 1) * (∫ x in (N : ℝ)..((M : ℝ)),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)))) := by
    filter_upwards [Filter.eventually_ge_atTop N] with M hM'
    exact em_one_interval537 N M hN hM' hs
  have hfin := tendsto_nhds_unique hlim_b (hlim_c.congr' heq.symm)
  rw [hfin]
  ring

/-- Second-order Euler Maclaurin for `ζ` with the `q`-kernel remainder, on `Re s > 0`. -/
theorem em_q_zeta537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s
      = (∑ n ∈ Finset.range (N + 1), (1 : ℂ) / (n : ℂ) ^ s)
        + (-(N : ℂ) ^ (1 - s)) / (1 - s) + (-(N : ℂ) ^ (-s)) / 2
        + s * (1 / 12) * (N : ℂ) ^ (-(s + 1))
        - s * (s + 1) * (∫ x in Set.Ioi (N : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))) := by
  have hz : riemannZeta0 N s = riemannZeta s := Zeta0EqZeta hN hs h1
  rw [← hz, riemannZeta0_apply]
  have hker : (∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
      = -(∫ x in Set.Ioi (N : ℝ),
          (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1))) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [floor_kernel_eq537]
    ring
  rw [hker, em_one_Ioi537 N hN hs]
  push_cast
  ring


/-- Backlund p. 361 display 52, the complex periodic Bernoulli kernel majorant. -/
theorem bernoulli_kernel_bound (s : ℂ) (hs : 1 ≤ s.re) (x : ℝ) (hx : 1 ≤ x) :
    ‖(((Int.fract x) ^ 2 - Int.fract x + 1 / 6 : ℝ) : ℂ) /
      (x : ℂ) ^ (s + 2)‖ ≤ (1 / 6 : ℝ) * x ^ (-3 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hb : |(Int.fract x) ^ 2 - Int.fract x + 1 / 6| ≤ (1 / 6 : ℝ) := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
    · have h0 := Int.fract_nonneg x
      have h1 := Int.fract_lt_one x
      nlinarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, Complex.re_ofNat]
  rw [div_eq_mul_inv, ← Real.rpow_neg hxpos.le]
  exact mul_le_mul hb (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
    (Real.rpow_nonneg hxpos.le _) (by norm_num)

/-- Backlund p. 361 display 52, the complex Bernoulli integral norm estimate. -/
theorem bernoulli_integral_bound (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖∫ x : ℝ in Set.Ioi (n : ℝ),
      (((Int.fract x) ^ 2 - Int.fract x + 1 / 6 : ℝ) : ℂ) /
        (x : ℂ) ^ (s + 2)‖ ≤ 1 / (12 * (n : ℝ) ^ 2) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hi : IntegrableOn (fun x : ℝ => (1 / 6 : ℝ) * x ^ (-3 : ℝ))
      (Set.Ioi (n : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hnpos).const_mul _
  have h := norm_integral_le_of_norm_le hi (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact bernoulli_kernel_bound s hs x (by
      have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact hnreal.trans hx.le))
  have he : (∫ x : ℝ in Set.Ioi (n : ℝ), (1 / 6 : ℝ) * x ^ (-3 : ℝ)) =
      1 / (12 * (n : ℝ) ^ 2) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hnpos]
    norm_num [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat]
    ring
  exact h.trans_eq he

/-- Backlund p. 346 display 8, the second-order Euler summation identity.
The representation reuses the independent copy of the upstream Euler development.
The norm estimate is proved separately. -/
theorem euler8_identity (n : ℕ) (hn : 1 ≤ n) (s : ℂ)
    (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    riemannZeta s =
      (∑ k ∈ Finset.Icc (1 : ℕ) (n - 1), (1 : ℂ) / (k : ℂ) ^ s) +
      1 / (2 * (n : ℂ) ^ s) + (n : ℂ) ^ (1 - s) / (s - 1) +
      s / (12 * (n : ℂ) ^ (s + 1)) - s * (s + 1) / 2 *
        ∫ x : ℝ in Set.Ioi (n : ℝ),
          (((Int.fract x) ^ 2 - Int.fract x + 1 / 6 : ℝ) : ℂ) /
            (x : ℂ) ^ (s + 2) := by
  have hspos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hset : Finset.range n = insert 0 (Finset.Icc (1 : ℕ) (n - 1)) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsum : (∑ k ∈ Finset.range (n + 1), (1 : ℂ) / (k : ℂ) ^ s) =
      (∑ k ∈ Finset.Icc (1 : ℕ) (n - 1), (1 : ℂ) / (k : ℂ) ^ s) + 1 / (n : ℂ) ^ s := by
    rw [Finset.sum_range_succ, hset, Finset.sum_insert (by simp)]
    rw [Nat.cast_zero, Complex.zero_cpow hs0, div_zero, zero_add]
  have hpole : (-(n : ℂ) ^ (1 - s)) / (1 - s) = (n : ℂ) ^ (1 - s) / (s - 1) := by
    have hn : 1 - s ≠ 0 := by intro h; apply hs1; linear_combination -h
    field_simp
    ring
  have hB : (∫ x in Set.Ioi (n : ℝ),
      ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))) =
      (1 / 2 : ℂ) * ∫ x in Set.Ioi (n : ℝ),
        (((Int.fract x) ^ 2 - Int.fract x + 1 / 6 : ℝ) : ℂ) / (x : ℂ) ^ (s + 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [Complex.cpow_neg]
    push_cast
    ring
  rw [em_q_zeta537 n hn hspos hs1, hsum, hpole, hB]
  simp only [Complex.cpow_neg]
  ring

/-- Backlund p. 361 display 52, the exact original Euler norm target.
The Euler identity and integral norm bound have clean axioms. -/
theorem euler8_bernoulli_bound (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ)
    (hσ : σ ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      (harmonic (n - 1) : ℝ) + 1 / (2 * (n : ℝ)) + 1 / t +
        Real.sqrt (t ^ 2 + 9 / 4) / (12 * (n : ℝ) ^ 2) +
        Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) / (24 * (n : ℝ) ^ 2) := by
  let s : ℂ := (σ : ℂ) + t * I
  have hsre : s.re = σ := by simp [s]
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have htpos : 0 < t := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [s] at this
    linarith
  have hp (x : ℝ) (hx : 1 ≤ x) (a : ℝ) (ha : a ≤ σ) :
      ‖(1 : ℂ) / (x : ℂ) ^ s‖ ≤ x ^ (-a) := by
    rw [norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x),
      hsre, one_div, ← Real.rpow_neg (by linarith : 0 ≤ x)]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hsum : ‖∑ k ∈ Finset.Icc (1 : ℕ) (n - 1), (1 : ℂ) / (k : ℂ) ^ s‖ ≤
      (harmonic (n - 1) : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    simpa [Real.rpow_neg_one] using hp k hkreal 1 hσ.1
  have hhalf : ‖(1 : ℂ) / (2 * (n : ℂ) ^ s)‖ ≤ 1 / (2 * (n : ℝ)) := by
    have hh := hp n hnreal 1 hσ.1
    have he : (1 : ℂ) / (2 * (n : ℂ) ^ s) = ((1 : ℂ) / (n : ℂ) ^ s) / 2 := by ring
    rw [he, norm_div]
    norm_num only [Complex.norm_ofNat]
    have hh' : ‖(1 : ℂ) / (n : ℂ) ^ s‖ ≤ (n : ℝ)⁻¹ := by simpa [Real.rpow_neg_one] using hh
    calc
      _ ≤ (n : ℝ)⁻¹ / 2 := div_le_div_of_nonneg_right hh' (by norm_num)
      _ = _ := by ring
  have hpole : ‖(n : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 / t := by
    have hnum : ‖(n : ℂ) ^ (1 - s)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      apply Real.rpow_le_one_of_one_le_of_nonpos hnreal
      simp only [Complex.sub_re, Complex.one_re, hsre]
      linarith [hσ.1]
    have hden : t ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      simpa [s, abs_of_pos htpos] using h
    rw [norm_div]
    exact div_le_div₀ (by norm_num) hnum htpos hden
  have hterm : ‖s / (12 * (n : ℂ) ^ (s + 1))‖ ≤ ‖s‖ / (12 * (n : ℝ) ^ 2) := by
    have hpow : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (s + 1).re := by
      apply Real.rpow_le_rpow_of_exponent_le hnreal
      simp only [Complex.add_re, Complex.one_re, hsre]
      linarith [hσ.1]
    rw [norm_div, norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    norm_num only [Complex.norm_ofNat]
    apply div_le_div_of_nonneg_left (norm_nonneg s) (by positivity)
    simpa using mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 12)
  have hrem : ‖s * (s + 1) / 2 *
      ∫ x : ℝ in Set.Ioi (n : ℝ),
        (((Int.fract x) ^ 2 - Int.fract x + 1 / 6 : ℝ) : ℂ) /
          (x : ℂ) ^ (s + 2)‖ ≤ ‖s * (s + 1)‖ / (24 * (n : ℝ) ^ 2) := by
    rw [norm_mul, norm_div]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ (‖s * (s + 1)‖ / 2) * (1 / (12 * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (bernoulli_integral_bound n hn s (by simpa [hsre] using hσ.1))
          (by positivity)
      _ = _ := by ring
  have hnorm1 : ‖s‖ ≤ Real.sqrt (t ^ 2 + 9 / 4) := by
    dsimp [s]
    rw [Complex.norm_add_mul_I]
    apply Real.sqrt_le_sqrt
    nlinarith [hσ.1, hσ.2]
  have hnorm2 : ‖s + 1‖ ≤ Real.sqrt (t ^ 2 + 25 / 4) := by
    have he : s + 1 = (((σ + 1 : ℝ) : ℂ) + t * I) := by dsimp [s]; push_cast; ring
    rw [he, Complex.norm_add_mul_I]
    apply Real.sqrt_le_sqrt
    nlinarith [hσ.1, hσ.2]
  have hprod : ‖s * (s + 1)‖ ≤ Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) := by
    rw [norm_mul, Real.sqrt_mul (by positivity : 0 ≤ t ^ 2 + 9 / 4)]
    exact mul_le_mul hnorm1 hnorm2 (norm_nonneg _) (Real.sqrt_nonneg _)
  have hz := euler8_identity n hn s (by simpa [hsre] using hσ.1) hs1
  change ‖riemannZeta s‖ ≤ _
  rw [hz]
  calc
    _ ≤ (harmonic (n - 1) : ℝ) + 1 / (2 * (n : ℝ)) + 1 / t +
        ‖s‖ / (12 * (n : ℝ) ^ 2) + ‖s * (s + 1)‖ / (24 * (n : ℝ) ^ 2) := by
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add hsum hhalf)) hpole)) hterm)) hrem)
    _ ≤ _ := by gcongr

end LeanLab.RamareSaouter2003.Decomp563a

#print axioms LeanLab.RamareSaouter2003.Decomp563a.bernoulli_kernel_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563a.bernoulli_integral_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563a.euler8_identity

#print axioms LeanLab.RamareSaouter2003.Decomp563a.euler8_bernoulli_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563a.hasDerivWithinAt_fract537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.hasDerivWithinAt_q537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.continuous_q_fract537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.abs_q_le537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.intervalIntegrable_b537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.intervalIntegrable_q537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.ibp_q537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.integrable_b_Ioi537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.floor_kernel_eq537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.integrable_q_Ioi537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.em_one_interval537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.em_one_Ioi537

#print axioms LeanLab.RamareSaouter2003.Decomp563a.em_q_zeta537
