import LeanLab.ExceptionalSet.Decomp523a

/-!
Refutation of the statement `leaf_fejer_convolution_majorant` of
`SPLIT_leaf_one_sided_majorant.lean`, as that statement is written there.

In that statement the kernel and the periodic indicator are both evaluated at
the same point `x - t`, so the integral over `t` does not depend on `x`: it is
the mass of the Fejer type kernel on the enlarged arc `[a - s, b + s)`, and it
is not a convolution.  For an arc near one half the kernel of cutoff two,
`1 + cos (2 * pi * u)`, is small, and the right side drops below one while the
left side equals one.

Counterexample: `H = 2`, `s = 1/6`, `a = 499/1000`, `b = 501/1000`, `x = 1/2`.
The left side is `1`.  The right side is
`12 * (503/1500 - sin (pi/3 + pi/500) / pi)`, which is below `0.71`.

This refutes the statement as written, not the underlying mathematics: a true
majorant needs the indicator evaluated at `t`, not at `x - t`.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp523a

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- Real part of `eC`. -/
private lemma refute_eC_re (v : ℝ) : (eC v).re = Real.cos (2 * Real.pi * v) := by
  unfold eC
  have h : 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) =
      ((2 * Real.pi * v : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re]

/-- Imaginary part of `eC`. -/
private lemma refute_eC_im (v : ℝ) : (eC v).im = Real.sin (2 * Real.pi * v) := by
  unfold eC
  have h : 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) =
      ((2 * Real.pi * v : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_im]

/-- The kernel of cutoff two is `1 + cos (2 * pi * u)`. -/
private lemma refute_kernel_two (u : ℝ) :
    (1 / ((2 : ℕ) : ℝ)) * ‖∑ k ∈ Finset.range 2, eC (((k : ℝ) + 1) * u)‖ ^ 2 =
      1 + Real.cos (2 * Real.pi * u) := by
  have hsum : (∑ k ∈ Finset.range 2, eC (((k : ℝ) + 1) * u)) = eC u + eC (2 * u) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have e1 : (((0 : ℕ) : ℝ) + 1) * u = u := by push_cast; ring
    have e2 : (((1 : ℕ) : ℝ) + 1) * u = 2 * u := by push_cast; ring
    rw [e1, e2]
  rw [hsum, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    refute_eC_re, refute_eC_re, refute_eC_im, refute_eC_im]
  have hc : Real.cos (2 * Real.pi * (2 * u)) = 2 * Real.cos (2 * Real.pi * u) ^ 2 - 1 := by
    rw [show 2 * Real.pi * (2 * u) = 2 * (2 * Real.pi * u) by ring, Real.cos_two_mul]
  have hs : Real.sin (2 * Real.pi * (2 * u)) =
      2 * Real.sin (2 * Real.pi * u) * Real.cos (2 * Real.pi * u) := by
    rw [show 2 * Real.pi * (2 * u) = 2 * (2 * Real.pi * u) by ring, Real.sin_two_mul]
  rw [hc, hs]
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2]
  linear_combination (1 / 2 : ℝ) * (1 + 2 * Real.cos (2 * Real.pi * u)) ^ 2 *
    Real.sin_sq_add_cos_sq (2 * Real.pi * u)

/-- A continuous function cut off by a threshold indicator integrates to the
integral up to the threshold. -/
private lemma refute_integral_cut (φ : ℝ → ℝ) (hφ : Continuous φ) (c d e : ℝ)
    (hcd : c ≤ d) (hde : d ≤ e) :
    ∫ u in c..e, φ u * (if u < d then (1 : ℝ) else 0) = ∫ u in c..d, φ u := by
  have hanti : Antitone fun u : ℝ => (if u < d then (1 : ℝ) else 0) := by
    intro p q hpq
    by_cases hq : q < d
    · have hp : p < d := lt_of_le_of_lt hpq hq
      simp [hp, hq]
    · by_cases hp : p < d <;> simp [hp, hq]
  have hint : ∀ p q : ℝ, IntervalIntegrable
      (fun u : ℝ => φ u * (if u < d then (1 : ℝ) else 0)) MeasureTheory.volume p q :=
    fun p q => (hanti.intervalIntegrable).continuousOn_mul hφ.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint c d) (hint d e)]
  have hz : ∫ u in d..e, φ u * (if u < d then (1 : ℝ) else 0) = 0 := by
    have hcong : (∫ u in d..e, φ u * (if u < d then (1 : ℝ) else 0)) =
        ∫ _u in d..e, (0 : ℝ) :=
      intervalIntegral.integral_congr_uIoo (fun u hu => by
        rw [Set.uIoo_of_le hde] at hu
        show φ u * (if u < d then (1 : ℝ) else 0) = 0
        rw [ite_eq_right (not_lt.mpr hu.1.le), mul_zero])
    rw [hcong, intervalIntegral.integral_zero]
  rw [hz, add_zero]
  exact intervalIntegral.integral_congr_uIoo (fun u hu => by
    rw [Set.uIoo_of_le hcd] at hu
    show φ u * (if u < d then (1 : ℝ) else 0) = φ u
    rw [ite_eq_left hu.2, mul_one])

/-- Over any full period, a continuous periodic function times the periodic
indicator of an arc integrates to its integral over the arc. -/
private lemma refute_period_arc (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hper : Function.Periodic φ 1) (c L r : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    ∫ u in r..r + 1, φ u * (if Int.fract (u - c) < L then (1 : ℝ) else 0) =
      ∫ u in c..c + L, φ u := by
  have hg : Function.Periodic
      (fun u : ℝ => φ u * (if Int.fract (u - c) < L then (1 : ℝ) else 0)) 1 := by
    intro u
    show φ (u + 1) * (if Int.fract (u + 1 - c) < L then (1 : ℝ) else 0) =
      φ u * (if Int.fract (u - c) < L then (1 : ℝ) else 0)
    rw [hper u, show u + 1 - c = u - c + 1 by ring, Int.fract_add_one]
  rw [hg.intervalIntegral_add_eq r c]
  have hstep : (∫ u in c..c + 1, φ u * (if Int.fract (u - c) < L then (1 : ℝ) else 0)) =
      ∫ u in c..c + 1, φ u * (if u < c + L then (1 : ℝ) else 0) := by
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    rw [Set.uIoo_of_le (by linarith : c ≤ c + 1)] at hu
    obtain ⟨hu0, hu1⟩ := hu
    have hfract : Int.fract (u - c) = u - c := by
      rw [Int.fract_eq_self]
      constructor <;> linarith
    have hcond : (Int.fract (u - c) < L) ↔ (u < c + L) := by
      rw [hfract]
      constructor <;> intro h <;> linarith
    show φ u * (if Int.fract (u - c) < L then (1 : ℝ) else 0) =
      φ u * (if u < c + L then (1 : ℝ) else 0)
    simp only [hcond]
  rw [hstep]
  exact refute_integral_cut φ hφ c (c + L) (c + 1) (by linarith) (by linarith)

/-- The integral of the kernel of cutoff two over an interval. -/
private lemma refute_integral_kernel (c d : ℝ) :
    ∫ u in c..d, (1 + Real.cos (2 * Real.pi * u)) =
      (d - c) + (Real.sin (2 * Real.pi * d) - Real.sin (2 * Real.pi * c)) / (2 * Real.pi) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hderiv : ∀ u ∈ Set.uIcc c d,
      HasDerivAt (fun v : ℝ => v + Real.sin (2 * Real.pi * v) / (2 * Real.pi))
        (1 + Real.cos (2 * Real.pi * u)) u := by
    intro u _
    have h1 : HasDerivAt (fun v : ℝ => 2 * Real.pi * v) (2 * Real.pi) u := by
      simpa using (hasDerivAt_id u).const_mul (2 * Real.pi)
    have h2 : HasDerivAt (fun v : ℝ => Real.sin (2 * Real.pi * v))
        (Real.cos (2 * Real.pi * u) * (2 * Real.pi)) u := h1.sin
    have h3 := (hasDerivAt_id u).add (h2.div_const (2 * Real.pi))
    have hval : (1 : ℝ) + Real.cos (2 * Real.pi * u) * (2 * Real.pi) / (2 * Real.pi) =
        1 + Real.cos (2 * Real.pi * u) := by
      field_simp
    rw [hval] at h3
    exact h3
  have hcont : Continuous fun u : ℝ => (1 + Real.cos (2 * Real.pi * u)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  ring

/-- The first integral of the statement at cutoff two, in closed form. -/
private lemma refute_first_integral (a b s x : ℝ)
    (hL0 : 0 ≤ b - a + 2 * s) (hL1 : b - a + 2 * s ≤ 1) :
    (∫ t in (0 : ℝ)..1,
        (1 / ((2 : ℕ) : ℝ)) * ‖∑ k ∈ Finset.range 2, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
          (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) =
      (b - a + 2 * s) +
        (Real.sin (2 * Real.pi * (b + s)) - Real.sin (2 * Real.pi * (a - s))) /
          (2 * Real.pi) := by
  have hcongr : (∫ t in (0 : ℝ)..1,
        (1 / ((2 : ℕ) : ℝ)) * ‖∑ k ∈ Finset.range 2, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
          (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) =
      ∫ t in (0 : ℝ)..1,
        (fun u : ℝ => (1 + Real.cos (2 * Real.pi * u)) *
          (if Int.fract (u - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) (x - t) := by
    apply intervalIntegral.integral_congr
    intro t _
    show (1 / ((2 : ℕ) : ℝ)) * ‖∑ k ∈ Finset.range 2, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
          (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0) =
      (1 + Real.cos (2 * Real.pi * (x - t))) *
          (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)
    rw [refute_kernel_two]
  rw [hcongr, intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => (1 + Real.cos (2 * Real.pi * u)) *
      (if Int.fract (u - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) x]
  have hend : x - 0 = (x - 1) + 1 := by ring
  rw [hend]
  have hper : Function.Periodic (fun u : ℝ => (1 + Real.cos (2 * Real.pi * u))) 1 := by
    intro u
    show 1 + Real.cos (2 * Real.pi * (u + 1)) = 1 + Real.cos (2 * Real.pi * u)
    rw [show 2 * Real.pi * (u + 1) = 2 * Real.pi * u + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  have hcont : Continuous fun u : ℝ => (1 + Real.cos (2 * Real.pi * u)) := by fun_prop
  rw [refute_period_arc (fun u : ℝ => (1 + Real.cos (2 * Real.pi * u))) hcont hper
    (a - s) (b - a + 2 * s) (x - 1) hL0 hL1, refute_integral_kernel]
  have e1 : a - s + (b - a + 2 * s) = b + s := by ring
  rw [e1]
  ring

/-- The mean of the periodic arc indicator is the arc length. -/
private lemma refute_second_integral (c L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    (∫ y in (0 : ℝ)..1, (if Int.fract (y - c) < L then (1 : ℝ) else 0)) = L := by
  have hcongr : (∫ y in (0 : ℝ)..1, (if Int.fract (y - c) < L then (1 : ℝ) else 0)) =
      ∫ y in (0 : ℝ)..0 + 1,
        (fun _ : ℝ => (1 : ℝ)) y * (if Int.fract (y - c) < L then (1 : ℝ) else 0) := by
    rw [zero_add]
    apply intervalIntegral.integral_congr
    intro y _
    show (if Int.fract (y - c) < L then (1 : ℝ) else 0) =
      1 * (if Int.fract (y - c) < L then (1 : ℝ) else 0)
    rw [one_mul]
  rw [hcongr, refute_period_arc (fun _ : ℝ => (1 : ℝ)) continuous_const (fun _ => rfl)
    c L 0 hL0 hL1]
  simp

/-- Lower bound for the sine at the two arc ends: `sin (pi/3 + pi/500)` is at
least `sin (pi/3)`, whose square is `3/4`. -/
private lemma refute_sin_lower :
    (17 / 20 : ℝ) < Real.sin (Real.pi / 3 + Real.pi / 500) := by
  have hmono : Real.sin (Real.pi / 3) ≤ Real.sin (Real.pi / 3 + Real.pi / 500) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  rw [Real.sin_pi_div_three] at hmono
  have h3 : (17 / 10 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

/-- The statement `leaf_fejer_convolution_majorant` of
`SPLIT_leaf_one_sided_majorant.lean` is false as written.  Counterexample:
`H = 2`, `s = 1/6`, `a = 499/1000`, `b = 501/1000`, `x = 1/2`.  The hypotheses
hold, the left side is `1` since the fractional part of `1/2` lies in `[a, b)`,
and the right side equals `12 * (503/1500 - sin (pi/3 + pi/500) / pi)`, which
is below `0.71`.  The cause is that the kernel and the indicator are both taken
at `x - t`, so the integral is the kernel mass on the arc `[a - s, b + s)` near
one half, where the kernel `1 + cos (2 * pi * u)` is small. -/
theorem leaf_fejer_convolution_majorant_false :
    ¬ (∀ (a b : ℝ) (H : ℕ), 0 ≤ a → a ≤ b → b ≤ 1 → 2 ≤ H →
    ∀ (s : ℝ), 0 < s → 2 * s = 1 / ((H : ℝ) + 1) →
    ∀ x : ℝ,
      (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        12 * (∫ t in (0 : ℝ)..1,
          (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
            (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
          + 12 * (b - a + 2 * s)
          - 12 * (∫ y in (0 : ℝ)..1,
              (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))) := by
  intro h
  have key := h (499 / 1000) (501 / 1000) 2 (by norm_num) (by norm_num) (by norm_num)
    (le_refl 2) (1 / 6) (by norm_num) (by norm_num) (1 / 2)
  have hfr : Int.fract (1 / 2 : ℝ) = 1 / 2 := by
    rw [Int.fract_eq_self]
    constructor <;> norm_num
  rw [hfr, ite_eq_left (by constructor <;> norm_num),
    refute_first_integral (499 / 1000) (501 / 1000) (1 / 6) (1 / 2) (by norm_num) (by norm_num),
    refute_second_integral (499 / 1000 - 1 / 6) (501 / 1000 - 499 / 1000 + 2 * (1 / 6))
      (by norm_num) (by norm_num)] at key
  -- the two sines
  have hS := refute_sin_lower
  have hsa : Real.sin (2 * Real.pi * (499 / 1000 - 1 / 6)) =
      Real.sin (Real.pi / 3 + Real.pi / 500) := by
    rw [← Real.sin_pi_sub]
    congr 1
    ring
  have hsb : Real.sin (2 * Real.pi * (501 / 1000 + 1 / 6)) =
      -Real.sin (Real.pi / 3 + Real.pi / 500) := by
    rw [← Real.sin_add_pi]
    congr 1
    ring
  rw [hsa, hsb] at key
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpos : 0 < Real.pi := Real.pi_pos
  -- key : 1 ≤ 12 * (L + (-S - S) / (2 * pi)) + 12 * L - 12 * L
  have hdiv : (-Real.sin (Real.pi / 3 + Real.pi / 500) - Real.sin (Real.pi / 3 + Real.pi / 500)) /
      (2 * Real.pi) = -(Real.sin (Real.pi / 3 + Real.pi / 500) / Real.pi) := by
    field_simp
    ring
  rw [hdiv] at key
  have hq : (17 / 20 : ℝ) / Real.pi < Real.sin (Real.pi / 3 + Real.pi / 500) / Real.pi :=
    div_lt_div_of_pos_right hS hpos
  have hq2 : (126 / 500 : ℝ) < (17 / 20 : ℝ) / Real.pi := by
    rw [lt_div_iff₀ hpos]
    linarith
  linarith

end LeanLab.ExceptionalSet.Decomp523a
