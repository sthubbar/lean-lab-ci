/-
Unit P1122-0114, burst-20261122, CLOUD S25. The Fejér kernel step of the Erdős–Turán
inequality `DQLemma4.ErdosTuranDQ4`, in the proof of L. Kuipers and H. Niederreiter, Uniform
Distribution of Sequences, Wiley 1974, chapter 2, Theorem 2.5, pages 112 to 114, copy in
`papers/KuipersNiederreiter1974-ch2.pdf`, PDF pages 25 to 27, read from the page images.

That proof uses no majorant of an interval indicator. It smooths the discrepancy function with
the Fejér kernel `Σ_{|h| ≤ m} (m + 1 - |h|) e(hx) = sin²((m+1)πx) / sin²(πx)`, display (2.37),
and the one-sided step is the lower bound of the smoothed function at a peak, display (2.39)
and the display after it on page 114. This file states that step and the four kernel facts it
uses. The earlier `leaf_vaaler_trig_majorant` was false, see
`FALSE_leaf_vaaler_trig_majorant.lean`; nothing here depends on it.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.ExceptionalSet.Selberg524Trig
import Mathlib

namespace LeanLab.ExceptionalSet.ETDQ4

open Real Finset

/-- The Fejér kernel of order `m` in real form, the left side of display (2.37), page 113 of
Kuipers and Niederreiter: `Σ_{h=-m}^{m} (m + 1 - |h|) e(hx)`, with the terms `h` and `-h`
paired into `2 (m + 1 - h) cos(2πhx)`. The closed form `sin²((m+1)πx) / sin²(πx)` of (2.37) is
`Selberg524.fejer_closed524`. -/
noncomputable def fejK (m : ℕ) (x : ℝ) : ℝ :=
  ((m : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) * cos (2 * π * ((h : ℝ) * x))

/-- The closed form (2.37), page 113, multiplied out: `sin²(πx) K_m(x) = sin²((m+1)πx)`. -/
theorem fejK_closed (m : ℕ) (x : ℝ) :
    sin (π * x) ^ 2 * fejK m x = sin (π * (((m : ℝ) + 1) * x)) ^ 2 :=
  LeanLab.ExceptionalSet.Selberg524.fejer_closed524 m x

/-- Display (2.37), page 113, the right side `sin²((m+1)πx)/sin²(πx)` is nonnegative,
and equals `(m+1)²` at integers, so the kernel is nonnegative everywhere. -/
theorem fejK_nonneg (m : ℕ) (x : ℝ) : 0 ≤ fejK m x := by
  by_cases hs : sin (π * x) = 0
  · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
    have hx : x = n := by
      have := Real.pi_pos
      field_simp at hn
      nlinarith [hn]
    unfold fejK
    apply add_nonneg (by positivity)
    apply mul_nonneg (by norm_num)
    apply sum_nonneg
    intro h hh
    rw [mem_Icc] at hh
    have hc : cos (2 * π * ((h : ℝ) * x)) = 1 := by
      rw [hx, show 2 * π * ((h : ℝ) * (n : ℝ)) = ((h * n : ℤ) : ℝ) * (2 * π) by push_cast; ring]
      exact Real.cos_int_mul_two_pi _
    rw [hc, mul_one]
    have : (h : ℝ) ≤ m := by exact_mod_cast hh.2
    linarith
  · have hp : 0 < sin (π * x) ^ 2 := by positivity
    have := fejK_closed m x
    by_contra hneg
    push Not at hneg
    have : sin (π * x) ^ 2 * fejK m x < 0 := mul_neg_of_pos_of_neg hp hneg
    nlinarith [sq_nonneg (sin (π * (((m : ℝ) + 1) * x)))]

/-- The evenness of `sin²((m+1)πx)/sin²(πx)` used on page 114 line 1, "using the evenness". -/
theorem fejK_neg (m : ℕ) (x : ℝ) : fejK m (-x) = fejK m x := by
  unfold fejK
  congr 2
  apply sum_congr rfl
  intro h _
  rw [show 2 * π * ((h : ℝ) * -x) = -(2 * π * ((h : ℝ) * x)) by ring, cos_neg]

/-- Page 114 line 2, "The integral of this function over `[0, 1/2]` is `(m + 1)/2` by
(2.37)": only the constant term `m + 1` survives, since `∫_0^{1/2} cos(2πhx) dx = 0` for every
integer `h ≥ 1`. -/
theorem fejK_integral_half (m : ℕ) :
    ∫ x in (0 : ℝ)..(1 / 2), fejK m x = ((m : ℝ) + 1) / 2 := by
  have hcos : ∀ h ∈ Icc 1 m,
      ∫ x in (0 : ℝ)..(1 / 2), (((m : ℝ) + 1) - (h : ℝ)) * cos (2 * π * ((h : ℝ) * x)) = 0 := by
    intro h hh
    rw [mem_Icc] at hh
    rw [intervalIntegral.integral_const_mul]
    have hc : (2 * π * (h : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < h := by exact_mod_cast hh.1
      positivity
    have e : (fun x : ℝ => cos (2 * π * ((h : ℝ) * x))) = fun x => cos ((2 * π * (h : ℝ)) * x) := by
      funext x; ring_nf
    rw [e, intervalIntegral.integral_comp_mul_left (fun x => cos x) hc, integral_cos]
    rw [show 2 * π * (h : ℝ) * (1 / 2) = (h : ℝ) * π by ring, Real.sin_nat_mul_pi]
    simp
  unfold fejK
  have hc2 : IntervalIntegrable
      (fun x : ℝ => 2 * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) * cos (2 * π * ((h : ℝ) * x)))
      MeasureTheory.volume 0 (1 / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add intervalIntegrable_const hc2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · rw [sum_eq_zero hcos]
    simp
    ring
  · intro h _
    apply Continuous.intervalIntegrable
    fun_prop

/-- Page 114, the bound used in the display after (2.39), `sin²((m+1)πx)/sin²(πx) ≤
1/sin²(πx) ≤ 1/(4x²)` for `0 < x ≤ 1/2`, "where we used `sin πx ≥ 2x` for `0 ≤ x ≤ 1/2`". -/
theorem fejK_le_inv_sq (m : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    fejK m x ≤ 1 / (4 * x ^ 2) := by
  have hpi := Real.pi_pos
  have hj : 2 / π * (π * x) ≤ sin (π * x) :=
    Real.mul_le_sin (by positivity) (by nlinarith)
  have h2x : 2 * x ≤ sin (π * x) := by
    have : 2 / π * (π * x) = 2 * x := by field_simp
    linarith
  have hsq : 4 * x ^ 2 ≤ sin (π * x) ^ 2 := by nlinarith
  have hcl := fejK_closed m x
  have hle1 : sin (π * x) ^ 2 * fejK m x ≤ 1 := by
    rw [hcl]; exact sin_sq_le_one _
  have hK := fejK_nonneg m x
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem fejK_continuous (m : ℕ) : Continuous (fejK m) := by
  unfold fejK
  fun_prop

theorem fejer_peak_lower_of (K : ℝ → ℝ) (M : ℝ) (hKc : Continuous K)
    (hK0 : ∀ x, 0 ≤ K x) (hKneg : ∀ x, K (-x) = K x)
    (hKint : ∫ x in (0 : ℝ)..(1 / 2), K x = M / 2)
    (hKle : ∀ x, 0 < x → x ≤ 1 / 2 → K x ≤ 1 / (4 * x ^ 2))
    (g : ℝ → ℝ) (d D : ℝ) (hd : 0 < d) (hdD : d ≤ D)
    (hd1 : d ≤ 1) (hg : IntervalIntegrable g MeasureTheory.volume (-(1 / 2)) (1 / 2))
    (hpeak : ∀ x, |x| < d / 2 → d / 2 - x ≤ g x)
    (hlow : ∀ x, -(1 / 2) ≤ x → x ≤ 1 / 2 → -D ≤ g x) :
    d * (M / 2) - 3 * D / (2 * d) ≤
      ∫ x in (-(1 / 2) : ℝ)..(1 / 2), g x * K x := by
  have hD : 0 < D := lt_of_lt_of_le hd hdD
  set a : ℝ := d / 2 with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 2 := by rw [ha]; linarith
  have hgK : IntervalIntegrable (fun x => g x * K x) MeasureTheory.volume (-(1 / 2)) (1 / 2) :=
    hg.mul_continuousOn hKc.continuousOn
  have sub : ∀ u v : ℝ, -(1/2) ≤ u → u ≤ 1/2 → -(1/2) ≤ v → v ≤ 1/2 →
      IntervalIntegrable (fun x => g x * K x) MeasureTheory.volume u v := by
    intro u v hu1 hu2 hv1 hv2
    apply hgK.mono_set
    rw [Set.uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
    intro x hx
    rcases Set.mem_uIcc.1 hx with h | h <;> constructor <;> linarith [h.1, h.2]
  have Kii : ∀ u v : ℝ, IntervalIntegrable K MeasureTheory.volume u v :=
    fun u v => hKc.intervalIntegrable u v
  -- split
  have hsplit : ∫ x in (-(1 / 2) : ℝ)..(1 / 2), g x * K x =
      (∫ x in (-(1 / 2) : ℝ)..(-a), g x * K x) + (∫ x in (-a)..a, g x * K x)
        + ∫ x in a..(1 / 2), g x * K x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (sub _ _ (by linarith) (by linarith) (by linarith) (by linarith))
        (sub _ _ (by linarith) (by linarith) (by linarith) (by linarith)),
      intervalIntegral.integral_add_adjacent_intervals
        (sub _ _ (by linarith) (by linarith) (by linarith) (by linarith))
        (sub _ _ (by linarith) (by linarith) (by linarith) (by linarith))]
  -- left piece
  have hleft : -D * ∫ x in (-(1 / 2) : ℝ)..(-a), K x ≤ ∫ x in (-(1 / 2) : ℝ)..(-a), g x * K x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith) ((Kii _ _).const_mul _)
      (sub _ _ (by linarith) (by linarith) (by linarith) (by linarith))
    intro x hx
    exact mul_le_mul_of_nonneg_right (hlow x hx.1 (by linarith [hx.2])) (hK0 x)
  have hright : -D * ∫ x in a..(1 / 2), K x ≤ ∫ x in a..(1 / 2), g x * K x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ha1 ((Kii _ _).const_mul _)
      (sub _ _ (by linarith) (by linarith) (by linarith) (by linarith))
    intro x hx
    exact mul_le_mul_of_nonneg_right (hlow x (by linarith [hx.1]) hx.2) (hK0 x)
  have hmid : ∫ x in (-a)..a, (a - x) * K x ≤ ∫ x in (-a)..a, g x * K x := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by linarith)
      ((Continuous.mul (by fun_prop) hKc).intervalIntegrable _ _)
      (sub _ _ (by linarith) (by linarith) (by linarith) (by linarith))
    intro x hx
    have : |x| < d / 2 := by rw [abs_lt]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_le_mul_of_nonneg_right (hpeak x this) (hK0 x)
  -- symmetry facts
  have hleftK : ∫ x in (-(1 / 2) : ℝ)..(-a), K x = ∫ x in a..(1 / 2), K x := by
    have := intervalIntegral.integral_comp_neg (a := a) (b := 1/2) (fun x => K x)
    simp only [hKneg] at this
    rw [this]
  have hodd : ∫ x in (-a)..a, x * K x = 0 := by
    have h1 := intervalIntegral.integral_comp_neg (a := -a) (b := a) (fun x => x * K x)
    simp only [hKneg, neg_neg, neg_mul, intervalIntegral.integral_neg] at h1
    linarith
  have hsym : ∫ x in (-a)..a, K x = 2 * ∫ x in (0:ℝ)..a, K x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (Kii (-a) 0) (Kii 0 a)]
    have := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun x => K x)
    simp only [hKneg, neg_zero] at this
    rw [← this]; ring
  have hmideq : ∫ x in (-a)..a, (a - x) * K x = d * ∫ x in (0:ℝ)..a, K x := by
    have e : (fun x => (a - x) * K x) = fun x => a * K x - x * K x := by
      funext x; ring
    have hc : Continuous (fun x : ℝ => x * K x) := continuous_id.mul hKc
    rw [e, intervalIntegral.integral_sub (f := fun x => a * K x) (g := fun x => x * K x)
      ((Kii _ _).const_mul _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hodd, hsym, ha]
    ring
  have htot : ∫ x in (0:ℝ)..a, K x = M / 2 - ∫ x in a..(1 / 2), K x := by
    rw [← hKint, ← intervalIntegral.integral_add_adjacent_intervals (Kii 0 a) (Kii a (1/2))]
    ring
  -- tail bound
  have htail : ∫ x in a..(1 / 2), K x ≤ 1 / (2 * d) := by
    have hcont : ContinuousOn (fun x : ℝ => 1 / (4 * x ^ 2)) (Set.uIcc a (1/2)) := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx
      rw [Set.uIcc_of_le ha1] at hx
      have : 0 < x := lt_of_lt_of_le ha0 hx.1
      positivity
    have h1 : ∫ x in a..(1 / 2), K x ≤ ∫ x in a..(1 / 2), 1 / (4 * x ^ 2) := by
      apply intervalIntegral.integral_mono_on ha1 (Kii _ _) hcont.intervalIntegrable
      intro x hx
      exact hKle x (lt_of_lt_of_le ha0 hx.1) hx.2
    have h2 : ∫ x in a..(1 / 2), 1 / (4 * x ^ 2) = (-1 / (4 * (1/2:ℝ))) - (-1 / (4 * a)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -1 / (4 * x))
      · intro x hx
        rw [Set.uIcc_of_le ha1] at hx
        have hx0 : x ≠ 0 := (lt_of_lt_of_le ha0 hx.1).ne'
        have := ((hasDerivAt_id x).const_mul 4).inv (by simp [hx0])
        convert this.const_mul (-1) using 1
        · funext y; simp [div_eq_mul_inv]
        · simp only [id]; field_simp
      · exact hcont.intervalIntegrable
    rw [h2] at h1
    have : (-1 / (4 * (1/2:ℝ))) - (-1 / (4 * a)) ≤ 1 / (2 * d) := by
      rw [ha]
      have : -1 / (4 * (d / 2)) = -(1 / (2 * d)) := by field_simp; ring
      rw [this]; norm_num
    linarith
  have hI0 : 0 ≤ ∫ x in a..(1 / 2), K x :=
    intervalIntegral.integral_nonneg ha1 (fun x _ => hK0 x)
  have key : (d + 2 * D) * ∫ x in a..(1 / 2), K x ≤ 3 * D / (2 * d) := by
    calc (d + 2 * D) * ∫ x in a..(1 / 2), K x ≤ (d + 2 * D) * (1 / (2 * d)) :=
          mul_le_mul_of_nonneg_left htail (by linarith)
      _ ≤ 3 * D / (2 * d) := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  rw [hsplit]
  rw [hleftK] at hleft
  rw [hmideq, htot] at hmid
  nlinarith [hleft, hright, hmid, key]


/-- Display (2.39), page 113, and the display after it, page 114, the Fejér kernel step.
Here `g` plays `Δ_N(x + a)`, `d` the height `D*_N` of the peak at the chosen point `b`, so that
`Δ_N(x + a) ≥ d/2 - x` for `|x| < d/2`, and `D` is a global bound `Δ_N ≥ -D`. With
`d = D = D*_N` this is the paper's `∫ Δ_N(x+a) K ≥ ((m+1)/2) D*_N - 3/2`; the form with
`d ≤ D` separate lets the peak be approached when the supremum is not attained. The
paper splits the integral at `±d/2`, uses evenness of the kernel, its integral `(m+1)/2` over
`[0, 1/2]`, and `K(x) ≤ 1/(4x²)` on `[d/2, 1/2]`, whose integral is `1/(2d) - 1/2 ≤ 1/(2d)`. -/
theorem fejer_peak_lower (m : ℕ) (g : ℝ → ℝ) (d D : ℝ) (hd : 0 < d) (hdD : d ≤ D)
    (hd1 : d ≤ 1) (hg : IntervalIntegrable g MeasureTheory.volume (-(1 / 2)) (1 / 2))
    (hpeak : ∀ x, |x| < d / 2 → d / 2 - x ≤ g x)
    (hlow : ∀ x, -(1 / 2) ≤ x → x ≤ 1 / 2 → -D ≤ g x) :
    d * (((m : ℝ) + 1) / 2) - 3 * D / (2 * d) ≤
      ∫ x in (-(1 / 2) : ℝ)..(1 / 2), g x * fejK m x :=
  fejer_peak_lower_of (fejK m) ((m : ℝ) + 1) (fejK_continuous m) (fejK_nonneg m) (fejK_neg m)
    (fejK_integral_half m) (fejK_le_inv_sq m) g d D hd hdD hd1 hg hpeak hlow

end LeanLab.ExceptionalSet.ETDQ4
