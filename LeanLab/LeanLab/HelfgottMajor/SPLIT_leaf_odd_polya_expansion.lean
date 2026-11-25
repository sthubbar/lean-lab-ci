import LeanLab.HelfgottMajor.SPLIT_leaf_odd_case_pomerance
import LeanLab.RieselVaughan1983.GaussImprim

/-!
Split of `leaf_odd_polya_expansion` from `SPLIT_leaf_odd_case_pomerance`, the Polya expansion
step of Pomerance, Remarks on the Polya-Vinogradov inequality, Integers 11A 2011, Article 19,
section 4, after Landau, as used for P0014 Helfgott, Major arcs, display 4.20.

The route, with `psi x = fract x - 1/2` and `F_H x = sum_{h <= H} sin (2 pi h x) / (pi h)`:
* `count_sawtooth`, PROVED: the interval indicator of `[1, n]` in terms of `psi` at `-a/q` and
  `(n - a)/q`, summed against `chi`; the mean term `n/q` drops since `sum_a chi a = 0`.
* `sawtooth_tail`, PROVED from `sawtooth_series`, the pointwise sawtooth Fourier series, itself
  PROVED by Dirichlet's test, the logarithm series and Abel's limit theorem: `|psi x + F_H x| <= 1 / (2 pi (H+1) ||x||)` for `x` not an integer, by Abel
  summation `sin_abel_tail` and Jordan's inequality `jordan_fract`; at integers the error is
  exactly `1/2`, proved here as `sawtooth_error_at_integer`.
* `dist_harmonic_sum`, PROVED: `sum_a 1/||(c - a)/q|| <= 2 q (log q + 1 - log 2)`.
* `main_term_gauss`, PROVED: the main term, by the Gauss sums `sum_a chi a e(h a / q) =
  conj chi(h) tau(chi)`, oddness and `|tau| = sqrt q`.
The assembly `leaf_odd_polya_expansion_proved` has no sorry in its dependency chain; it is proved
by the triangle inequality and the endpoint count: the point `a = 0` costs nothing since `chi 0 = 0`, and the
single `a = n mod q` costs `1/2`.

No definition is introduced. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real Filter Topology

/-- Jordan's inequality at `pi x`: `|sin (pi x)| >= 2 ||x||`. -/
theorem jordan_fract (x : ℝ) :
    2 * min (Int.fract x) (1 - Int.fract x) ≤ |sin (π * x)| := by
  set f := Int.fract x with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg x
  have hf1 : f < 1 := Int.fract_lt_one x
  have hxs : |sin (π * x)| = sin (π * f) := by
    have : π * x = π * f + (⌊x⌋ : ℤ) * π := by
      rw [hf, Int.fract]; ring
    rw [this, sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    exact abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos]))
  rw [hxs]
  set m := min f (1 - f) with hm
  have hm0 : 0 ≤ m := le_min hf0 (by linarith)
  have hm2 : m ≤ 1 / 2 := by
    rcases le_total f (1 - f) with h | h
    · rw [hm, min_eq_left h]; linarith
    · rw [hm, min_eq_right h]; linarith
  have hsm : sin (π * f) = sin (π * m) := by
    rcases le_total f (1 - f) with h | h
    · rw [hm, min_eq_left h]
    · rw [hm, min_eq_right h, show π * (1 - f) = π - π * f by ring, sin_pi_sub]
  rw [hsm]
  have hj := mul_le_sin (x := π * m) (by positivity) (by nlinarith [pi_pos])
  have : 2 / π * (π * m) = 2 * m := by field_simp
  linarith

/-- Abel summation with antitone nonnegative weights: `|sum w_i b_i| <= w_0 M` when every
partial sum of `b` is at most `M` in absolute value. -/
theorem abel_bound (w b : ℕ → ℝ) (M : ℝ) (hw : ∀ i, w (i + 1) ≤ w i) (hw0 : ∀ i, 0 ≤ w i)
    (hB : ∀ k, |∑ i ∈ Finset.range (k + 1), b i| ≤ M) (k : ℕ) :
    |∑ i ∈ Finset.range (k + 1), w i * b i| ≤ w 0 * M := by
  have aux : ∀ k, |∑ i ∈ Finset.range (k + 1), w i * b i -
      w k * ∑ i ∈ Finset.range (k + 1), b i| ≤ (w 0 - w k) * M := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ b,
        show ∑ i ∈ Finset.range (k + 1), w i * b i + w (k + 1) * b (k + 1) -
          w (k + 1) * (∑ i ∈ Finset.range (k + 1), b i + b (k + 1)) =
          (∑ i ∈ Finset.range (k + 1), w i * b i - w k * ∑ i ∈ Finset.range (k + 1), b i) +
            (w k - w (k + 1)) * ∑ i ∈ Finset.range (k + 1), b i by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hw k))]
      have := mul_le_mul_of_nonneg_left (hB k) (sub_nonneg.mpr (hw k))
      nlinarith
  have h1 := aux k
  have h2 : |w k * ∑ i ∈ Finset.range (k + 1), b i| ≤ w k * M := by
    rw [abs_mul, abs_of_nonneg (hw0 k)]
    exact mul_le_mul_of_nonneg_left (hB k) (hw0 k)
  calc _ = |(∑ i ∈ Finset.range (k + 1), w i * b i - w k * ∑ i ∈ Finset.range (k + 1), b i) +
        w k * ∑ i ∈ Finset.range (k + 1), b i| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ (w 0 - w k) * M + w k * M := add_le_add h1 h2
    _ = w 0 * M := by ring

/-- The telescoping identity `2 sin (pi x) sum sin (2 pi h x) = cos ((2s-1) pi x) - cos ((2(s+k)-1) pi x)`. -/
theorem sin_partial_telescope (x : ℝ) (s k : ℕ) :
    2 * sin (π * x) * ∑ i ∈ Finset.range k, sin (2 * π * ((s + i : ℕ) : ℝ) * x) =
      cos ((2 * (s : ℝ) - 1) * π * x) - cos ((2 * ((s + k : ℕ) : ℝ) - 1) * π * x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have e1 : (2 * ((s + k : ℕ) : ℝ) - 1) * π * x =
        2 * π * ((s + k : ℕ) : ℝ) * x - π * x := by ring
    have e2 : (2 * ((s + (k + 1) : ℕ) : ℝ) - 1) * π * x =
        2 * π * ((s + k : ℕ) : ℝ) * x + π * x := by push_cast; ring
    rw [e1, e2, cos_sub, cos_add]
    ring

/-- Partial sums of `sin (2 pi h x)` are at most `1/|sin (pi x)|`. -/
theorem sin_partial_bound (x : ℝ) (hx : sin (π * x) ≠ 0) (s k : ℕ) :
    |∑ i ∈ Finset.range k, sin (2 * π * ((s + i : ℕ) : ℝ) * x)| ≤ 1 / |sin (π * x)| := by
  have ht := sin_partial_telescope x s k
  have hpos : 0 < |sin (π * x)| := abs_pos.mpr hx
  have hS : |2 * sin (π * x)| * |∑ i ∈ Finset.range k, sin (2 * π * ((s + i : ℕ) : ℝ) * x)| ≤ 2 := by
    rw [← abs_mul, ht]
    have := abs_sub (cos ((2 * (s : ℝ) - 1) * π * x)) (cos ((2 * ((s + k : ℕ) : ℝ) - 1) * π * x))
    have h1 := abs_cos_le_one ((2 * (s : ℝ) - 1) * π * x)
    have h2 := abs_cos_le_one ((2 * ((s + k : ℕ) : ℝ) - 1) * π * x)
    linarith
  rw [abs_mul, abs_two] at hS
  rw [le_div_iff₀ hpos]
  nlinarith

/-- Pomerance 2011 section 4, the Abel summation step: for `H < N`,
`|sum_{H < h <= N} sin (2 pi h x)/h| <= 1/((H+1) |sin (pi x)|)`. -/
theorem sin_abel_tail (x : ℝ) (hx : Int.fract x ≠ 0) (H N : ℕ) (hHN : H < N) :
    |∑ h ∈ Finset.Icc (H + 1) N, sin (2 * π * h * x) / h| ≤
      1 / (((H : ℝ) + 1) * |sin (π * x)|) := by
  have hsx : sin (π * x) ≠ 0 := by
    have hm : 0 < min (Int.fract x) (1 - Int.fract x) := by
      have h0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
      exact lt_min h0 (by linarith [Int.fract_lt_one x])
    have := jordan_fract x
    intro h0; rw [h0, abs_zero] at this; linarith
  have hIcc : Finset.Icc (H + 1) N = Finset.Ico (H + 1) (N + 1) := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range,
    show N + 1 - (H + 1) = (N - H - 1) + 1 by omega]
  have hab := abel_bound (fun i => 1 / (((H + 1 + i : ℕ) : ℝ)))
    (fun i => sin (2 * π * ((H + 1 + i : ℕ) : ℝ) * x)) (1 / |sin (π * x)|)
    (fun i => by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith)
    (fun i => by positivity)
    (fun k => sin_partial_bound x hsx (H + 1) (k + 1)) (N - H - 1)
  have heq : ∑ i ∈ Finset.range (N - H - 1 + 1), sin (2 * π * ((H + 1 + i : ℕ) : ℝ) * x) /
      ((H + 1 + i : ℕ) : ℝ) = ∑ i ∈ Finset.range (N - H - 1 + 1),
      1 / (((H + 1 + i : ℕ) : ℝ)) * sin (2 * π * ((H + 1 + i : ℕ) : ℝ) * x) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [heq]
  refine hab.trans (le_of_eq ?_)
  simp only [add_zero]
  push_cast
  field_simp

/-- Dirichlet's test, Mathlib `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`: the
sawtooth series `sum sin (2 pi i y)/i` converges for `0 < y < 1`. -/
theorem saw_partial_converges (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    ∃ l, Tendsto (fun n => ∑ i ∈ Finset.range n, sin (2 * π * i * y) / i) atTop (𝓝 l) := by
  have hsy : sin (π * y) ≠ 0 := (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])).ne'
  let w : ℕ → ℝ := fun i => 1 / (((1 + i : ℕ) : ℝ))
  let z : ℕ → ℝ := fun i => sin (2 * π * ((1 + i : ℕ) : ℝ) * y)
  have hw : Antitone w := by
    refine antitone_nat_of_succ_le fun n => ?_
    show 1 / (((1 + (n + 1) : ℕ) : ℝ)) ≤ 1 / (((1 + n : ℕ) : ℝ))
    apply one_div_le_one_div_of_le (by positivity)
    push_cast; linarith
  have hw0 : Tendsto w atTop (𝓝 0) := by
    have : Tendsto (fun i : ℕ => ((1 + i : ℕ) : ℝ)) atTop atTop := by
      have h1 : Tendsto (fun i : ℕ => 1 + i) atTop atTop :=
        tendsto_atTop_mono (fun i => Nat.le_add_left i 1) tendsto_id
      exact tendsto_natCast_atTop_atTop.comp h1
    have h2 := this.inv_tendsto_atTop
    refine h2.congr fun i => ?_
    simp [w]
  have hzb : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ 1 / |sin (π * y)| := by
    intro n
    rw [Real.norm_eq_abs]
    exact sin_partial_bound y hsy 1 n
  have hc : CauchySeq fun n => ∑ i ∈ Finset.range n, w i • z i :=
    hw.cauchySeq_series_mul_of_tendsto_zero_of_bounded hw0 hzb
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨l, ?_⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hl.congr fun n => ?_
  rw [Finset.sum_range_succ']
  simp only [smul_eq_mul, Nat.cast_zero, mul_zero, zero_mul, sin_zero, div_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [w, z]
  push_cast
  ring_nf

/-- The Abel means of the sawtooth series: for `0 <= r < 1`, the imaginary part of the
logarithm series `-log (1 - r e(y)) = sum (r e(y))^n / n`. -/
theorem saw_power (y r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => sin (2 * π * n * y) / n * r ^ n)
      (-Complex.log (1 - (r : ℂ) * Complex.exp (((2 * π * y : ℝ) : ℂ) * Complex.I))).im := by
  have hz : ‖(r : ℂ) * Complex.exp (((2 * π * y : ℝ) : ℂ) * Complex.I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    exact hr1
  have h := Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hz)
  refine h.congr_fun fun n => ?_
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow,
    show (n : ℂ) * (((2 * π * y : ℝ) : ℂ) * Complex.I) = (((2 * π * n * y : ℝ)) : ℂ) * Complex.I by
      push_cast; ring,
    Complex.div_natCast_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  ring

/-- The boundary value: `Im (-log (1 - e(y))) = pi (1/2 - y)` for `0 < y < 1`, from
`1 - e(y) = 2 sin (pi y) e(y/2 - 1/4)`. -/
theorem saw_log_value (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    (-Complex.log (1 - Complex.exp (((2 * π * y : ℝ) : ℂ) * Complex.I))).im = π * (1 / 2 - y) := by
  have hs : 0 < sin (π * y) := sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])
  set θ : ℝ := π * y - π / 2 with hθ
  have hrep : 1 - Complex.exp (((2 * π * y : ℝ) : ℂ) * Complex.I) =
      ((2 * sin (π * y) : ℝ) : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    have c1 : cos θ = sin (π * y) := by rw [hθ, cos_sub_pi_div_two]
    have s1 : sin θ = -cos (π * y) := by rw [hθ, sin_sub_pi_div_two]
    have c2 : cos (2 * π * y) = 1 - 2 * sin (π * y) ^ 2 := by
      rw [show 2 * π * y = 2 * (π * y) by ring, cos_two_mul, cos_sq']; ring
    have s2 : sin (2 * π * y) = 2 * sin (π * y) * cos (π * y) := by
      rw [show 2 * π * y = 2 * (π * y) by ring, sin_two_mul]
    rw [c1, s1, c2, s2]
    push_cast
    ring
  rw [Complex.neg_im, Complex.log_im, hrep, Complex.arg_mul_cos_add_sin_mul_I (by positivity)]
  · rw [hθ]; ring
  · rw [hθ]; constructor <;> nlinarith [pi_pos]

/-- The value of the sawtooth series on `(0, 1)`, by Abel's limit theorem, Mathlib
`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`, and continuity of `log` off the slit. -/
theorem saw_series_unit (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, sin (2 * π * i * y) / i) atTop
      (𝓝 (π * (1 / 2 - y))) := by
  obtain ⟨l, hl⟩ := saw_partial_converges y hy0 hy1
  have abel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  set e : ℂ := Complex.exp (((2 * π * y : ℝ) : ℂ) * Complex.I) with he
  have hslit : (1 - ((1 : ℝ) : ℂ) * e) ∈ Complex.slitPlane := by
    left
    rw [Complex.ofReal_one, one_mul, he, Complex.sub_re, Complex.one_re,
      Complex.exp_ofReal_mul_I_re]
    have : cos (2 * π * y) < 1 := by
      have h1 : cos (2 * π * y) ≠ 1 := by
        rw [Ne, Real.cos_eq_one_iff]
        rintro ⟨k, hk⟩
        have hk' : (k : ℝ) = y := by
          have := pi_pos
          field_simp at hk
          nlinarith
        have : (0 : ℝ) < k := by rw [hk']; exact hy0
        have : (k : ℝ) < 1 := by rw [hk']; exact hy1
        have h0 : (0 : ℤ) < k := by exact_mod_cast ‹(0 : ℝ) < k›
        have h1' : k < (1 : ℤ) := by exact_mod_cast ‹(k : ℝ) < 1›
        omega
      exact lt_of_le_of_ne (cos_le_one _) h1
    linarith
  have hca : ContinuousAt (fun r : ℝ => (-Complex.log (1 - (r : ℂ) * e)).im) 1 := by
    apply Complex.continuous_im.continuousAt.comp
    apply ContinuousAt.neg
    exact ContinuousAt.comp (g := Complex.log) (continuousAt_clog hslit) (by fun_prop)
  have hcont : Tendsto (fun r : ℝ => (-Complex.log (1 - (r : ℂ) * e)).im) (𝓝[<] 1)
      (𝓝 (π * (1 / 2 - y))) := by
    have := hca.tendsto
    simp only [Complex.ofReal_one, one_mul] at this
    rw [he, saw_log_value y hy0 hy1] at this
    exact this.mono_left nhdsWithin_le_nhds
  have heq : (fun r : ℝ => (-Complex.log (1 - (r : ℂ) * e)).im) =ᶠ[𝓝[<] 1]
      (fun r : ℝ => ∑' n : ℕ, sin (2 * π * n * y) / n * r ^ n) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact ((saw_power y r hr.1.le hr.2).tsum_eq).symm
  have hl' : l = π * (1 / 2 - y) := tendsto_nhds_unique abel (hcont.congr' heq)
  rw [hl'] at hl
  exact hl

/-- Reindexing `Icc 1 N` as `range N`. -/
theorem sum_Icc_eq_sum_range_succ (g : ℕ → ℝ) (N : ℕ) :
    ∑ h ∈ Finset.Icc 1 N, g h = ∑ i ∈ Finset.range N, g (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- PROVED: the sawtooth Fourier series, Pomerance 2011 section 4, as in Montgomery and Vaughan,
the expansion `psi x = - sum_{h >= 1} sin (2 pi h x)/(pi h)` of `psi x = fract x - 1/2`: at every
non integer `x` the partial sums converge to `1/2 - fract x`. -/
theorem sawtooth_series (x : ℝ) (hx : Int.fract x ≠ 0) :
    Tendsto (fun N : ℕ => ∑ h ∈ Finset.Icc 1 N, sin (2 * π * h * x) / (π * h)) atTop
      (𝓝 (1 / 2 - Int.fract x)) := by
  set y := Int.fract x with hy
  have hy0 : 0 < y := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
  have hy1 : y < 1 := Int.fract_lt_one x
  have hper : ∀ h : ℕ, sin (2 * π * h * x) = sin (2 * π * h * y) := by
    intro h
    have : 2 * π * h * x = 2 * π * h * y + ((h * ⌊x⌋ : ℤ) : ℝ) * (2 * π) := by
      rw [hy, Int.fract]; push_cast; ring
    rw [this, sin_add_int_mul_two_pi]
  have hT := ((saw_series_unit y hy0 hy1).comp (tendsto_add_atTop_nat 1)).const_mul (1 / π)
  rw [show 1 / π * (π * (1 / 2 - y)) = 1 / 2 - y by field_simp] at hT
  refine hT.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [sum_Icc_eq_sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, sin_zero, div_zero, add_zero]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hper]
  push_cast
  field_simp

/-- PROVED: the explicit tail of the sawtooth series,
`|psi x + F_H x| <= 1/(2 pi (H+1) ||x||)` for `x` not an integer, Pomerance 2011 section 4. -/
theorem sawtooth_tail (x : ℝ) (H : ℕ) (hH : 1 ≤ H) (hx : Int.fract x ≠ 0) :
    |Int.fract x - 1 / 2 + ∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * x) / (π * h)| ≤
      1 / (2 * π * ((H : ℝ) + 1) * min (Int.fract x) (1 - Int.fract x)) := by
  set G : ℕ → ℝ := fun N => ∑ h ∈ Finset.Icc 1 N, sin (2 * π * h * x) / (π * h) with hG
  have hmpos : 0 < min (Int.fract x) (1 - Int.fract x) := by
    have h0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
    exact lt_min h0 (by linarith [Int.fract_lt_one x])
  have hsin : 2 * min (Int.fract x) (1 - Int.fract x) ≤ |sin (π * x)| := jordan_fract x
  have hspos : 0 < |sin (π * x)| := by linarith
  have hT : Tendsto (fun N => G H - G N) atTop (𝓝 (G H - (1 / 2 - Int.fract x))) :=
    tendsto_const_nhds.sub (sawtooth_series x hx)
  have hbound : ∀ᶠ N in atTop, |G H - G N| ≤ 1 / π * (1 / (((H : ℝ) + 1) * |sin (π * x)|)) := by
    filter_upwards [eventually_gt_atTop H] with N hN
    have hsplit : Finset.Icc 1 N = Finset.Icc 1 H ∪ Finset.Icc (H + 1) N := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 H) (Finset.Icc (H + 1) N) := by
      rw [Finset.disjoint_left]; intro r h1 h2
      simp only [Finset.mem_Icc] at h1 h2; omega
    have hGN : G N = G H + 1 / π * ∑ h ∈ Finset.Icc (H + 1) N, sin (2 * π * h * x) / h := by
      simp only [hG]
      rw [hsplit, Finset.sum_union hdisj, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      field_simp
    rw [hGN, show G H - (G H + 1 / π * ∑ h ∈ Finset.Icc (H + 1) N, sin (2 * π * h * x) / h) =
      -(1 / π * ∑ h ∈ Finset.Icc (H + 1) N, sin (2 * π * h * x) / h) by ring, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
    exact mul_le_mul_of_nonneg_left (sin_abel_tail x hx H N hN) (by positivity)
  have hlim : |G H - (1 / 2 - Int.fract x)| ≤
      1 / π * (1 / (((H : ℝ) + 1) * |sin (π * x)|)) :=
    le_of_tendsto (hT.abs) hbound
  have heq : Int.fract x - 1 / 2 + G H = G H - (1 / 2 - Int.fract x) := by ring
  simp only [hG] at heq hlim
  rw [heq]
  refine hlim.trans ?_
  have hH1 : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 2 * π * ((H : ℝ) + 1) * min (Int.fract x) (1 - Int.fract x) ≤
      π * (((H : ℝ) + 1) * |sin (π * x)|) := by
    have := mul_le_mul_of_nonneg_left hsin (by positivity : (0 : ℝ) ≤ π * ((H : ℝ) + 1))
    nlinarith
  linarith

/-- Sums over `0 <= a < q` are sums over `ZMod q`. -/
theorem sum_range_eq_sum_zmod {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ a ∈ Finset.range q, f (a : ZMod q) = ∑ x : ZMod q, f x := by
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod q)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a _; rfl

/-- The twisted Gauss sum of a primitive character, Pomerance 2011 section 4:
`sum_a chi a e(k a / q) = conj chi (k) tau(chi)`, from Mathlib's
`gaussSum_mulShift_of_isPrimitive`. -/
theorem gauss_twist {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (k : ℤ) :
    ∑ a ∈ Finset.range q, χ (a : ZMod q) * Complex.exp (2 * π * Complex.I * ((k * a : ℤ) : ℂ) / q) =
      χ⁻¹ (k : ZMod q) * gaussSum χ ZMod.stdAddChar := by
  rw [← gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ]
  have : ∀ a : ℕ, Complex.exp (2 * π * Complex.I * ((k * a : ℤ) : ℂ) / q) =
      (ZMod.stdAddChar.mulShift (k : ZMod q)) (a : ZMod q) := by
    intro a
    rw [AddChar.mulShift_apply, show (k : ZMod q) * (a : ZMod q) = (((k * a : ℤ)) : ZMod q) by
      push_cast; ring, ZMod.stdAddChar_coe]
  simp_rw [this]
  rw [sum_range_eq_sum_zmod (fun x => χ x * (ZMod.stdAddChar.mulShift (k : ZMod q)) x)]
  rfl

/-- An odd character has `chi (-1) = -1`. -/
theorem odd_neg_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h_odd : χ (-1) ≠ 1) :
    χ (-1) = -1 := by
  have h2 : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by ring_nf; rw [sq, h2]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) h_odd
  · exact eq_neg_of_add_eq_zero_left h


/-- Hence `chi^{-1} (-1) = -1`. -/
theorem inv_neg_one_odd {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h_odd : χ (-1) ≠ 1) :
    χ⁻¹ (-1) = -1 := by
  rw [MulChar.inv_apply_eq_inv', odd_neg_one χ h_odd]
  norm_num

/-- The sine twist, Pomerance 2011 section 4: for odd primitive `chi`,
`sum_a chi a sin (2 pi h (c - a)/q) = i conj chi (h) tau(chi) cos (2 pi h c / q)`. -/
theorem sin_twist {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (h_odd : χ (-1) ≠ 1) (c : ℤ) (h : ℕ) :
    ∑ a ∈ Finset.range q, χ (a : ZMod q) * ((sin (2 * π * h * (((c : ℝ) - a) / q)) : ℝ) : ℂ) =
      Complex.I * χ⁻¹ (h : ZMod q) * gaussSum χ ZMod.stdAddChar *
        ((cos (2 * π * h * c / q) : ℝ) : ℂ) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  set φ : ℝ := 2 * π * h * c / q with hφ
  have hterm : ∀ a : ℕ, ((sin (2 * π * h * (((c : ℝ) - a) / q)) : ℝ) : ℂ) =
      Complex.I / 2 * (Complex.exp (-(φ : ℂ) * Complex.I) *
          Complex.exp (2 * π * Complex.I * (((h : ℤ) * a : ℤ) : ℂ) / q) -
        Complex.exp ((φ : ℂ) * Complex.I) *
          Complex.exp (2 * π * Complex.I * (((-(h : ℤ)) * a : ℤ) : ℂ) / q)) := by
    intro a
    rw [Complex.ofReal_sin, Complex.sin, ← Complex.exp_add, ← Complex.exp_add]
    have e1 : -(((2 * π * h * (((c : ℝ) - a) / q)) : ℝ) : ℂ) * Complex.I =
        -(φ : ℂ) * Complex.I + 2 * π * Complex.I * (((h : ℤ) * a : ℤ) : ℂ) / q := by
      rw [hφ]; push_cast; field_simp; ring
    have e2 : (((2 * π * h * (((c : ℝ) - a) / q)) : ℝ) : ℂ) * Complex.I =
        (φ : ℂ) * Complex.I + 2 * π * Complex.I * (((-(h : ℤ)) * a : ℤ) : ℂ) / q := by
      rw [hφ]; push_cast; field_simp; ring
    rw [e1, e2]; ring
  simp_rw [hterm]
  have hsplit : ∑ a ∈ Finset.range q, χ (a : ZMod q) *
      (Complex.I / 2 * (Complex.exp (-(φ : ℂ) * Complex.I) *
          Complex.exp (2 * π * Complex.I * (((h : ℤ) * a : ℤ) : ℂ) / q) -
        Complex.exp ((φ : ℂ) * Complex.I) *
          Complex.exp (2 * π * Complex.I * (((-(h : ℤ)) * a : ℤ) : ℂ) / q))) =
      Complex.I / 2 * (Complex.exp (-(φ : ℂ) * Complex.I) *
          ∑ a ∈ Finset.range q, χ (a : ZMod q) *
            Complex.exp (2 * π * Complex.I * (((h : ℤ) * a : ℤ) : ℂ) / q) -
        Complex.exp ((φ : ℂ) * Complex.I) *
          ∑ a ∈ Finset.range q, χ (a : ZMod q) *
            Complex.exp (2 * π * Complex.I * (((-(h : ℤ)) * a : ℤ) : ℂ) / q)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hsplit, gauss_twist χ hχ, gauss_twist χ hχ]
  have hneg : χ⁻¹ (((-(h : ℤ)) : ℤ) : ZMod q) = -χ⁻¹ (h : ZMod q) := by
    rw [show (((-(h : ℤ)) : ℤ) : ZMod q) = (-1) * (h : ZMod q) by push_cast; ring, map_mul,
      inv_neg_one_odd χ h_odd]
    ring
  rw [hneg, show (((h : ℤ)) : ZMod q) = (h : ZMod q) by push_cast; rfl, Complex.ofReal_cos,
    Complex.cos]
  ring

/-- The main term of Pomerance 2011 section 4, PROVED: the truncated series summed against
`chi` is `tau(chi)/(pi i) sum_h conj chi(h) (1 - cos (2 pi h n/q))/h` up to sign, of norm at most
`sqrt q / pi` times the cosine sum, since `|tau(chi)| = sqrt q`, Riesel and Vaughan file
`GaussImprim`, and `|chi h| <= 1`. -/
theorem main_term_gauss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (_hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (H : ℕ) (_hH : 1 ≤ H) (n : ℕ) :
    ‖∑ a ∈ Finset.range q, χ (a : ZMod q) *
        (((∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * (((n : ℝ) - a) / q)) / (π * h)) -
          (∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * ((-(a : ℝ)) / q)) / (π * h)) : ℝ) : ℂ)‖ ≤
      sqrt (q : ℝ) / π * ∑ h ∈ Finset.Icc 1 H, (1 - cos (2 * π * h * n / q)) / (h : ℝ) := by
  set τ : ℂ := gaussSum χ ZMod.stdAddChar with hτ
  have hτn : ‖τ‖ = sqrt (q : ℝ) := by
    rw [← LeanLab.RieselVaughan1983.GaussImprim.norm_sq_gaussSum_of_isPrimitive hχ,
      Real.sqrt_sq (norm_nonneg _)]
  have h0 : ∀ a : ℕ, (-(a : ℝ)) / q = (((0 : ℤ) : ℝ) - a) / q := fun a => by simp
  have hn : ∀ a : ℕ, ((n : ℝ) - a) / q = (((n : ℤ) : ℝ) - a) / q := fun a => by simp
  simp only [h0, hn]
  have heq : ∑ a ∈ Finset.range q, χ (a : ZMod q) *
        (((∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * ((((n : ℤ) : ℝ) - a) / q)) / (π * h)) -
          (∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * ((((0 : ℤ) : ℝ) - a) / q)) / (π * h)) : ℝ)
            : ℂ) =
      ∑ h ∈ Finset.Icc 1 H, (((1 / (π * h)) : ℝ) : ℂ) *
        (Complex.I * χ⁻¹ (h : ZMod q) * τ *
          (((cos (2 * π * h * ((n : ℤ) : ℝ) / q)) : ℝ) : ℂ) -
         Complex.I * χ⁻¹ (h : ZMod q) * τ *
          (((cos (2 * π * h * ((0 : ℤ) : ℝ) / q)) : ℝ) : ℂ)) := by
    have hper : ∀ a ∈ Finset.range q, χ (a : ZMod q) *
        (((∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * ((((n : ℤ) : ℝ) - a) / q)) / (π * h)) -
          (∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * ((((0 : ℤ) : ℝ) - a) / q)) / (π * h)) : ℝ)
            : ℂ) =
        ∑ h ∈ Finset.Icc 1 H, (((1 / (π * h)) : ℝ) : ℂ) *
          (χ (a : ZMod q) * ((sin (2 * π * h * ((((n : ℤ) : ℝ) - a) / q)) : ℝ) : ℂ) -
            χ (a : ZMod q) * ((sin (2 * π * h * ((((0 : ℤ) : ℝ) - a) / q)) : ℝ) : ℂ)) := by
      intro a _
      rw [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_sum, ← Finset.sum_sub_distrib,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_one]
      ring
    rw [Finset.sum_congr rfl hper, Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, sin_twist χ hχ h_odd n h,
      sin_twist χ hχ h_odd 0 h]
  rw [heq]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun h hh => ?_
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
  have hhpos : (0 : ℝ) < h := by linarith
  have hχh : ‖χ⁻¹ (h : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have hc : (0 : ℝ) ≤ 1 - cos (2 * π * h * n / q) := by linarith [cos_le_one (2 * π * h * n / q)]
  rw [show Complex.I * χ⁻¹ (h : ZMod q) * τ * (((cos (2 * π * h * ((n : ℤ) : ℝ) / q)) : ℝ) : ℂ) -
      Complex.I * χ⁻¹ (h : ZMod q) * τ * (((cos (2 * π * h * ((0 : ℤ) : ℝ) / q)) : ℝ) : ℂ) =
      -(Complex.I * χ⁻¹ (h : ZMod q) * τ * (((1 - cos (2 * π * h * n / q)) : ℝ) : ℂ)) by
    push_cast; simp; ring]
  rw [norm_mul, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, hτn,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (π * h))]
  have hs : 0 ≤ sqrt (q : ℝ) := Real.sqrt_nonneg _
  calc 1 / (π * h) * (1 * ‖χ⁻¹ (h : ZMod q)‖ * sqrt q * (1 - cos (2 * π * h * n / q)))
      ≤ 1 / (π * h) * (1 * 1 * sqrt q * (1 - cos (2 * π * h * n / q))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hc
        apply mul_le_mul_of_nonneg_right _ hs
        linarith
    _ = sqrt q / π * ((1 - cos (2 * π * h * n / q)) / h) := by
        field_simp

/-- One step of the sawtooth: `fract (t/q) - fract ((t+1)/q)` is `1 - 1/q` when `q | t + 1`
and `-1/q` otherwise. -/
theorem fract_step (t : ℤ) (q : ℕ) (hq : 2 ≤ q) :
    Int.fract ((t : ℝ) / q) - Int.fract (((t + 1 : ℤ) : ℝ) / q) =
      (if (q : ℤ) ∣ (t + 1) then (1 : ℝ) else 0) - 1 / q := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [Int.fract_div_intCast_eq_div_intCast_mod, Int.fract_div_intCast_eq_div_intCast_mod]
  have hr0 := Int.emod_nonneg t hqz.ne'
  have hrlt := Int.emod_lt_of_pos t hqz
  have h1 : (1 : ℤ) % q = 1 := Int.emod_eq_of_lt (by norm_num) (by omega)
  have hadd : (t + 1) % q = (t % q + 1) % q := by rw [Int.add_emod, h1]
  by_cases h : t % q + 1 = q
  · have h0 : (t + 1) % q = 0 := by rw [hadd, h, Int.emod_self]
    have hd : (q : ℤ) ∣ t + 1 := Int.dvd_of_emod_eq_zero h0
    simp only [hd, ↓reduceIte]
    rw [h0]
    have : ((t % q : ℤ) : ℝ) = q - 1 := by
      have : t % q = q - 1 := by omega
      rw [this]; push_cast; ring
    rw [this]; field_simp; push_cast; ring
  · have hlt : t % q + 1 < q := by omega
    have h0 : (t + 1) % q = t % q + 1 := by rw [hadd, Int.emod_eq_of_lt (by omega) hlt]
    have hd : ¬ (q : ℤ) ∣ t + 1 := by
      intro hd
      have := Int.emod_eq_zero_of_dvd hd
      omega
    simp only [hd, ↓reduceIte]
    rw [h0]
    push_cast
    field_simp
    ring

/-- A nontrivial character sums to zero over a period; odd characters are nontrivial. -/
theorem sum_chi_range_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h_odd : χ (-1) ≠ 1) : ∑ a ∈ Finset.range q, χ (a : ZMod q) = 0 := by
  rw [sum_range_eq_sum_zmod (fun x => χ x)]
  apply MulChar.sum_eq_zero_of_ne_one
  intro h1
  apply h_odd
  rw [h1]
  exact MulChar.one_apply (isUnit_one.neg)

/-- Picking out the residue `n + 1` from the period. -/
theorem sum_chi_indicator {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ∑ a ∈ Finset.range q, χ (a : ZMod q) *
      (if (q : ℤ) ∣ ((n : ℤ) - a + 1) then (1 : ℂ) else 0) = χ ((n + 1 : ℕ) : ZMod q) := by
  have hiff : ∀ a : ℕ, ((q : ℤ) ∣ ((n : ℤ) - a + 1)) ↔ ((a : ZMod q) = ((n + 1 : ℕ) : ZMod q)) := by
    intro a
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  simp_rw [hiff]
  rw [sum_range_eq_sum_zmod (fun x => χ x * if x = ((n + 1 : ℕ) : ZMod q) then (1 : ℂ) else 0)]
  simp

/-- The counting identity by induction on `n`. -/
theorem count_sawtooth_core {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) =
      ∑ a ∈ Finset.range q, χ (a : ZMod q) *
        ((Int.fract ((-(a : ℝ)) / q) - Int.fract (((n : ℝ) - a) / q) : ℝ) : ℂ) := by
  have hq2 : 2 ≤ q := by have := NeZero.ne q; omega
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hstep : ∀ a ∈ Finset.range q, χ (a : ZMod q) *
        ((Int.fract ((-(a : ℝ)) / q) - Int.fract ((((n + 1 : ℕ) : ℝ) - a) / q) : ℝ) : ℂ) =
        χ (a : ZMod q) * ((Int.fract ((-(a : ℝ)) / q) - Int.fract (((n : ℝ) - a) / q) : ℝ) : ℂ) +
          (χ (a : ZMod q) * (if (q : ℤ) ∣ ((n : ℤ) - a + 1) then (1 : ℂ) else 0) -
            (1 / q : ℂ) * χ (a : ZMod q)) := by
      intro a _
      have hfs := fract_step ((n : ℤ) - a) q hq2
      have e1 : (((n : ℤ) - a : ℤ) : ℝ) = (n : ℝ) - a := by push_cast; ring
      have e2 : ((((n : ℤ) - a + 1 : ℤ)) : ℝ) = (((n + 1 : ℕ) : ℝ)) - a := by push_cast; ring
      rw [e1, e2] at hfs
      have : Int.fract ((((n + 1 : ℕ) : ℝ) - a) / q) = Int.fract (((n : ℝ) - a) / q) -
          ((if (q : ℤ) ∣ ((n : ℤ) - a + 1) then (1 : ℝ) else 0) - 1 / q) := by linarith
      rw [this]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      sum_chi_indicator, ← Finset.mul_sum, sum_chi_range_zero χ h_odd]
    simp

/-- PROVED, Pomerance 2011 section 4, the first line of Landau's argument: for `0 <= a < q` the
number of `m` in `[1, n]` with `m = a mod q` is `n/q + psi (-a/q) - psi ((n-a)/q)` with
`psi x = fract x - 1/2`; summing against a nontrivial `chi` the mean `n/q` drops out. -/
theorem count_sawtooth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) =
      ∑ a ∈ Finset.range q, χ (a : ZMod q) *
        (((Int.fract ((-(a : ℝ)) / q) - 1 / 2) - (Int.fract (((n : ℝ) - a) / q) - 1 / 2) : ℝ)
          : ℂ) := by
  rw [count_sawtooth_core χ hq h_odd n]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  ring

/-- The harmonic estimate `sum_{r < q} 1/min (r, q - r) <= 2 H_{q/2} <= 2 (log q + 1 - log 2)`,
from Mathlib's `harmonic_le_one_add_log`. -/
theorem harm_half_bound {q : ℕ} (hq : 2 ≤ q) :
    ∑ r ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (min (r : ℝ) ((q : ℝ) - r)) ≤
      2 * (log q + 1 - log 2) := by
  set m := q / 2 with hm
  have hm1 : 1 ≤ m := by omega
  have hmq : (m : ℝ) ≤ (q : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    exact_mod_cast (by omega : m * 2 ≤ q)
  have hH : (∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s) ≤ log q + 1 - log 2 := by
    have h := harmonic_le_one_add_log m
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    have hlog : log (m : ℝ) ≤ log q - log 2 := by
      rw [← log_div (by positivity) (by norm_num)]
      exact log_le_log (by exact_mod_cast hm1) hmq
    simp_rw [one_div]
    linarith
  have hsplit : Finset.Icc 1 (q - 1) = Finset.Icc 1 m ∪ Finset.Icc (m + 1) (q - 1) := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) (q - 1)) := by
    rw [Finset.disjoint_left]; intro r h1 h2
    simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hA : ∑ r ∈ Finset.Icc 1 m, (1 : ℝ) / (min (r : ℝ) ((q : ℝ) - r)) ≤
      ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s := by
    refine Finset.sum_le_sum fun r hr => le_of_eq ?_
    have hr' := Finset.mem_Icc.mp hr
    have : (r : ℝ) ≤ (q : ℝ) - r := by
      have : r + r ≤ q := by omega
      have : ((r + r : ℕ) : ℝ) ≤ q := by exact_mod_cast this
      push_cast at this; linarith
    rw [min_eq_left this]
  have hB : ∑ r ∈ Finset.Icc (m + 1) (q - 1), (1 : ℝ) / (min (r : ℝ) ((q : ℝ) - r)) ≤
      ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / s := by
    calc _ = ∑ r ∈ Finset.Icc (m + 1) (q - 1), (1 : ℝ) / ((q - r : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hr' := Finset.mem_Icc.mp hr
          have hcast : ((q - r : ℕ) : ℝ) = (q : ℝ) - r := by
            rw [Nat.cast_sub (by omega)]
          have : (q : ℝ) - r ≤ (r : ℝ) := by
            have : q ≤ r + r := by omega
            have : (q : ℝ) ≤ ((r + r : ℕ) : ℝ) := by exact_mod_cast this
            push_cast at this; linarith
          rw [min_eq_right this, hcast]
      _ = ∑ s ∈ (Finset.Icc (m + 1) (q - 1)).image (fun r => q - r), (1 : ℝ) / s := by
          rw [Finset.sum_image]
          intro x hx y hy hxy
          simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
          simp only at hxy
          omega
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro s hs
            simp only [Finset.mem_image, Finset.mem_Icc] at hs ⊢
            obtain ⟨r, ⟨h1, h2⟩, rfl⟩ := hs
            omega
          · intro s _ _; positivity
  linarith

/-- Residue bookkeeping: `(c - ((c - t) mod q)) mod q = t` for `0 <= t < q`. -/
theorem emod_back {q : ℕ} (_hq : 2 ≤ q) (c t : ℤ) (ht0 : 0 ≤ t) (htq : t < q) :
    (c - (c - t) % q) % q = t := by
  have hd := Int.emod_def (c - t) q
  rw [hd, show c - (c - t - (q : ℤ) * ((c - t) / q)) = t + (q : ℤ) * ((c - t) / q) by ring,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt ht0 htq]

/-- PROVED, Pomerance 2011 section 4, the sum over residues of the inverse distance to the
nearest integer: for every integer shift `c`, the points `(c - a)/q`, `0 <= a < q`, not
integers have `sum 1/||(c - a)/q|| <= 2 q (log q + 1 - log 2)`, after the permutation
`a -> (c - a) mod q` of residues. -/
theorem dist_harmonic_sum {q : ℕ} (hq : 2 ≤ q) (c : ℤ) :
    ∑ a ∈ (Finset.range q).filter (fun a : ℕ => Int.fract (((c : ℝ) - a) / q) ≠ 0),
      1 / min (Int.fract (((c : ℝ) - a) / q)) (1 - Int.fract (((c : ℝ) - a) / q)) ≤
      2 * (q : ℝ) * (log q + 1 - log 2) := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hfr : ∀ a : ℕ, Int.fract (((c : ℝ) - a) / q) = ((((c - a) % q : ℤ)) : ℝ) / q := by
    intro a
    have := Int.fract_div_intCast_eq_div_intCast_mod (k := ℝ) (m := c - a) (n := q)
    push_cast at this
    exact this
  have hnn : ∀ a : ℕ, 0 ≤ (c - a) % q := fun a => Int.emod_nonneg _ hqz.ne'
  have hlt : ∀ a : ℕ, (c - a) % q < q := fun a => Int.emod_lt_of_pos _ hqz
  have hterm : ∀ a ∈ (Finset.range q).filter (fun a : ℕ => Int.fract (((c : ℝ) - a) / q) ≠ 0),
      1 / min (Int.fract (((c : ℝ) - a) / q)) (1 - Int.fract (((c : ℝ) - a) / q)) =
      (q : ℝ) * ((1 : ℝ) / min ((((c - a) % q).toNat : ℕ) : ℝ)
        ((q : ℝ) - (((c - a) % q).toNat : ℕ))) := by
    intro a _
    rw [hfr a]
    have hcast : ((((c - a) % q).toNat : ℕ) : ℝ) = ((((c - a) % q : ℤ)) : ℝ) := by
      have : ((((c - a) % q).toNat : ℕ) : ℤ) = (c - a) % q := Int.toNat_of_nonneg (hnn a)
      exact_mod_cast this
    rw [hcast]
    set r : ℝ := ((((c - a) % q : ℤ)) : ℝ)
    rw [show (1 : ℝ) - r / q = ((q : ℝ) - r) / q by field_simp, min_div_div_right hqR.le,
      one_div_div]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbij : ∑ a ∈ (Finset.range q).filter (fun a : ℕ => Int.fract (((c : ℝ) - a) / q) ≠ 0),
      (1 : ℝ) / min ((((c - a) % q).toNat : ℕ) : ℝ) ((q : ℝ) - (((c - a) % q).toNat : ℕ)) =
      ∑ r ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (min (r : ℝ) ((q : ℝ) - r)) := by
    refine Finset.sum_nbij' (fun a : ℕ => ((c - a) % q).toNat)
      (fun r : ℕ => ((c - r) % q).toNat) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      have hne : (c - a) % q ≠ 0 := by
        intro h0; apply ha'.2; rw [hfr a, h0]; simp
      have := hnn a; have := hlt a
      simp only [Finset.mem_Icc]
      omega
    · intro r hr
      have hr' : 1 ≤ r ∧ r ≤ q - 1 := by simpa using hr
      have hb := emod_back hq c r (by positivity) (by omega)
      have := hnn r; have := hlt r
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have hcast : (((((c - r) % q).toNat : ℕ)) : ℤ) = (c - r) % q := Int.toNat_of_nonneg (hnn r)
      rw [hfr, hcast, hb]
      have : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
      push_cast
      exact div_ne_zero (ne_of_gt this) hqR.ne'
    · intro a ha
      have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      have haq := Finset.mem_range.mp ha'.1
      have hcast : (((((c - a) % q).toNat : ℕ)) : ℤ) = (c - a) % q := Int.toNat_of_nonneg (hnn a)
      rw [hcast, emod_back hq c a (by positivity) (by omega)]
      simp
    · intro r hr
      have hr' : 1 ≤ r ∧ r ≤ q - 1 := by simpa using hr
      have hcast : (((((c - r) % q).toNat : ℕ)) : ℤ) = (c - r) % q := Int.toNat_of_nonneg (hnn r)
      rw [hcast, emod_back hq c r (by positivity) (by omega)]
      simp
    · intro a _; rfl
  rw [hbij]
  have := harm_half_bound hq
  nlinarith

/-- At an integer point the truncated sawtooth series vanishes, so its error is `psi = -1/2`. -/
theorem sawtooth_error_at_integer (x : ℝ) (H : ℕ) (hx : Int.fract x = 0) :
    |Int.fract x - 1 / 2 + ∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * x) / (π * h)| = 1 / 2 := by
  have hxk : x = (⌊x⌋ : ℝ) := by
    have := Int.floor_add_fract x
    rw [hx, add_zero] at this
    exact this.symm
  have hs : ∀ h ∈ Finset.Icc 1 H, sin (2 * π * h * x) / (π * h) = 0 := by
    intro h _
    rw [hxk, show 2 * π * (h : ℝ) * (⌊x⌋ : ℝ) = ((2 * h * ⌊x⌋ : ℤ) : ℝ) * π by push_cast; ring,
      sin_int_mul_pi, zero_div]
  rw [Finset.sum_eq_zero hs, hx]
  norm_num

/-- The tail error at every point, the integer case costing `1/2`, summed with weights
`‖chi a‖ <= 1` over the residues: Pomerance 2011 section 4. -/
theorem tail_sum_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq2 : 2 ≤ q)
    (H : ℕ) (hH : 1 ≤ H) (c : ℤ) :
    ∑ a ∈ Finset.range q, ‖χ (a : ZMod q)‖ *
        |Int.fract (((c : ℝ) - a) / q) - 1 / 2 +
          ∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * (((c : ℝ) - a) / q)) / (π * h)| ≤
      (q : ℝ) * (log q + 1 - log 2) / (π * ((H : ℝ) + 1)) +
        1 / 2 * ∑ a ∈ (Finset.range q).filter (fun a : ℕ => Int.fract (((c : ℝ) - a) / q) = 0),
          ‖χ (a : ZMod q)‖ := by
  set x : ℕ → ℝ := fun a => ((c : ℝ) - a) / q with hxdef
  have hHpos : (0 : ℝ) < 2 * π * ((H : ℝ) + 1) := by positivity
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range q) (fun a : ℕ => Int.fract (x a) = 0)]
  rw [add_comm]
  apply add_le_add
  · -- the non integer points
    calc _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => ¬ Int.fract (x a) = 0),
          1 / (2 * π * ((H : ℝ) + 1)) *
            (1 / min (Int.fract (x a)) (1 - Int.fract (x a))) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have hfa : Int.fract (x a) ≠ 0 := (Finset.mem_filter.mp ha).2
          have hT := sawtooth_tail (x a) H hH hfa
          have hχ1 : ‖χ (a : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
          have hn0 : 0 ≤ |Int.fract (x a) - 1 / 2 +
              ∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * x a) / (π * h)| := abs_nonneg _
          calc ‖χ (a : ZMod q)‖ * |Int.fract (x a) - 1 / 2 +
                ∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * x a) / (π * h)|
              ≤ 1 * |Int.fract (x a) - 1 / 2 +
                ∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * x a) / (π * h)| :=
                mul_le_mul_of_nonneg_right hχ1 hn0
            _ ≤ _ := by
                rw [one_mul]
                refine hT.trans (le_of_eq ?_)
                rw [one_div_mul_one_div]
      _ = 1 / (2 * π * ((H : ℝ) + 1)) *
            ∑ a ∈ (Finset.range q).filter (fun a : ℕ => Int.fract (x a) ≠ 0),
              1 / min (Int.fract (x a)) (1 - Int.fract (x a)) := by
          rw [Finset.mul_sum]
      _ ≤ 1 / (2 * π * ((H : ℝ) + 1)) * (2 * (q : ℝ) * (log q + 1 - log 2)) := by
          apply mul_le_mul_of_nonneg_left (dist_harmonic_sum hq2 c)
          positivity
      _ = _ := by field_simp
  · -- the integer points, error exactly `1/2`
    rw [Finset.mul_sum]
    refine le_of_eq (Finset.sum_congr rfl fun a ha => ?_)
    have hfa : Int.fract (x a) = 0 := (Finset.mem_filter.mp ha).2
    rw [sawtooth_error_at_integer (x a) H hfa, mul_comm]

/-- Only `a = 0` among `0 <= a < q` has `-a/q` an integer, and `chi 0 = 0`. -/
theorem endpoint_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q ≠ 1) :
    ∑ a ∈ (Finset.range q).filter (fun a : ℕ => Int.fract ((((0 : ℤ) : ℝ) - a) / q) = 0),
      ‖χ (a : ZMod q)‖ = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨har, hfa⟩
  have hqpos : (0 : ℝ) < q := by
    have := NeZero.ne q
    exact_mod_cast Nat.pos_of_ne_zero this
  have halt : (a : ℝ) < q := by exact_mod_cast Finset.mem_range.mp har
  have hk := Int.floor_add_fract ((((0 : ℤ) : ℝ) - a) / q)
  rw [hfa, add_zero] at hk
  set k : ℤ := ⌊(((0 : ℤ) : ℝ) - a) / q⌋ with hkdef
  have hkq : (k : ℝ) * q = -(a : ℝ) := by
    rw [hk]; field_simp; push_cast; ring
  have ha00 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hk1 : (-1 : ℝ) < k := by
    by_contra hc
    push Not at hc
    nlinarith
  have hk2 : (k : ℝ) < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hk0 : k = 0 := by
    have h1 : k < 1 := by exact_mod_cast hk2
    have h2 : -1 < k := by exact_mod_cast hk1
    omega
  have ha0 : (a : ℝ) = 0 := by
    rw [hk0] at hkq
    simp at hkq
    exact_mod_cast hkq
  have : a = 0 := by exact_mod_cast ha0
  subst this
  have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq
  simp only [Nat.cast_zero, norm_eq_zero]
  exact MulChar.map_zero χ

/-- At most one `a` with `0 <= a < q` has `(n - a)/q` an integer, so this endpoint costs `1/2`. -/
theorem endpoint_n {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ∑ a ∈ (Finset.range q).filter (fun a : ℕ => Int.fract ((((n : ℤ) : ℝ) - a) / q) = 0),
      ‖χ (a : ZMod q)‖ ≤ 1 := by
  have hqpos : (0 : ℝ) < q := by
    have := NeZero.ne q
    exact_mod_cast Nat.pos_of_ne_zero this
  have hcard : ((Finset.range q).filter
      (fun a : ℕ => Int.fract ((((n : ℤ) : ℝ) - a) / q) = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rcases Finset.mem_filter.mp ha with ⟨har, hfa⟩
    rcases Finset.mem_filter.mp hb with ⟨hbr, hfb⟩
    have hab := (Int.fract_eq_fract).mp (hfa.trans hfb.symm)
    rcases hab with ⟨z, hz⟩
    have halt : (a : ℝ) < q := by exact_mod_cast Finset.mem_range.mp har
    have hblt : (b : ℝ) < q := by exact_mod_cast Finset.mem_range.mp hbr
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hz' : ((b : ℝ) - a) = z * q := by
      have := hz
      field_simp at this
      linarith
    have hz1 : (z : ℝ) < 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    have hz2 : (-1 : ℝ) < z := by
      by_contra hc
      push Not at hc
      nlinarith
    have hz0 : z = 0 := by
      have h1 : z < 1 := by exact_mod_cast hz1
      have h2 : -1 < z := by exact_mod_cast hz2
      omega
    rw [hz0] at hz'
    simp at hz'
    exact_mod_cast (sub_eq_zero.mp hz').symm
  calc _ ≤ ∑ a ∈ (Finset.range q).filter
        (fun a : ℕ => Int.fract ((((n : ℤ) : ℝ) - a) / q) = 0), (1 : ℝ) :=
        Finset.sum_le_sum fun a _ => DirichletCharacter.norm_le_one χ _
    _ = ((((Finset.range q).filter
        (fun a : ℕ => Int.fract ((((n : ℤ) : ℝ) - a) / q) = 0)).card : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 1 := Nat.cast_le_one.mpr hcard

/-- `leaf_odd_polya_expansion` PROVED, with exactly its statement, from the lemmas above
above: Pomerance 2011 section 4. -/
theorem leaf_odd_polya_expansion_proved {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (H : ℕ) (hH : 1 ≤ H) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * ∑ h ∈ Finset.Icc 1 H, (1 - cos (2 * π * h * n / q)) / (h : ℝ) +
        2 * (q : ℝ) * (log q + 1 - log 2) / (π * ((H : ℝ) + 1)) + 1 / 2 := by
  have hq2 : 2 ≤ q := by
    have := NeZero.ne q
    omega
  set F : ℝ → ℝ := fun x => ∑ h ∈ Finset.Icc 1 H, sin (2 * π * h * x) / (π * h) with hFdef
  set R : ℝ → ℝ := fun x => Int.fract x - 1 / 2 + F x with hRdef
  set x0 : ℕ → ℝ := fun a => (((0 : ℤ) : ℝ) - a) / q with hx0
  set xn : ℕ → ℝ := fun a => (((n : ℤ) : ℝ) - a) / q with hxn
  have hx0' : ∀ a : ℕ, (-(a : ℝ)) / q = x0 a := fun a => by simp [hx0]
  have hxn' : ∀ a : ℕ, ((n : ℝ) - a) / q = xn a := fun a => by simp [hxn]
  rw [count_sawtooth χ hq h_odd n]
  simp only [hx0', hxn']
  have hsplit : ∀ a ∈ Finset.range q, χ (a : ZMod q) *
      (((Int.fract (x0 a) - 1 / 2) - (Int.fract (xn a) - 1 / 2) : ℝ) : ℂ) =
      χ (a : ZMod q) * ((F (xn a) - F (x0 a) : ℝ) : ℂ) +
        χ (a : ZMod q) * ((R (x0 a) - R (xn a) : ℝ) : ℂ) := by
    intro a _
    rw [← mul_add, ← Complex.ofReal_add]
    congr 2
    simp only [hRdef]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hmain := main_term_gauss χ hχ hq h_odd H hH n
  simp only [hx0', hxn'] at hmain
  have herr : ‖∑ a ∈ Finset.range q, χ (a : ZMod q) * ((R (x0 a) - R (xn a) : ℝ) : ℂ)‖ ≤
      ∑ a ∈ Finset.range q, ‖χ (a : ZMod q)‖ * |R (x0 a)| +
        ∑ a ∈ Finset.range q, ‖χ (a : ZMod q)‖ * |R (xn a)| := by
    rw [← Finset.sum_add_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact abs_sub _ _
  have h0 := tail_sum_bound χ hq2 H hH 0
  have hn := tail_sum_bound χ hq2 H hH n
  rw [endpoint_zero χ hq] at h0
  have hen := endpoint_n χ n
  have hR0 : ∑ a ∈ Finset.range q, ‖χ (a : ZMod q)‖ * |R (x0 a)| ≤
      (q : ℝ) * (log q + 1 - log 2) / (π * ((H : ℝ) + 1)) := by
    have := h0
    simp only [mul_zero, add_zero] at this
    exact this
  have hRn : ∑ a ∈ Finset.range q, ‖χ (a : ZMod q)‖ * |R (xn a)| ≤
      (q : ℝ) * (log q + 1 - log 2) / (π * ((H : ℝ) + 1)) + 1 / 2 := by
    refine hn.trans ?_
    linarith
  calc _ ≤ ‖∑ a ∈ Finset.range q, χ (a : ZMod q) * ((F (xn a) - F (x0 a) : ℝ) : ℂ)‖ +
        ‖∑ a ∈ Finset.range q, χ (a : ZMod q) * ((R (x0 a) - R (xn a) : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ _ := by
        have hm : ‖∑ a ∈ Finset.range q, χ (a : ZMod q) * ((F (xn a) - F (x0 a) : ℝ) : ℂ)‖ ≤
            sqrt (q : ℝ) / π * ∑ h ∈ Finset.Icc 1 H, (1 - cos (2 * π * h * n / q)) / (h : ℝ) :=
          hmain
        have : 2 * (q : ℝ) * (log q + 1 - log 2) / (π * ((H : ℝ) + 1)) =
            (q : ℝ) * (log q + 1 - log 2) / (π * ((H : ℝ) + 1)) +
              (q : ℝ) * (log q + 1 - log 2) / (π * ((H : ℝ) + 1)) := by ring
        linarith

/-- The same statement under the split name, for wiring. -/
theorem leaf_odd_polya_expansion_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (H : ℕ) (hH : 1 ≤ H) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * ∑ h ∈ Finset.Icc 1 H, (1 - cos (2 * π * h * n / q)) / (h : ℝ) +
        2 * (q : ℝ) * (log q + 1 - log 2) / (π * ((H : ℝ) + 1)) + 1 / 2 :=
  leaf_odd_polya_expansion_proved χ hχ hq h_odd H hH n

end LeanLab.HelfgottMajor.PolyaVinogradov123
