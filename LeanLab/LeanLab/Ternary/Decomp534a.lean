/-
Helfgott https://arxiv.org/abs/1305.2897v4 pages 76 and 77.
Sine integral components of the argument preceding B.36.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.HelfgottArcs.Statements

namespace LeanLab.Ternary.Task534
open Real MeasureTheory Set Filter
open scoped Topology

/-- The sine integral on page 76 before B.36, with its removable singularity filled. -/
noncomputable def sineIntegral (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, Real.sinc u

/-- The sine integral is odd. Page 76, the two signed tails before B.36. -/
theorem sineIntegral_neg (x : ℝ) : sineIntegral (-x) = -sineIntegral x := by
  unfold sineIntegral
  have h := intervalIntegral.integral_comp_neg (a := -x) (b := 0) Real.sinc
  simp only [Real.sinc_neg, neg_zero, neg_neg] at h
  rw [← h, intervalIntegral.integral_symm]

/-- On the unit interval the sine integral lies between zero and its argument.
Page 76, the small argument estimate before B.36. -/
theorem sineIntegral_unit {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ sineIntegral x ∧ sineIntegral x ≤ x := by
  constructor
  · apply intervalIntegral.integral_nonneg hx
    intro u hu
    exact (Real.sinc_pos (by rw [abs_of_nonneg hu.1]; linarith [Real.pi_gt_three, hu.2])).le
  · have h := intervalIntegral.integral_mono_on hx
      (Real.continuous_sinc.intervalIntegrable 0 x)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 x)
      (fun u _ => Real.sinc_le_one u)
    simpa [sineIntegral] using h

/-- The inverse square majorant has its exact finite integral.
Page 76, the elementary integration by parts tail estimate before B.36. -/
theorem integral_inverse_square {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, 1 / u ^ 2) = 1 / a - 1 / b := by
  have hn : ∀ u ∈ uIcc a b, u ≠ 0 := by
    rw [uIcc_of_le hab]
    intro u hu
    exact ne_of_gt (lt_of_lt_of_le ha hu.1)
  have hi : IntervalIntegrable (fun u : ℝ => 1 / u ^ 2) volume a b :=
    (continuousOn_const.div (continuousOn_id.pow 2) (fun u hu => pow_ne_zero _ (hn u hu))).intervalIntegrable
  have hd : ∀ u ∈ uIcc a b, HasDerivAt (fun u : ℝ => -(1 / u)) (1 / u ^ 2) u := by
    intro u hu
    have hd := (hasDerivAt_inv (hn u hu)).neg
    convert hd using 1
    · funext v; simp [one_div]
    · simp [one_div]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa only [neg_sub_neg] using h

/-- Integration by parts for the finite sine tail.
Page 76, the tail estimate before B.36. No value at infinity is used. -/
theorem sine_tail_parts {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, Real.sin u / u) = Real.cos a / a - Real.cos b / b -
      ∫ u in a..b, Real.cos u / u ^ 2 := by
  have hn : ∀ u ∈ uIcc a b, u ≠ 0 := by
    rw [uIcc_of_le hab]
    intro u hu
    exact ne_of_gt (lt_of_lt_of_le ha hu.1)
  have hi : ContinuousOn (fun u : ℝ => u⁻¹) (uIcc a b) :=
    continuousOn_id.inv₀ hn
  have hi2 : ContinuousOn (fun u : ℝ => -(u ^ 2)⁻¹) (uIcc a b) :=
    ((continuousOn_id.pow 2).inv₀ (fun u hu => pow_ne_zero _ (hn u hu))).neg
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun u : ℝ => u⁻¹) (v := fun u : ℝ => -Real.cos u)
    (u' := fun u : ℝ => -(u ^ 2)⁻¹) (v' := Real.sin)
    (fun u hu => hasDerivAt_inv (hn u hu))
    (fun u _ => by convert (Real.hasDerivAt_cos u).neg using 1; simp)
    hi2.intervalIntegrable (Real.continuous_sin.intervalIntegrable a b)
  have h1 : (fun u : ℝ => u⁻¹ * Real.sin u) = (fun u => Real.sin u / u) := by
    funext u; simp [div_eq_mul_inv, mul_comm]
  have h2 : (fun u : ℝ => -(u ^ 2)⁻¹ * -Real.cos u) =
      (fun u => Real.cos u / u ^ 2) := by
    funext u; simp [div_eq_mul_inv, mul_comm]
  rw [h1, h2] at h
  calc
    _ = _ := h
    _ = _ := by ring

/-- The finite sine tail has size at most two divided by its positive lower endpoint.
Page 76, the integration by parts estimate before B.36. -/
theorem sine_tail_finite {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ u in a..b, Real.sin u / u| ≤ 2 / a := by
  have hb : 0 < b := ha.trans_le hab
  have hn : ∀ u ∈ uIcc a b, u ≠ 0 := by
    rw [uIcc_of_le hab]
    intro u hu
    exact ne_of_gt (ha.trans_le hu.1)
  have hq : ContinuousOn (fun u : ℝ => 1 / u ^ 2) (uIcc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun u hu => pow_ne_zero _ (hn u hu))
  have hc : ContinuousOn (fun u : ℝ => Real.cos u / u ^ 2) (uIcc a b) :=
    Real.continuous_cos.continuousOn.div (continuousOn_id.pow 2)
      (fun u hu => pow_ne_zero _ (hn u hu))
  have hi : |∫ u in a..b, Real.cos u / u ^ 2| ≤ 1 / a - 1 / b := by
    calc
      _ ≤ ∫ u in a..b, |Real.cos u / u ^ 2| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ u in a..b, 1 / u ^ 2 := by
        apply intervalIntegral.integral_mono_on hab hc.abs.intervalIntegrable hq.intervalIntegrable
        intro u _
        rw [abs_div, abs_sq]
        exact div_le_div_of_nonneg_right (Real.abs_cos_le_one u) (sq_nonneg u)
      _ = _ := integral_inverse_square ha hab
  have hea : |Real.cos a / a| ≤ 1 / a := by
    rw [abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one a) ha.le
  have heb : |Real.cos b / b| ≤ 1 / b := by
    rw [abs_div, abs_of_pos hb]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one b) hb.le
  rw [sine_tail_parts ha hab]
  calc
    _ ≤ |Real.cos a / a - Real.cos b / b| + |∫ u in a..b, Real.cos u / u ^ 2| :=
      abs_sub _ _
    _ ≤ (|Real.cos a / a| + |Real.cos b / b|) +
        |∫ u in a..b, Real.cos u / u ^ 2| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ (1 / a + 1 / b) + (1 / a - 1 / b) := add_le_add (add_le_add hea heb) hi
    _ = _ := by ring

/-- Differences of sine integrals equal the ordinary finite sine tail away from zero.
Page 76, definition of Si and the tail estimate before B.36. -/
theorem sineIntegral_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    sineIntegral b - sineIntegral a = ∫ u in a..b, Real.sin u / u := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.continuous_sinc.intervalIntegrable 0 a)
    (Real.continuous_sinc.intervalIntegrable a b)
  have heq : (∫ u in a..b, Real.sinc u) = ∫ u in a..b, Real.sin u / u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    exact Real.sinc_of_ne_zero (ne_of_gt (ha.trans_le hu.1))
  unfold sineIntegral
  linarith

/-- Every limit of Si has the explicit tail error bound from integration by parts.
Page 76, estimate before B.36. The value of the limit is a separate input. -/
theorem sineIntegral_tail_of_limit {L x : ℝ} (hx : 0 < x)
    (hL : Tendsto sineIntegral atTop (𝓝 L)) :
    |sineIntegral x - L| ≤ 2 / x := by
  have hlim : Tendsto (fun y => |sineIntegral y - sineIntegral x|) atTop
      (𝓝 |L - sineIntegral x|) := (hL.sub_const _).abs
  have hb : |L - sineIntegral x| ≤ 2 / x := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop x] with y hy
    rw [sineIntegral_sub hx hy]
    exact sine_tail_finite hx hy
  simpa only [abs_sub_comm] using hb

/-- Reflection of the negative sine integral error gives a growing exponential.
Page 76, the negative half of the integration by parts display before B.36. -/
theorem reflected_negative_tail (A H : ℝ) :
    (∫ w in -A..0, Real.exp (-w / H) * |sineIntegral w + Real.pi / 2|) =
      ∫ w in (0 : ℝ)..A, Real.exp (w / H) * |sineIntegral w - Real.pi / 2| := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := A)
    (fun w => Real.exp (-w / H) * |sineIntegral w + Real.pi / 2|)
  simp only [neg_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro w _
  change Real.exp (- -w / H) * |sineIntegral (-w) + Real.pi / 2| = _
  rw [neg_neg, sineIntegral_neg]
  congr 1
  calc
    |-sineIntegral w + Real.pi / 2| = |-(sineIntegral w - Real.pi / 2)| := by congr 1; ring
    _ = _ := abs_neg _

/-- The finite tail bound proves existence of the sine integral limit without its value.
Page 76, the convergence claim before B.36. -/
theorem sineIntegral_has_limit : ∃ L : ℝ, Tendsto sineIntegral atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  let N : ℝ := 2 / ε + 1
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sineIntegral_sub hN hn]
  apply lt_of_le_of_lt (sine_tail_finite hN hn)
  apply (div_lt_iff₀ hN).mpr
  have h : 2 / ε < N := by dsimp [N]; linarith
  have h' := (div_lt_iff₀ hε).mp h
  nlinarith

/-- The sine integral has derivative sinc, including at its removable singularity.
Page 76, the integration by parts step following B.35. -/
theorem hasDerivAt_sineIntegral (x : ℝ) :
    HasDerivAt sineIntegral (Real.sinc x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (Real.continuous_sinc.intervalIntegrable 0 x)
    Real.continuous_sinc.aestronglyMeasurable.stronglyMeasurableAtFilter
    Real.continuous_sinc.continuousAt

/-- Finite integration by parts against the sine integral.
Page 76, the integration by parts step following B.35. Endpoint terms are retained. -/
theorem sineIntegral_parts {a b : ℝ} {g g' : ℝ → ℝ}
    (hg : ∀ u ∈ uIcc a b, HasDerivAt g (g' u) u)
    (hg' : IntervalIntegrable g' volume a b) :
    (∫ u in a..b, g u * Real.sinc u) =
      g b * sineIntegral b - g a * sineIntegral a -
        ∫ u in a..b, g' u * sineIntegral u := by
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hg
    (fun u _ => hasDerivAt_sineIntegral u) hg'
    (Real.continuous_sinc.intervalIntegrable a b)

/-- No uniform constant turns the reflected exponential into a decaying exponential.
Derived obstruction to the reflection estimate on page 76 before B.36.
This is not a refutation of the full smoothing bound. -/
theorem reflected_weight_no_uniform_decay {H : ℝ} (hH : 0 < H) :
    ¬ ∃ C : ℝ, ∀ w : ℝ, 0 ≤ w →
      Real.exp (w / H) ≤ C * Real.exp (-w / H) := by
  rintro ⟨C, hC⟩
  have hC1 : 1 ≤ C := by simpa using hC 0 le_rfl
  have h := hC (H * (C + 1)) (by positivity)
  have heq : H * (C + 1) / H = C + 1 := by field_simp
  rw [heq, neg_div, heq] at h
  have he : Real.exp (-(C + 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ C)
  have hl := Real.add_one_le_exp (C + 1)
  linarith

/-- The elementary exponential rounding in the last inequality of B.36 is strict.
Helfgott page 77. This proves only the scalar step, not the disputed norm estimate. -/
theorem smoothing_scalar_rounding {H : ℝ} (hH : 0 < H) :
    1 - Real.exp (-(1 / H)) + (4 / Real.pi) * (Real.log H / H) <
      (1 + 4 / Real.pi * Real.log H) / H := by
  have he := Real.one_sub_lt_exp_neg (one_div_ne_zero hH.ne')
  have hid : (1 + 4 / Real.pi * Real.log H) / H =
      1 / H + (4 / Real.pi) * (Real.log H / H) := by ring
  rw [hid]
  linarith

/-- LEAF. The explicit value of any sine integral limit.
Abramowitz and Stegun page 232 display 5.2.25, cited on Helfgott page 76
before B.36. Existence alone is proved by sineIntegral_has_limit.
Source: https://personal.math.ubc.ca/~cbm/aands/page_232.htm . -/
theorem sineIntegral_value_leaf (L : ℝ)
    (hL : Tendsto sineIntegral atTop (𝓝 L)) : L = Real.pi / 2 := by
  sorry

/-- The proved existence and separate value leaf give the cited sine integral limit.
Page 76 and Abramowitz and Stegun page 232 display 5.2.25.
CONDITIONAL ON sineIntegral_value_leaf. -/
theorem sineIntegral_limit_value :
    Tendsto sineIntegral atTop (𝓝 (Real.pi / 2)) := by
  obtain ⟨L, hL⟩ := sineIntegral_has_limit
  rwa [sineIntegral_value_leaf L hL] at hL

/-- The positive sine integral tail bound follows from the separate limit value leaf.
Page 76, estimate before B.36. CONDITIONAL ON sineIntegral_value_leaf. -/
theorem sineIntegral_positive_tail {x : ℝ} (hx : 0 < x) :
    |sineIntegral x - Real.pi / 2| ≤ 2 / x :=
  sineIntegral_tail_of_limit hx sineIntegral_limit_value

/-- The negative sine integral tail bound follows by oddness.
Page 76, estimate before B.36. CONDITIONAL ON sineIntegral_value_leaf. -/
theorem sineIntegral_negative_tail {x : ℝ} (hx : x < 0) :
    |sineIntegral x + Real.pi / 2| ≤ 2 / |x| := by
  have h := sineIntegral_positive_tail (neg_pos.mpr hx)
  rw [sineIntegral_neg] at h
  have he : -sineIntegral x - Real.pi / 2 = -(sineIntegral x + Real.pi / 2) := by ring
  rw [he, abs_neg] at h
  simpa only [abs_of_neg hx] using h

/-- The logarithmic compact profile has a quadratic exponential envelope.
Derived truncation bound for the B.35 logarithmic integral on page 76.
The bound holds outside the support because the profile is zero there. -/
theorem hfun_logarithmic_envelope (v : ℝ) :
    |LeanLab.HelfgottArcs.hfun (Real.exp v)| ≤
      8 * Real.exp (3 / 2) * Real.exp (2 * v) := by
  unfold LeanLab.HelfgottArcs.hfun
  split_ifs with h
  · have hy := Real.exp_pos v
    have hz : 0 ≤ 2 - Real.exp v := sub_nonneg.mpr h.2
    have hp : (2 - Real.exp v) ^ 3 ≤ (2 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by linarith [h.2]) (by linarith) 3
    have he : Real.exp (Real.exp v - 1 / 2) ≤ Real.exp (3 / 2) :=
      Real.exp_le_exp.mpr (by linarith [h.2])
    have hnonneg : 0 ≤ Real.exp v ^ 2 * (2 - Real.exp v) ^ 3 *
        Real.exp (Real.exp v - 1 / 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hz 3)) (Real.exp_pos _).le
    rw [abs_of_nonneg hnonneg]
    calc
      _ ≤ (Real.exp v ^ 2 * 2 ^ 3) * Real.exp (3 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp (sq_nonneg _)) he
          (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [show Real.exp (2 * v) = Real.exp v ^ 2 by simpa using Real.exp_nat_mul v 2]; ring
  · simp only [abs_zero]
    positivity

/-- The removed negative logarithmic tail has an explicit integrable envelope.
Derived truncation bound for Helfgott page 76 equation B.35 at H two hundred.
It bounds the regularized sine kernel and does not identify the Mellin change of variables. -/
theorem logarithmic_tail_bound (t c : ℝ) :
    |∫ v in Set.Iic c, LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
        Real.sinc (200 * (Real.log t - v))| ≤
      4 * Real.exp (3 / 2) * (200 / Real.pi) * Real.exp (2 * c) := by
  let K : ℝ := 8 * Real.exp (3 / 2) * (200 / Real.pi)
  have hi : IntegrableOn (fun v => K * Real.exp (2 * v)) (Set.Iic c) :=
    (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) c).const_mul K
  have hd (v : ℝ) :
      |LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
        Real.sinc (200 * (Real.log t - v))| ≤ K * Real.exp (2 * v) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 200 / Real.pi)]
    calc
      _ ≤ (|LeanLab.HelfgottArcs.hfun (Real.exp v)| * (200 / Real.pi)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (by positivity)
      _ ≤ (8 * Real.exp (3 / 2) * Real.exp (2 * v)) * (200 / Real.pi) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_right (hfun_logarithmic_envelope v) (by positivity : (0 : ℝ) ≤ 200 / Real.pi)
      _ = _ := by dsimp [K]; ring
  calc
    _ ≤ ∫ v in Set.Iic c, |LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
        Real.sinc (200 * (Real.log t - v))| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Iic c))
        (fun v => LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
          Real.sinc (200 * (Real.log t - v)))
    _ ≤ ∫ v in Set.Iic c, K * Real.exp (2 * v) :=
      setIntegral_mono_of_nonneg (fun _ _ => abs_nonneg _) (fun v _ => hd v) hi
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 2)]
      dsimp [K]
      ring

/-- The diagnostic logarithmic cutoff minus thirty leaves a tail budget below ten to minus twenty two.
Derived numerical rounding of the page 76 B.35 truncation envelope.
This bound does not certify the quadrature on the retained interval. -/
theorem diagnostic_tail_rounding :
    4 * Real.exp (3 / 2) * (200 / Real.pi) * Real.exp (-60) <
      1 / (10 : ℝ) ^ 22 := by
  have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have he : Real.exp (3 / 2) ≤ 9 := by
    calc
      _ ≤ Real.exp (2 * 1) := Real.exp_le_exp.mpr (by norm_num)
      _ = Real.exp 1 ^ 2 := by simp
      _ ≤ (3 : ℝ) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le he1 2
      _ = _ := by norm_num
  have hp : (200 : ℝ) / Real.pi ≤ 100 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  have hc : 4 * Real.exp (3 / 2) * (200 / Real.pi) ≤ 3600 := by
    calc
      _ ≤ 4 * 9 * 100 := mul_le_mul
        (mul_le_mul_of_nonneg_left he (by norm_num)) hp (by positivity) (by norm_num)
      _ = _ := by norm_num
  have hl : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hm := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) hl 60
  have he60 : Real.exp (60 : ℝ) = Real.exp 1 ^ 60 := by
    simp
  have hb : (3600 : ℝ) * 10 ^ 22 < Real.exp 60 := by
    rw [he60]
    exact lt_of_lt_of_le (by norm_num) hm
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  norm_num at hb ⊢
  linarith

/-- The Mellin convolution has its exact regularized logarithmic integral.
Helfgott page 76 equation B.35, with y equal exp v. The single removable
kernel value is changed only on a null set. -/
theorem mconv_logarithmic_identity {t : ℝ} (ht : 0 < t) :
    LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun
      (LeanLab.HelfgottArcs.FH 200) t =
      ∫ v : ℝ, LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
        Real.sinc (200 * (Real.log t - v)) := by
  have hsub := integral_comp_exp (fun y => LeanLab.HelfgottArcs.hfun y *
    LeanLab.HelfgottArcs.FH 200 (t / y) / y)
  unfold LeanLab.HelfgottArcs.mconv
  rw [← hsub]
  calc
    _ = ∫ v : ℝ, LeanLab.HelfgottArcs.hfun (Real.exp v) *
        LeanLab.HelfgottArcs.FH 200 (t / Real.exp v) := by
      congr 1
      funext v
      simp only [smul_eq_mul]
      field_simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (Real.log t)] with v hv
      have hz : Real.log t - v ≠ 0 := sub_ne_zero.mpr hv.symm
      unfold LeanLab.HelfgottArcs.FH
      rw [Real.log_div ht.ne' (Real.exp_pos _).ne', Real.log_exp,
        Real.sinc_of_ne_zero (mul_ne_zero (by norm_num : (200 : ℝ) ≠ 0) hz)]
      field_simp

/-- The regularized logarithmic integrand is integrable on every left half line.
Derived justification for truncating the page 76 B.35 integral. -/
theorem logarithmic_integrable_left (t c : ℝ) :
    IntegrableOn (fun v => LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
      Real.sinc (200 * (Real.log t - v))) (Set.Iic c) := by
  let K : ℝ := 8 * Real.exp (3 / 2) * (200 / Real.pi)
  have hm : Measurable (fun v => LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
      Real.sinc (200 * (Real.log t - v))) := by
    have hh : Measurable (fun v => LeanLab.HelfgottArcs.hfun (Real.exp v)) := by
      unfold LeanLab.HelfgottArcs.hfun
      exact Measurable.ite (measurableSet_Icc.preimage Real.continuous_exp.measurable)
        (by fun_prop) measurable_const
    exact (hh.mul measurable_const).mul
      (Real.continuous_sinc.comp (by fun_prop)).measurable
  apply ((integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) c).const_mul K).mono'
    hm.aestronglyMeasurable
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 200 / Real.pi)]
  calc
    _ ≤ (|LeanLab.HelfgottArcs.hfun (Real.exp v)| * (200 / Real.pi)) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (by positivity)
    _ ≤ (8 * Real.exp (3 / 2) * Real.exp (2 * v)) * (200 / Real.pi) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (hfun_logarithmic_envelope v) (by positivity : (0 : ℝ) ≤ 200 / Real.pi)
    _ = _ := by dsimp [K]; ring

/-- The exact Mellin convolution differs from its finite logarithmic truncation
by at most the separately bounded negative tail. Helfgott page 76 equation B.35. -/
theorem mconv_logarithmic_truncation {t c : ℝ} (ht : 0 < t) (hc : c ≤ Real.log 2) :
    |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun
        (LeanLab.HelfgottArcs.FH 200) t -
      ∫ v in c..Real.log 2, LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
        Real.sinc (200 * (Real.log t - v))| ≤
      4 * Real.exp (3 / 2) * (200 / Real.pi) * Real.exp (2 * c) := by
  let f : ℝ → ℝ := fun v => LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
    Real.sinc (200 * (Real.log t - v))
  have hsupport : ∀ v, v ∉ Set.Iic (Real.log 2) → f v = 0 := by
    intro v hv
    have hlarge : (2 : ℝ) < Real.exp v := by
      exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mp (lt_of_not_ge hv)
    simp [f, LeanLab.HelfgottArcs.hfun, not_le_of_gt hlarge]
  have hwhole : (∫ v : ℝ, f v) = ∫ v in Set.Iic (Real.log 2), f v :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).symm
  have hi := logarithmic_integrable_left t (Real.log 2)
  have hsplit := intervalIntegral.integral_Iic_sub_Iic
    (hi.mono_set (Set.Iic_subset_Iic.mpr hc)) hi
  rw [mconv_logarithmic_identity ht]
  change |(∫ v : ℝ, f v) - ∫ v in c..Real.log 2, f v| ≤ _
  rw [hwhole, ← hsplit]
  convert logarithmic_tail_bound t c using 1
  congr 1
  dsimp [f]
  ring

/-- The numerical diagnostic differs from the actual Mellin convolution by less than ten to minus twenty two.
Helfgott page 76 equation B.35, derived truncation check at t equal exp of minus twenty.
The retained finite integral still needs a certified numerical evaluation. -/
theorem diagnostic_truncation_error :
    |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun
        (LeanLab.HelfgottArcs.FH 200) (Real.exp (-20)) -
      ∫ v in (-30 : ℝ)..Real.log 2, LeanLab.HelfgottArcs.hfun (Real.exp v) * (200 / Real.pi) *
        Real.sinc (200 * (-20 - v))| < 1 / (10 : ℝ) ^ 22 := by
  have hc : (-30 : ℝ) ≤ Real.log 2 := by
    have hp : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have h := mconv_logarithmic_truncation (t := Real.exp (-20)) (c := -30)
    (Real.exp_pos _) hc
  norm_num only [Real.log_exp, mul_neg, mul_zero, neg_mul, show (2 : ℝ) * 30 = 60 by norm_num] at h
  exact lt_of_le_of_lt h diagnostic_tail_rounding

/-- The small positive argument sine error is at most pi over two without a limit value input.
Helfgott page 76, the unit interval estimate before B.36. -/
theorem sineIntegral_small_positive {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |sineIntegral x - Real.pi / 2| ≤ Real.pi / 2 := by
  have h := sineIntegral_unit hx hx1
  rw [abs_of_nonpos (by linarith [Real.pi_gt_three])]
  linarith

/-- The small negative argument sine error is at most pi over two without a limit value input.
Helfgott page 76, the negative unit interval estimate before B.36. -/
theorem sineIntegral_small_negative {x : ℝ} (hx : -1 ≤ x) (hx0 : x ≤ 0) :
    |sineIntegral x + Real.pi / 2| ≤ Real.pi / 2 := by
  have h := sineIntegral_unit (x := -x) (by linarith) (by linarith)
  rw [sineIntegral_neg] at h
  rw [abs_of_nonneg (by linarith [Real.pi_gt_three])]
  linarith

/-- A finite interval of cosine curvature supplies a strict positive gap in the sine tail majorant.
Derived finite version of the strict tail estimate on Helfgott page 76 before B.36. -/
theorem sine_tail_finite_gap {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    |∫ u in a..c, Real.sin u / u| ≤ 2 / a -
      ∫ u in a..b, (1 - |Real.cos u|) / u ^ 2 := by
  have hac : a ≤ c := hab.trans hbc
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := ha.trans_le hac
  have hq : ContinuousOn (fun u : ℝ => 1 / u ^ 2) (uIcc a c) := by
    apply continuousOn_const.div (continuousOn_id.pow 2)
    rw [uIcc_of_le hac]
    intro u hu
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le hu.1))
  have hf : ContinuousOn (fun u : ℝ => |Real.cos u| / u ^ 2) (uIcc a c) := by
    apply Real.continuous_cos.abs.continuousOn.div (continuousOn_id.pow 2)
    rw [uIcc_of_le hac]
    intro u hu
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le hu.1))
  have hsab : uIcc a b ⊆ uIcc a c := by
    rw [uIcc_of_le hab, uIcc_of_le hac]
    exact Icc_subset_Icc le_rfl hbc
  have hsbc : uIcc b c ⊆ uIcc a c := by
    rw [uIcc_of_le hbc, uIcc_of_le hac]
    exact Icc_subset_Icc hab le_rfl
  have hqab := (hq.mono hsab).intervalIntegrable (μ := volume)
  have hqbc := (hq.mono hsbc).intervalIntegrable (μ := volume)
  have hfab := (hf.mono hsab).intervalIntegrable (μ := volume)
  have hfbc := (hf.mono hsbc).intervalIntegrable (μ := volume)
  have hleft : (∫ u in a..b, |Real.cos u| / u ^ 2) = 1 / a - 1 / b -
      ∫ u in a..b, (1 - |Real.cos u|) / u ^ 2 := by
    have hid : (fun u : ℝ => (1 - |Real.cos u|) / u ^ 2) =
        (fun u => 1 / u ^ 2 - |Real.cos u| / u ^ 2) := by funext u; ring
    rw [hid, intervalIntegral.integral_sub hqab hfab, integral_inverse_square ha hab]
    ring
  have hright : (∫ u in b..c, |Real.cos u| / u ^ 2) ≤ 1 / b - 1 / c := by
    rw [← integral_inverse_square hb hbc]
    apply intervalIntegral.integral_mono_on hbc hfbc hqbc
    intro u _
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one u) (sq_nonneg u)
  have hcos : |∫ u in a..c, Real.cos u / u ^ 2| ≤ 1 / a - 1 / c -
      ∫ u in a..b, (1 - |Real.cos u|) / u ^ 2 := by
    calc
      _ ≤ ∫ u in a..c, |Real.cos u / u ^ 2| := intervalIntegral.abs_integral_le_integral_abs hac
      _ = ∫ u in a..c, |Real.cos u| / u ^ 2 := by simp only [abs_div, abs_sq]
      _ = (∫ u in a..b, |Real.cos u| / u ^ 2) + ∫ u in b..c, |Real.cos u| / u ^ 2 :=
        (intervalIntegral.integral_add_adjacent_intervals hfab hfbc).symm
      _ ≤ _ := by linarith
  have hea : |Real.cos a / a| ≤ 1 / a := by
    rw [abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one a) ha.le
  have hec : |Real.cos c / c| ≤ 1 / c := by
    rw [abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one c) hc.le
  rw [sine_tail_parts ha hac]
  calc
    _ ≤ |Real.cos a / a - Real.cos c / c| + |∫ u in a..c, Real.cos u / u ^ 2| := abs_sub _ _
    _ ≤ (|Real.cos a / a| + |Real.cos c / c|) + |∫ u in a..c, Real.cos u / u ^ 2| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (1 / a + 1 / c) + (1 / a - 1 / c -
        ∫ u in a..b, (1 - |Real.cos u|) / u ^ 2) := add_le_add (add_le_add hea hec) hcos
    _ = _ := by ring

/-- The finite cosine defect is positive on every positive interval of length pi.
Derived strictness step for Helfgott page 76 before B.36. -/
theorem cosine_defect_positive {a : ℝ} (ha : 0 < a) :
    0 < ∫ u in a..a + Real.pi, (1 - |Real.cos u|) / u ^ 2 := by
  apply intervalIntegral.integral_pos (by linarith [Real.pi_pos])
  · apply (continuousOn_const.sub Real.continuous_cos.abs.continuousOn).div
      (continuousOn_id.pow 2)
    intro u hu
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le hu.1))
  · intro u _
    exact div_nonneg (sub_nonneg.mpr (Real.abs_cos_le_one u)) (sq_nonneg u)
  · by_cases h : |Real.cos a| < 1
    · refine ⟨a, ⟨le_rfl, by linarith [Real.pi_pos]⟩, ?_⟩
      exact div_pos (sub_pos.mpr h) (sq_pos_of_pos ha)
    · have he : |Real.cos a| = 1 := le_antisymm (Real.abs_cos_le_one a) (le_of_not_gt h)
      have hc : Real.cos a ^ 2 = 1 := by rw [← sq_abs, he]; norm_num
      have hs : Real.sin a = 0 := by nlinarith [Real.sin_sq_add_cos_sq a]
      refine ⟨a + Real.pi / 2, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, ?_⟩
      rw [Real.cos_add_pi_div_two, hs]
      simp only [neg_zero, abs_zero, sub_zero, one_div]
      positivity

/-- Every finite sine integral limit has the strict tail bound printed on page 76 before B.36.
The positive cosine defect keeps a uniform gap when the upper endpoint tends to infinity. -/
theorem sineIntegral_tail_strict_of_limit {L x : ℝ} (hx : 0 < x)
    (hL : Tendsto sineIntegral atTop (𝓝 L)) :
    |sineIntegral x - L| < 2 / x := by
  have hp : x ≤ x + Real.pi := by linarith [Real.pi_pos]
  have hlim := (hL.sub_const (sineIntegral x)).abs
  have hb : |L - sineIntegral x| ≤ 2 / x -
      ∫ u in x..x + Real.pi, (1 - |Real.cos u|) / u ^ 2 := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (x + Real.pi)] with y hy
    rw [sineIntegral_sub hx (hp.trans hy)]
    exact sine_tail_finite_gap hx hp hy
  have hd := cosine_defect_positive hx
  rw [abs_sub_comm] at hb
  linarith

/-- The printed strict positive sine tail follows from the isolated explicit value leaf.
Helfgott page 76 before B.36. CONDITIONAL ON sineIntegral_value_leaf. -/
theorem sineIntegral_positive_tail_strict {x : ℝ} (hx : 0 < x) :
    |sineIntegral x - Real.pi / 2| < 2 / x :=
  sineIntegral_tail_strict_of_limit hx sineIntegral_limit_value

/-- The printed strict negative sine tail follows from oddness and the explicit value leaf.
Helfgott page 76 before B.36. CONDITIONAL ON sineIntegral_value_leaf. -/
theorem sineIntegral_negative_tail_strict {x : ℝ} (hx : x < 0) :
    |sineIntegral x + Real.pi / 2| < 2 / |x| := by
  have h := sineIntegral_positive_tail_strict (neg_pos.mpr hx)
  rw [sineIntegral_neg] at h
  have he : -sineIntegral x - Real.pi / 2 = -(sineIntegral x + Real.pi / 2) := by ring
  rw [he, abs_neg] at h
  simpa only [abs_of_neg hx] using h

end LeanLab.Ternary.Task534
