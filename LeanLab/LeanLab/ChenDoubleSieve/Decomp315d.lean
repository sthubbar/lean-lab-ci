import LeanLab.ChenDoubleSieve.Decomp275i

/-!
Supply split for Wu 2004 Section 10.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- Split the upper sieve coefficient at three using both known local formulas.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem upper_weighted_split {F f : ℝ → ℝ} (h : IsLinearSieve F f)
    {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    4 / exp eulerMascheroniConstant *
      (∫ t in a..5, F t / (1 - t / 6)) =
    8 * (∫ t in a..3, 1 / (t * (1 - t / 6))) +
    8 * (∫ t in (3 : ℝ)..5,
      (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6))) := by
  have hFi : IntervalIntegrable (fun t => F t / (1 - t / 6)) volume a 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : a ≤ 5)]
    refine (h.1.mono (fun t ht => ?_)).div (by fun_prop) ?_
    · change 0 < t
      linarith [ht.1]
    · intro t ht
      linarith [ht.2]
  have hi₁ : IntervalIntegrable (fun t => F t / (1 - t / 6)) volume a 3 := by
    apply hFi.mono_set
    rw [Set.uIcc_of_le ha3, Set.uIcc_of_le (by linarith : a ≤ 5)]
    exact Set.Icc_subset_Icc_right (by norm_num)
  have hi₂ : IntervalIntegrable (fun t => F t / (1 - t / 6)) volume 3 5 := by
    apply hFi.mono_set
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5),
      Set.uIcc_of_le (by linarith : a ≤ 5)]
    exact Set.Icc_subset_Icc_left ha3
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, mul_add]
  have hsmall : (∫ t in a..3, F t / (1 - t / 6)) =
      (2 * exp eulerMascheroniConstant) * ∫ t in a..3, 1 / (t * (1 - t / 6)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le ha3] at ht
    dsimp only
    rw [Task275.linear_upper_three h (by linarith [ht.1]) ht.2]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hlarge : (∫ t in (3 : ℝ)..5, F t / (1 - t / 6)) =
      (2 * exp eulerMascheroniConstant) * ∫ t in (3 : ℝ)..5,
        (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at ht
    dsimp only
    rw [Task275.linear_upper_five h ht]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsmall, hlarge]
  field_simp [Real.exp_ne_zero]
  <;> ring

/-- The actual F2 coefficient has an elementary split at the sieve transition.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem F2_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 2 =
    8 * (∫ t in (258 / 125 : ℝ)..3, 1 / (t * (1 - t / 6))) +
    8 * (∫ t in (3 : ℝ)..5,
      (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6))) := by
  change 4 / exp eulerMascheroniConstant *
    (∫ t in ((1 / 2 - sigma1) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t)) = _
  norm_num only [kappa1, sigma1, show (1 / 2 - 41 / 125 : ℝ) / (1 / 12) = 258 / 125 by norm_num,
    show (1 / 2 - 1 / 12 : ℝ) / (1 / 12) = 5 by norm_num]
  convert upper_weighted_split h (a := 258 / 125) (by norm_num) (by norm_num) using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring

/-- The actual F3 coefficient shares the same upper tail as F2.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem F3_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 3 =
    8 * (∫ t in (327 / 125 : ℝ)..3, 1 / (t * (1 - t / 6))) +
    8 * (∫ t in (3 : ℝ)..5,
      (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6))) := by
  change 4 / exp eulerMascheroniConstant *
    (∫ t in ((1 / 2 - sigma2) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t)) = _
  norm_num only [kappa1, sigma2, show (1 / 2 - 141 / 500 : ℝ) / (1 / 12) = 327 / 125 by norm_num,
    show (1 / 2 - 1 / 12 : ℝ) / (1 / 12) = 5 by norm_num]
  convert upper_weighted_split h (a := 327 / 125) (by norm_num) (by norm_num) using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring

/-- The elementary part of F2 and F3 has an exact logarithmic antiderivative.
Source: page 39 equation 10.4, derived integration helper. -/
theorem reciprocal_head {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    (∫ t in a..3, 1 / (t * (1 - t / 6))) = log ((6 - a) / a) := by
  have hcont₁ : ContinuousOn (fun t : ℝ => (1 : ℝ) / t) (Set.uIcc a 3) := by
    rw [Set.uIcc_of_le ha3]
    refine continuousOn_const.div continuousOn_id ?_
    intro t ht
    linarith [ht.1]
  have hcont₂ : ContinuousOn (fun t : ℝ => (1 : ℝ) / (6 - t)) (Set.uIcc a 3) := by
    rw [Set.uIcc_of_le ha3]
    refine continuousOn_const.div (by fun_prop) ?_
    intro t ht
    linarith [ht.2]
  have he : (∫ t in a..3, 1 / (t * (1 - t / 6))) =
      (∫ t in a..3, 1 / t) + ∫ t in a..3, 1 / (6 - t) := by
    rw [← intervalIntegral.integral_add hcont₁.intervalIntegrable hcont₂.intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le ha3] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht6 : 6 - t ≠ 0 := by linarith [ht.2]
    have htden : 1 - t / 6 ≠ 0 := by linarith [ht.2]
    field_simp [ht0, ht6, htden]
    <;> ring
  rw [he]
  simp only [one_div]
  rw [integral_inv_of_pos ha (by norm_num),
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 6]
  norm_num only [show (6 - 3 : ℝ) = 3 by norm_num]
  rw [integral_inv_of_pos (by norm_num) (by linarith : 0 < 6 - a),
    Real.log_div (by norm_num : (3 : ℝ) ≠ 0) ha.ne',
    Real.log_div (by linarith : 6 - a ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_div (by linarith : 6 - a ≠ 0) ha.ne']
  ring

/-- F2 and F3 differ only by an elementary logarithmic head.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem F2_sub_F3 {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 2 - integralTerms F f ω 3 =
      8 * (log (82 / 43 : ℝ) - log (141 / 109 : ℝ)) := by
  rw [F2_elementary h ω, F3_elementary h ω,
    reciprocal_head (a := 258 / 125) (by norm_num) (by norm_num),
    reciprocal_head (a := 327 / 125) (by norm_num) (by norm_num)]
  norm_num only [show (6 - 258 / 125 : ℝ) / (258 / 125) = 82 / 43 by norm_num,
    show (6 - 327 / 125 : ℝ) / (327 / 125) = 141 / 109 by norm_num]
  ring

set_option maxHeartbeats 2000000

/-! ### Rational logarithm series, cast to the reals -/

section quadrature

open Set Filter Topology
open intervalIntegral

private lemma rat_logLower_cast (N : ℕ) (y : ℚ) :
    ((∑ j ∈ range N, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1) : ℚ) : ℝ) =
      ∑ j ∈ range N, (((y : ℝ) - 1) / ((y : ℝ) + 1)) ^ (2 * j + 1) / (2 * j + 1) := by
  push_cast
  rfl

private lemma rat_logUpper_cast (N : ℕ) (y : ℚ) :
    ((2 * (∑ j ∈ range N, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1) : ℚ)
        + 2 * ((y - 1) / (y + 1)) ^ (2 * N + 1) / (1 - ((y - 1) / (y + 1)) ^ 2) : ℚ) : ℝ) =
      Wu04Integral.logUpper N (y : ℝ) := by
  rw [Wu04Integral.logUpper, Wu04Integral.logLower]
  push_cast
  ring

private lemma rat_logLower_cast' (N : ℕ) (y : ℚ) :
    ((2 * (∑ j ∈ range N, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1)) : ℚ) : ℝ) =
      Wu04Integral.logLower N (y : ℝ) := by
  rw [Wu04Integral.logLower]
  push_cast
  ring

/-! ### Two-sided polynomial bounds for `log` on `[0, 1/2]` -/

private lemma log_one_add_abs {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    |Real.log (1 + s) - ∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)|
      ≤ 2 * s ^ (n + 1) := by
  have hx : |-s| < 1 := by
    rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have hsum : (∑ i ∈ range n, (-s) ^ (i + 1) / (i + 1) : ℝ)
      = -(∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [neg_pow]
    have : (-1 : ℝ) ^ (i + 1) = -((-1) ^ i) := by
      rw [pow_succ]
      ring
    rw [this]
    ring
  have h1s : (1 : ℝ) - -s = 1 + s := by ring
  rw [hsum, h1s, abs_neg, abs_of_nonneg h0] at h
  calc |Real.log (1 + s) - ∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)|
      = |-(∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) + Real.log (1 + s)| := by
        rw [neg_add_eq_sub, abs_sub_comm]
    _ ≤ s ^ (n + 1) / (1 - s) := h
    _ ≤ 2 * s ^ (n + 1) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg h0 (n + 1), h0]

private lemma log_one_add_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    Real.log (1 + s) ≤ (∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) + 2 * s ^ (n + 1) := by
  have h := (abs_le.mp (log_one_add_abs h0 h1 n)).2
  linarith

private lemma log_one_add_ge {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    (∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) - 2 * s ^ (n + 1) ≤ Real.log (1 + s) := by
  have h := (abs_le.mp (log_one_add_abs h0 h1 n)).1
  linarith

private lemma log_one_add_ge9 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) - 2 * u ^ 9 ≤ Real.log (1 + u) := by
  have h := log_one_add_ge (s := u) h0 h1 8
  simpa using h

private lemma log_one_add_le9 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    Real.log (1 + u) ≤ (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) + 2 * u ^ 9 := by
  have h := log_one_add_le (s := u) h0 h1 8
  simpa using h

private lemma log_one_sub_abs {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    |Real.log (1 - s) + ∑ i ∈ range n, s ^ (i + 1) / (i + 1)| ≤ 2 * s ^ (n + 1) := by
  have hx : |s| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have h1s : (1 : ℝ) - s = 1 - s := rfl
  rw [h1s, abs_of_nonneg h0] at h
  calc |Real.log (1 - s) + ∑ i ∈ range n, s ^ (i + 1) / (i + 1)|
      = |(∑ i ∈ range n, s ^ (i + 1) / (i + 1)) + Real.log (1 - s)| := by rw [add_comm]
    _ ≤ s ^ (n + 1) / (1 - s) := h
    _ ≤ 2 * s ^ (n + 1) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg h0 (n + 1), h0]

private lemma log_one_sub_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    Real.log (1 - s) ≤ -(∑ i ∈ range n, s ^ (i + 1) / (i + 1)) + 2 * s ^ (n + 1) := by
  have h := (abs_le.mp (log_one_sub_abs h0 h1 n)).2
  linarith

private lemma log_one_sub_ge {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    -(∑ i ∈ range n, s ^ (i + 1) / (i + 1)) - 2 * s ^ (n + 1) ≤ Real.log (1 - s) := by
  have h := (abs_le.mp (log_one_sub_abs h0 h1 n)).1
  linarith

private lemma inv_geom_bounds {p h : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hs : h ≤ p / 2) (L : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) h) :
    (∑ l ∈ range (L + 1), (-(t / p)) ^ l) * (1 / p) - (1 / p) * ((h / p) ^ (L + 1) / (1 - h / p))
        ≤ 1 / (p + t) ∧
      1 / (p + t) ≤
        (∑ l ∈ range (L + 1), (-(t / p)) ^ l) * (1 / p) + (1 / p) * ((h / p) ^ (L + 1) / (1 - h / p)) := by
  have hpne : p ≠ 0 := hp.ne'
  have hu0 : 0 ≤ t / p := div_nonneg ht.1 hp.le
  have huh : t / p ≤ h / p := by gcongr; exact ht.2
  have hhr : h / p ≤ 1 / 2 := by rw [div_le_iff₀ hp]; linarith
  have hpos : (0 : ℝ) < 1 - h / p := by linarith
  have h2 : (0:ℝ) < 1 + t / p := by linarith
  -- geometric identity
  have hne : (-(t / p) - 1) ≠ 0 := by
    have h : -(t / p) - 1 = -(1 + t / p) := by ring
    rw [h]; exact neg_ne_zero.mpr h2.ne'
  have hval : (∑ l ∈ range (L + 1), (-(t / p)) ^ l) = ((-(t / p)) ^ (L + 1) - 1) / (-(t / p) - 1) := by
    rw [eq_div_iff hne]
    simpa only [mul_comm] using geom_sum_mul (-(t / p)) (L + 1)
  have hgeom : (∑ l ∈ range (L + 1), (-(t / p)) ^ l) + (-(t / p)) ^ (L + 1) / (1 + t / p)
      = 1 / (1 + t / p) := by
    rw [hval, show (-(t / p)) - 1 = -(1 + t / p) by ring, div_neg]
    field_simp
    ring
  have habs : |(-(t / p)) ^ (L + 1) / (1 + t / p)| ≤ (h / p) ^ (L + 1) / (1 - h / p) := by
    have h3 : 1 - h / p ≤ 1 + t / p := by linarith
    rw [abs_div, abs_pow, abs_neg, abs_of_nonneg hu0, abs_of_pos h2]
    exact div_le_div₀ (pow_nonneg (by positivity : (0:ℝ) ≤ h / p) _) (pow_le_pow_left₀ hu0 huh _) hpos h3
  have hkey : 1 / (p + t) = (1 / p) * (∑ l ∈ range (L + 1), (-(t / p)) ^ l)
      + (1 / p) * ((-(t / p)) ^ (L + 1) / (1 + t / p)) := by
    have hpt : p + t = p * (1 + t / p) := by field_simp
    have hsplit : 1 / (p * (1 + t / p)) = (1 / p) * (1 / (1 + t / p)) := by
      field_simp
    rw [hpt, hsplit, ← hgeom]
    ring
  have hpp : (0:ℝ) < 1 / p := by positivity
  constructor
  · rw [hkey]
    have h := neg_abs_le ((-(t / p)) ^ (L + 1) / (1 + t / p))
    nlinarith
  · rw [hkey]
    have h := le_abs_self ((-(t / p)) ^ (L + 1) / (1 + t / p))
    nlinarith

private lemma contAt_of_contOn {f : ℝ → ℝ} {a b x : ℝ} (ha : a ≤ b)
    (h : ContinuousOn f (uIcc a b)) (hx : x ∈ Ioo a b) : ContinuousAt f x :=
  h.continuousAt (by rw [Set.uIcc_of_le ha]; exact Icc_mem_nhds hx.1 hx.2)

private lemma triangle_swap {f h : ℝ → ℝ} {c A B : ℝ}
    (hc : 0 ≤ c) (hAB : A ≤ B - c)
    (hf : ContinuousOn f (uIcc (A - c) (B - c))) (hh : ContinuousOn h (uIcc A B)) :
    ∫ t in A..B, (∫ x in (A - c)..(t - c), f x) * h t
      = ∫ x in (A - c)..(B - c), f x * (∫ t in (x + c)..B, h t) := by
  have hAc : A - c ≤ B - c := by linarith
  have hAB' : A ≤ B := by linarith
  set F : ℝ → ℝ := fun x => ∫ s in (A - c)..x, f s with hFdef
  set K : ℝ → ℝ := fun s => ∫ t in A..s, h t with hKdef
  have hfi : IntervalIntegrable f volume (A - c) (B - c) := hf.intervalIntegrable
  have hhi : IntervalIntegrable h volume A B := hh.intervalIntegrable
  have hFc : ContinuousOn F (uIcc (A - c) (B - c)) := by
    rw [hFdef]; exact continuousOn_primitive_interval' hfi (Set.left_mem_uIcc)
  have hKc : ContinuousOn K (uIcc A B) := by
    rw [hKdef]; exact continuousOn_primitive_interval' hhi (Set.left_mem_uIcc)
  -- continuity of the two integrands on the full interval
  have hφc : ContinuousOn (fun t => F (t - c) * h t) (uIcc A B) := by
    refine ContinuousOn.mul ?_ hh
    refine hFc.comp (by fun_prop) ?_
    intro t ht
    rw [Set.uIcc_of_le hAB'] at ht
    rw [Set.uIcc_of_le hAc]
    constructor <;> linarith [ht.1, ht.2]
  have hgc : ContinuousOn (fun x => f x * K (x + c)) (uIcc (A - c) (B - c)) := by
    refine ContinuousOn.mul hf ?_
    refine hKc.comp (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le hAc] at hx
    rw [Set.uIcc_of_le hAB']
    constructor <;> linarith [hx.1, hx.2, hc]
  have hφi : ∀ {u v : ℝ}, A ≤ u → u ≤ v → v ≤ B → IntervalIntegrable (fun t => F (t - c) * h t) volume u v := by
    intro u v h1 h2 h3
    apply (hφc.mono ?_).intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le h2] at ht
    rw [Set.uIcc_of_le hAB']
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgi : IntervalIntegrable (fun x => f x * K (x + c)) volume (A - c) (B - c) :=
    hgc.intervalIntegrable
  have hhi' : ∀ {u v : ℝ}, A ≤ u → u ≤ v → v ≤ B → IntervalIntegrable h volume u v := by
    intro u v hu huv hvB
    apply (hh.mono ?_).intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    rw [Set.uIcc_of_le hAB']
    exact ⟨by linarith [ht.1, hu], by linarith [ht.2, hvB]⟩
  have hgi' : ∀ {v : ℝ}, A - c ≤ v → v ≤ B - c →
      IntervalIntegrable (fun x => f x * K (x + c)) volume (A - c) v := by
    intro v hv1 hv2
    apply (hgc.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hv1] at hx
    rw [Set.uIcc_of_le hAc]
    exact ⟨hx.1, by linarith [hx.2]⟩
  -- derivative of the outer primitive
  have dG : ∀ y ∈ Ioo A B,
      HasDerivAt (fun y => ∫ t in A..y, F (t - c) * h t) (F (y - c) * h y) y := by
    intro y hy
    have hcy : ContinuousAt (fun t => F (t - c) * h t) y := by
      refine ContinuousAt.mul ?_ (contAt_of_contOn hAB' hh hy)
      exact (contAt_of_contOn hAc hFc ⟨by linarith [hy.1], by linarith [hy.2]⟩).comp
        (by fun_prop : ContinuousAt (fun t : ℝ => t - c) y)
    have hφopen : ContinuousOn (fun t => F (t - c) * h t) (Ioo A B) := by
      refine hφc.mono ?_
      intro t ht
      rw [Set.uIcc_of_le hAB']
      exact ⟨ht.1.le, ht.2.le⟩
    have hsm : StronglyMeasurableAtFilter (fun t => F (t - c) * h t) (𝓝 y) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hφopen y hy
    exact integral_hasDerivAt_right (hφi le_rfl (le_of_lt hy.1) (le_of_lt hy.2)) hsm hcy
  -- derivative of the inner primitive
  have dPrim : ∀ y ∈ Ioo A B,
      HasDerivAt (fun y => ∫ x in (A - c)..(y - c), f x * K (x + c)) (f (y - c) * K y) y := by
    intro y hy
    have hyc : y - c ∈ Ioo (A - c) (B - c) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hcy : ContinuousAt (fun x => f x * K (x + c)) (y - c) := by
      refine ContinuousAt.mul (contAt_of_contOn hAc hf hyc) ?_
      exact (contAt_of_contOn hAB' hKc ⟨by linarith [hyc.1], by linarith [hyc.2, hc]⟩).comp
        (by fun_prop : ContinuousAt (fun x : ℝ => x + c) (y - c))
    have hgopen : ContinuousOn (fun x => f x * K (x + c)) (Ioo (A - c) (B - c)) := by
      refine hgc.mono ?_
      intro t ht
      rw [Set.uIcc_of_le hAc]
      exact ⟨ht.1.le, ht.2.le⟩
    have hsm : StronglyMeasurableAtFilter (fun x => f x * K (x + c)) (𝓝 (y - c)) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hgopen (y - c) hyc
    have h1 : HasDerivAt (fun z => ∫ x in (A - c)..z, f x * K (x + c))
        (f (y - c) * K (y - c + c)) (y - c) :=
      integral_hasDerivAt_right (hgi' (by linarith [hyc.1]) (by linarith [hyc.2])) hsm hcy
    have h2 : HasDerivAt (fun y : ℝ => y - c) 1 y := by
      simpa using (hasDerivAt_id y).sub_const c
    simpa [Function.comp_def, sub_add_cancel] using h1.comp y h2
  -- derivative of F ∘ (· - c)
  have dFc : ∀ y ∈ Ioo A B, HasDerivAt (fun y => F (y - c)) (f (y - c)) y := by
    intro y hy
    have hyc : y - c ∈ Ioo (A - c) (B - c) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hcy : ContinuousAt f (y - c) := contAt_of_contOn hAc hf hyc
    have hfopen : ContinuousOn f (Ioo (A - c) (B - c)) := by
      refine hf.mono ?_
      intro t ht
      rw [Set.uIcc_of_le hAc]
      exact ⟨ht.1.le, ht.2.le⟩
    have hsm : StronglyMeasurableAtFilter f (𝓝 (y - c)) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hfopen (y - c) hyc
    have h1 : HasDerivAt F (f (y - c)) (y - c) := by
      rw [hFdef]
      have hv : IntervalIntegrable f volume (A - c) (y - c) := by
        apply (hf.mono ?_).intervalIntegrable
        intro t ht
        rw [Set.uIcc_of_le (by linarith [hyc.1])] at ht
        rw [Set.uIcc_of_le hAc]
        exact ⟨ht.1, by linarith [ht.2, hyc.2]⟩
      exact integral_hasDerivAt_right hv hsm hcy
    have h2 : HasDerivAt (fun y : ℝ => y - c) 1 y := by
      simpa using (hasDerivAt_id y).sub_const c
    simpa [Function.comp_def] using h1.comp y h2
  have dK : ∀ y ∈ Ioo A B, HasDerivAt K (h y) y := by
    intro y hy
    have hcy : ContinuousAt h y := contAt_of_contOn hAB' hh hy
    have hhy : IntervalIntegrable h volume A y := hhi' (u := A) (v := y) le_rfl (le_of_lt hy.1) (le_of_lt hy.2)
    have hhopen : ContinuousOn h (Ioo A B) := by
      refine hh.mono ?_
      intro t ht
      rw [Set.uIcc_of_le hAB']
      exact ⟨ht.1.le, ht.2.le⟩
    have hsm : StronglyMeasurableAtFilter h (𝓝 y) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hhopen y hy
    rw [hKdef]
    exact integral_hasDerivAt_right hhy hsm hcy
  -- continuity of the difference function on [A,B]
  have hWcont : ContinuousOn
      (fun y => (∫ t in A..y, F (t - c) * h t)
        - ((∫ t in A..y, h t) * F (y - c) - ∫ x in (A - c)..(y - c), f x * K (x + c)))
      (Icc A B) := by
    have h1 : ContinuousOn (fun y => ∫ t in A..y, F (t - c) * h t) (Icc A B) := by
      have h := continuousOn_primitive_interval' (hφi le_rfl hAB' le_rfl) (Set.left_mem_uIcc (a := A) (b := B))
      rwa [Set.uIcc_of_le hAB'] at h
    have h2 : ContinuousOn (fun y => ∫ t in A..y, h t) (Icc A B) := by
      have h := continuousOn_primitive_interval' hhi (Set.left_mem_uIcc (a := A) (b := B))
      rwa [Set.uIcc_of_le hAB'] at h
    have h3 : ContinuousOn (fun y => F (y - c)) (Icc A B) := by
      refine hFc.comp (by fun_prop) ?_
      intro y hy
      rw [Set.uIcc_of_le hAc]
      constructor <;> linarith [hy.1, hy.2]
    have h4 : ContinuousOn (fun y => ∫ x in (A - c)..(y - c), f x * K (x + c)) (Icc A B) := by
      have hb := continuousOn_primitive_interval' hgi (Set.left_mem_uIcc (a := A - c) (b := B - c))
      have hcomp : (fun y : ℝ => ∫ x in (A - c)..(y - c), f x * K (x + c))
          = (fun y : ℝ => (fun z => ∫ x in (A - c)..z, f x * K (x + c)) (y - c)) := rfl
      rw [hcomp]
      refine hb.comp (by fun_prop) ?_
      intro y hy
      rw [Set.uIcc_of_le hAc]
      constructor <;> linarith [hy.1, hy.2]
    exact h1.sub ((h2.mul h3).sub h4)
  -- zero derivative in the interior
  have hWderiv : ∀ y ∈ Ioo A B,
      HasDerivAt (fun y => (∫ t in A..y, F (t - c) * h t)
        - ((∫ t in A..y, h t) * F (y - c) - ∫ x in (A - c)..(y - c), f x * K (x + c))) 0 y := by
    intro y hy
    have h1 := dG y hy
    have h2 := (dK y hy).mul (dFc y hy)
    have h3 := dPrim y hy
    have hd := h1.sub (h2.sub h3)
    have hval : F (y - c) * h y - (h y * F (y - c) + K y * f (y - c) - f (y - c) * K y) = 0 := by
      ring
    rw [← hval]
    exact hd
  -- conclude
  have key : (∫ t in A..B, F (t - c) * h t)
      = (∫ t in A..B, h t) * F (B - c) - ∫ x in (A - c)..(B - c), f x * K (x + c) := by
    have hzero : (∫ y in A..B, (0 : ℝ)) = (fun y => (∫ t in A..y, F (t - c) * h t)
        - ((∫ t in A..y, h t) * F (y - c) - ∫ x in (A - c)..(y - c), f x * K (x + c))) B
        - (fun y => (∫ t in A..y, F (t - c) * h t)
        - ((∫ t in A..y, h t) * F (y - c) - ∫ x in (A - c)..(y - c), f x * K (x + c))) A :=
      integral_eq_sub_of_hasDerivAt_of_le hAB' hWcont hWderiv intervalIntegrable_const
    simp only [intervalIntegral.integral_zero] at hzero
    have hA : (∫ t in A..A, F (t - c) * h t)
        - ((∫ t in A..A, h t) * F (A - c) - ∫ x in (A - c)..(A - c), f x * K (x + c)) = 0 := by
      simp
    have hB : (∫ t in A..B, F (t - c) * h t)
        - ((∫ t in A..B, h t) * F (B - c) - ∫ x in (A - c)..(B - c), f x * K (x + c)) = 0 := by
      linarith [hzero, hA]
    linarith [hB]
  have goal_eq : (∫ t in A..B, (∫ x in (A - c)..(t - c), f x) * h t)
      = ∫ t in A..B, F (t - c) * h t := by
    apply intervalIntegral.integral_congr
    intro t _
    rw [hFdef]
  rw [goal_eq, key]
  have hFB : F (B - c) = ∫ s in (A - c)..(B - c), f s := by rw [hFdef]
  have hstep : ∀ x ∈ uIcc (A - c) (B - c), (∫ t in (x + c)..B, h t) = (∫ t in A..B, h t) - K (x + c) := by
    intro x hx
    rw [Set.uIcc_of_le hAc] at hx
    have hAx : A ≤ x + c := by linarith [hx.1]
    have hxB : x + c ≤ B := by linarith [hx.2]
    rw [hKdef]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hhi' (u := A) (v := x + c) le_rfl hAx hxB) (hhi' (u := x + c) (v := B) hAx hxB le_rfl)]
    ring
  have hFac : (∫ t in A..B, h t) * (∫ s in (A - c)..(B - c), f s)
      = ∫ x in (A - c)..(B - c), f x * (∫ t in A..B, h t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hexp : (∫ x in (A - c)..(B - c), f x * (∫ t in (x + c)..B, h t))
      = ∫ x in (A - c)..(B - c), (f x * (∫ t in A..B, h t) - f x * K (x + c)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    show f x * (∫ t in (x + c)..B, h t) = f x * (∫ t in A..B, h t) - f x * K (x + c)
    rw [hstep x hx]
    ring
  rw [hFB, hexp, intervalIntegral.integral_sub (hfi.mul_const _) hgi, hFac]

private lemma int_pow_sub (p q : ℝ) (k : ℕ) :
    (∫ x in p..q, (x - p) ^ k) = (q - p) ^ (k + 1) / (k + 1) := by
  have h := intervalIntegral.integral_comp_sub_right (a := p) (b := q) (fun y : ℝ => y ^ k) p
  rw [show p - p = 0 by ring] at h
  rw [h, integral_pow]
  ring

private lemma poly3_eq (p x : ℝ) (A B C : ℕ → ℝ) (na nb nc : ℕ) :
    (∑ i ∈ range na, A i * (x - p) ^ i) * (∑ j ∈ range nb, B j * (x - p) ^ j) *
        (∑ l ∈ range nc, C l * (x - p) ^ l)
      = ∑ l ∈ range nc, ∑ j ∈ range nb, ∑ i ∈ range na,
          A i * B j * C l * (x - p) ^ (i + j + l) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun i _ => ?_)))
  have h : (x - p) ^ (i + j + l) = (x - p) ^ i * (x - p) ^ j * (x - p) ^ l := by
    rw [pow_add, pow_add]
  rw [h]
  ring

private lemma int_prod3 (p q : ℝ) (hpq : p ≤ q) (A B C : ℕ → ℝ) (na nb nc : ℕ) :
    (∫ x in p..q, (∑ i ∈ range na, A i * (x - p) ^ i) * (∑ j ∈ range nb, B j * (x - p) ^ j) *
        (∑ l ∈ range nc, C l * (x - p) ^ l))
      = ∑ l ∈ range nc, ∑ j ∈ range nb, ∑ i ∈ range na,
          A i * B j * C l * ((q - p) ^ (i + j + l + 1) / (i + j + l + 1)) := by
  have hcongr : (∫ x in p..q, (∑ i ∈ range na, A i * (x - p) ^ i) *
      (∑ j ∈ range nb, B j * (x - p) ^ j) * (∑ l ∈ range nc, C l * (x - p) ^ l))
      = ∫ x in p..q, (∑ l ∈ range nc, ∑ j ∈ range nb, ∑ i ∈ range na,
          A i * B j * C l * (x - p) ^ (i + j + l)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact poly3_eq p x A B C na nb nc
  rw [hcongr, intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [intervalIntegral.integral_const_mul, int_pow_sub]
        push_cast
        ring
      · intro i _
        exact (by fun_prop : Continuous fun x : ℝ => A i * B j * C l * (x - p) ^ (i + j + l)).intervalIntegrable _ _
    · intro j _
      exact (by fun_prop : Continuous fun x : ℝ => ∑ i ∈ range na, A i * B j * C l * (x - p) ^ (i + j + l)).intervalIntegrable _ _
  · intro l _
    exact (by fun_prop : Continuous fun x : ℝ => ∑ j ∈ range nb, ∑ i ∈ range na,
      A i * B j * C l * (x - p) ^ (i + j + l)).intervalIntegrable _ _


/-! ### Three elementary estimates used for the positivity of the bounds -/

private lemma alt8_ge {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    u - u ^ 2 / 2 ≤ ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
  have hexp : (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1))
      = u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5 - u ^ 6 / 6 + u ^ 7 / 7 - u ^ 8 / 8 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  rw [hexp]
  have h3 : 0 ≤ u ^ 3 * (1 / 3 - u / 4) := mul_nonneg (pow_nonneg h0 3) (by linarith)
  have h5 : 0 ≤ u ^ 5 * (1 / 5 - u / 6) := mul_nonneg (pow_nonneg h0 5) (by linarith)
  have h7 : 0 ≤ u ^ 7 * (1 / 7 - u / 8) := mul_nonneg (pow_nonneg h0 7) (by linarith)
  nlinarith [h3, h5, h7]

private lemma two_u9_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : 2 * u ^ 9 ≤ u - u ^ 2 / 2 := by
  have h3 : 2 * u ^ 9 ≤ u / 128 := by
    have h2 : u ^ 8 ≤ (1 / 2 : ℝ) ^ 8 := pow_le_pow_left₀ h0 h1 8
    nlinarith [pow_nonneg h0 9]
  nlinarith

private lemma geom9_ge {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1 / 2) :
    1 / 2 ≤ ∑ l ∈ range 9, (-w) ^ l := by
  have hexp : (∑ l ∈ range 9, (-w) ^ l)
      = 1 - w + w ^ 2 - w ^ 3 + w ^ 4 - w ^ 5 + w ^ 6 - w ^ 7 + w ^ 8 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hexp]
  have hg : 1 - w + w ^ 2 - w ^ 3 + w ^ 4 - w ^ 5 + w ^ 6 - w ^ 7 + w ^ 8
      = (1 - w) * (1 + w ^ 2 + w ^ 4 + w ^ 6) + w ^ 8 := by ring
  rw [hg]
  have hpos : 0 ≤ (1 - w) * (1 + w ^ 2 + w ^ 4 + w ^ 6) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [pow_nonneg h0 8]

/-! ### The panel lower bound for `∫ log (x-1) log (5/(x+1)) / x` -/

private lemma P_panel_lower (p q : ℚ) (hp : 2 ≤ p) (hq : q ≤ 4) (hpq : p < q)
    (hsmall : q - p ≤ (p - 1) / 2) (hsmall2 : q - p ≤ p / 2)
    (lL lG : ℚ)
    (hlL : (lL : ℝ) ≤ Real.log ((p : ℝ) - 1)) (hlL0 : 0 ≤ (lL : ℝ))
    (hlG : (lG : ℝ) ≤ Real.log (5 / ((p : ℝ) + 1))) :
    (∑ l ∈ range 9, ∑ j ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lL else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else -2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j = 0 then lG else if j ≤ 8 then -((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j)
              else -2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p - ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j + l + 1) / ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)))
      ≤ ∫ x in (p : ℝ)..(q : ℝ), Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hQ4 : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hP1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hPQ : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hH0 : (0 : ℝ) ≤ (q : ℝ) - (p : ℝ) := by linarith
  have hs1 : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ (((p - 1) / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall
    push_cast at this ⊢
    linarith
  have hs2 : (q : ℝ) - (p : ℝ) ≤ (p : ℝ) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ ((p / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall2
    push_cast at this ⊢
    linarith
  set A : ℕ → ℝ := fun i => (((if i = 0 then lL else if i ≤ 8 then
      (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i) else -2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
    with hAdef
  set B : ℕ → ℝ := fun j => (((if j = 0 then lG else if j ≤ 8 then
      -((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j) else -2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ)
    with hBdef
  set C : ℕ → ℝ := fun l => (((if l = 0 then
      (1 : ℚ) / p - ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
      else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ) with hCdef
  have hrow : (∑ l ∈ range 9, ∑ j ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lL else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else -2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j = 0 then lG else if j ≤ 8 then -((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j)
              else -2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p - ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j + l + 1) / ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)))
      = ∑ l ∈ range 9, ∑ j ∈ range 10, ∑ i ∈ range 10,
          A i * B j * C l * (((q : ℝ) - (p : ℝ)) ^ (i + j + l + 1) / ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)) := by
    simp only [hAdef, hBdef, hCdef]
  rw [hrow, ← int_prod3 (p : ℝ) (q : ℝ) hPQ.le A B C 10 10 9]
  refine intervalIntegral.integral_mono_on hPQ.le ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ =>
      (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
        (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)).intervalIntegrable _ _
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hPQ.le]
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact ContinuousOn.log (by fun_prop) (fun x hx => by linarith [hx.1])
      · apply ContinuousOn.log ?_ (fun x hx =>
          ne_of_gt (div_pos (by norm_num) (by linarith [hx.1])))
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro x hx
        linarith [hx.1]
    · exact continuousOn_id
    · intro x hx
      change x ≠ 0
      linarith [hx.1]
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hxp, hxq⟩ := hx
    set t : ℝ := x - (p : ℝ) with htdef
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have htH : t ≤ (q : ℝ) - (p : ℝ) := by rw [htdef]; linarith
    have hP0' : (0 : ℝ) < (p : ℝ) := hP0
    have hPm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hPp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
    set u : ℝ := t / ((p : ℝ) - 1) with hudef
    set v : ℝ := t / ((p : ℝ) + 1) with hvdef
    set w : ℝ := t / (p : ℝ) with hwdef
    have hu0 : 0 ≤ u := div_nonneg ht0 hPm1.le
    have hu1 : u ≤ 1 / 2 := by
      rw [hudef, div_le_iff₀ hPm1]
      have hHle : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := hs1
      nlinarith
    have hv0 : 0 ≤ v := div_nonneg ht0 hPp1.le
    have hv1 : v ≤ 1 / 2 := by
      rw [hvdef, div_le_iff₀ hPp1]
      nlinarith [hs2, htH]
    have hw0 : 0 ≤ w := div_nonneg ht0 hP0.le
    have hw1 : w ≤ 1 / 2 := by
      rw [hwdef, div_le_iff₀ hP0]
      nlinarith [hs2, htH]
    have hu_pos : (0 : ℝ) < 1 + u := by linarith
    have hv_pos : (0 : ℝ) < 1 + v := by linarith
    -- the coefficient identities
    have eA0 : A 0 = (lL : ℝ) := by
      simp only [hAdef, ↓reduceIte]
    have eA9 : A 9 = -2 / ((p : ℝ) - 1) ^ 9 := by
      simp only [hAdef]
      rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
      push_cast
      ring
    have eB0 : B 0 = (lG : ℝ) := by
      simp only [hBdef, ↓reduceIte]
    have eB9 : B 9 = -2 / ((p : ℝ) + 1) ^ 9 := by
      simp only [hBdef]
      rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
      push_cast
      ring
    have hArow : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i)
        = (lL : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) - 2 * u ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ, eA0, eA9]
      have hmid : (∑ i ∈ range 8, A (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hAi : A (i + 1) = (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) - 1) ^ (i + 1) := by
          simp only [hAdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hAi]
        rw [show u ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) - 1) ^ (i + 1) from by
          rw [hudef, div_pow]]
        ring
      rw [hmid]
      rw [show -2 / ((p : ℝ) - 1) ^ 9 * (x - (p : ℝ)) ^ 9 = -(2 * u ^ 9) from by
        rw [show u ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) - 1) ^ 9 from by rw [hudef, div_pow]]
        field_simp]
      ring
    have hBrow : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
        = (lG : ℝ) - (∑ j ∈ range 8, (-1 : ℝ) ^ j * v ^ (j + 1) / (j + 1)) - 2 * v ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ, eB0, eB9]
      have hmid : (∑ j ∈ range 8, B (j + 1) * (x - (p : ℝ)) ^ (j + 1))
          = ∑ j ∈ range 8, -((-1 : ℝ) ^ j * v ^ (j + 1) / (j + 1)) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj8 : j + 1 ≤ 8 := by simpa using Finset.mem_range.mp hj
        have hBj : B (j + 1) = -((-1 : ℝ) ^ j) / ((j : ℝ) + 1) / ((p : ℝ) + 1) ^ (j + 1) := by
          simp only [hBdef]
          rw [if_neg (by omega : j + 1 ≠ 0), if_pos hj8]
          push_cast
          field_simp
        rw [hBj]
        rw [show v ^ (j + 1) = (x - (p : ℝ)) ^ (j + 1) / ((p : ℝ) + 1) ^ (j + 1) from by
          rw [hvdef, div_pow]]
        ring
      rw [hmid, Finset.sum_neg_distrib]
      rw [show -2 / ((p : ℝ) + 1) ^ 9 * (x - (p : ℝ)) ^ 9 = -(2 * v ^ 9) from by
        rw [show v ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) + 1) ^ 9 from by rw [hvdef, div_pow]]
        field_simp]
      ring
    have hCrow : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
        = (1 / (p : ℝ) - (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
          + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
      rw [Finset.sum_range_succ']
      have eC0 : C 0 = (1 / (p : ℝ) - (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
        simp only [hCdef]
        push_cast
        rw [mul_div_assoc]
      rw [eC0]
      have hmid : (∑ l ∈ range 8, C (l + 1) * (x - (p : ℝ)) ^ (l + 1))
          = (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have hCl : C (l + 1) = (-1 : ℝ) ^ (l + 1) / (p : ℝ) ^ (l + 2) := by
          simp only [hCdef]
          rw [if_neg (by omega : l + 1 ≠ 0)]
          push_cast
          field_simp
        rw [hCl]
        rw [show (-w) ^ (l + 1) = (-1 : ℝ) ^ (l + 1) * (x - (p : ℝ)) ^ (l + 1) / (p : ℝ) ^ (l + 1) from by
          rw [hwdef, show -(t / (p:ℝ)) = -((x - (p:ℝ)) / (p:ℝ)) from by rw [htdef], neg_pow, div_pow]
          ring]
        field_simp
        rw [pow_succ]
        ring
      rw [hmid]
      ring
    -- bounds for the three factors
    have hAle : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) ≤ Real.log (x - 1) := by
      rw [hArow]
      have hx1 : x - 1 = ((p : ℝ) - 1) * (1 + u) := by
        rw [show 1 + u = (x - 1) / ((p : ℝ) - 1) from by
          rw [hudef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_mul (by linarith) (by linarith)]
      have h := log_one_add_ge9 hu0 hu1
      have h1 := add_le_add hlL h
      calc (lL : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) - 2 * u ^ 9
          = (lL : ℝ) + ((∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) - 2 * u ^ 9) := by
            ring
        _ ≤ Real.log ((p : ℝ) - 1) + Real.log (1 + u) := h1
    have hBle : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) ≤ Real.log (5 / (x + 1)) := by
      rw [hBrow]
      have hx1 : 5 / (x + 1) = (5 / ((p : ℝ) + 1)) / (1 + v) := by
        rw [show 1 + v = (x + 1) / ((p : ℝ) + 1) from by
          rw [hvdef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_div (by positivity) (by linarith)]
      have h := log_one_add_le9 hv0 hv1
      calc (lG : ℝ) - (∑ j ∈ range 8, (-1 : ℝ) ^ j * v ^ (j + 1) / (j + 1)) - 2 * v ^ 9
          = (lG : ℝ) + (-(∑ j ∈ range 8, (-1 : ℝ) ^ j * v ^ (j + 1) / (j + 1)) - 2 * v ^ 9) := by
            ring
        _ ≤ Real.log (5 / ((p : ℝ) + 1)) + (-Real.log (1 + v)) := by linarith [h, hlG]
    have hCle : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≤ 1 / x := by
      rw [hCrow]
      have hsum : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := (inv_geom_bounds (p := (p : ℝ)) (h := (q : ℝ) - (p : ℝ)) hP0 hH0 hs2 8
        (t := t) ⟨ht0, htH⟩).1
      rw [show -(t / (p : ℝ)) = -w from by rw [hwdef]] at hg
      rw [show (p : ℝ) + t = x from by rw [htdef]; ring, hsum] at hg
      calc (1 / (p : ℝ) - (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 + ∑ l ∈ range 8, (-w) ^ (l + 1)) * (1 / (p : ℝ))
            - (1 / (p : ℝ)) * ((((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
            rw [show (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) = (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 from by norm_num]
            ring
        _ ≤ 1 / x := hg
    -- positivity of two of them
    have hA0 : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) := by
      rw [hArow]
      have h1 := alt8_ge hu0 hu1
      have h2 := two_u9_le hu0 hu1
      nlinarith [hlL0]
    have hC0 : 0 ≤ (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by
      rw [hCrow]
      have hsum9 : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := geom9_ge hw0 hw1
      rw [hsum9] at hg
      have hrat : (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 / (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)) ≤ 1 / 2 := by
        have h0 : 0 ≤ ((q : ℝ) - (p : ℝ)) / (p : ℝ) := div_nonneg hH0 hP0.le
        have h1 : ((q : ℝ) - (p : ℝ)) / (p : ℝ) ≤ 1 / 2 := by
          rw [div_le_iff₀ hP0]; linarith
        have h2 : (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 ≤ (1 / 2 : ℝ) ^ 9 :=
          pow_le_pow_left₀ h0 h1 9
        have h3 : (0 : ℝ) < 1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ) := by linarith
        rw [div_le_iff₀ h3]
        nlinarith [pow_nonneg h0 9]
      have hinv : (0 : ℝ) < 1 / (p : ℝ) := by positivity
      have hX1 : (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 / (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)) ≤ 1 := by
        linarith [hrat]
      have hS2 : -(1 / 2 : ℝ) ≤ ∑ l ∈ range 8, (-w) ^ (l + 1) := by linarith [hg]
      have e1 : (1 / (p : ℝ) - (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 / (p : ℝ)) * (1 - (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)) + ∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        ring
      rw [e1]
      apply mul_nonneg hinv.le
      linarith
    -- the product comparison
    have hf0 : 0 ≤ Real.log (x - 1) := Real.log_nonneg (by linarith)
    have hg0 : 0 ≤ Real.log (5 / (x + 1)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hxpos : (0 : ℝ) < x := by linarith
    by_cases hB : 0 ≤ (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
    · have h1 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
          (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          ≤ Real.log (x - 1) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) :=
        mul_le_mul_of_nonneg_right hAle hB
      have h2 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
            (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
          ≤ Real.log (x - 1) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
        mul_le_mul_of_nonneg_right h1 hC0
      have h3 : Real.log (x - 1) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          ≤ Real.log (x - 1) * Real.log (5 / (x + 1)) :=
        mul_le_mul_of_nonneg_left hBle hf0
      have h4 : Real.log (x - 1) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
          ≤ Real.log (x - 1) * Real.log (5 / (x + 1)) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
        mul_le_mul_of_nonneg_right h3 hC0
      have h5 : Real.log (x - 1) * Real.log (5 / (x + 1)) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
          ≤ Real.log (x - 1) * Real.log (5 / (x + 1)) * (1 / x) :=
        mul_le_mul_of_nonneg_left hCle (mul_nonneg hf0 hg0)
      have h6 : Real.log (x - 1) * Real.log (5 / (x + 1)) * (1 / x)
          = Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
        simp only [div_eq_mul_inv]
        ring
      linarith [h2, h4, h5]
    · have hBlt : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) < 0 := not_le.mp hB
      have hAC : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
          (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := mul_nonneg hA0 hC0
      have hzero : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
            (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≤ 0 := by
        nlinarith
      have hpos : 0 ≤ Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by positivity
      linarith

/-! ### The F0 leaf -/

private lemma logLowerQ_nonneg (N : ℕ) (y : ℚ) (hy : 1 ≤ y) :
    (0 : ℚ) ≤ 2 * ∑ j ∈ range N, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1) := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  apply div_nonneg
  · apply pow_nonneg
    apply div_nonneg <;> linarith
  · positivity

/-! ### Integrability and continuity of the inner primitive in `F0` -/

private lemma logquot_continuousOn :
    ContinuousOn (fun x : ℝ => Real.log (x - 1) / x) (Set.uIcc (2:ℝ) 4) := by
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
  apply ContinuousOn.div
  · apply ContinuousOn.log (by fun_prop)
    intro x hx; linarith [hx.1]
  · exact continuousOn_id
  · intro x hx; change x ≠ 0; linarith [hx.1]

private lemma logquot_integrable : IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume 2 4 :=
  logquot_continuousOn.intervalIntegrable

private lemma inner_cont :
    ContinuousOn (fun t : ℝ => ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) (Set.uIcc (4:ℝ) 6) := by
  have h := continuousOn_primitive_interval' logquot_integrable
    (Set.left_mem_uIcc (a := (2:ℝ)) (b := (4:ℝ)))
  refine h.comp (by fun_prop) ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 6)] at ht
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
  constructor <;> linarith [ht.1, ht.2]

private lemma inner_split_integrable :
    IntervalIntegrable (fun t : ℝ => (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) / (t - 1))
      volume 4 6 := by
  have hcont : ContinuousOn
      (fun t : ℝ => (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) / (t - 1)) (Set.uIcc 4 6) := by
    refine ContinuousOn.div inner_cont ?_ ?_
    · exact (by fun_prop : ContinuousOn (fun t : ℝ => t - 1) (Set.uIcc (4:ℝ) 6))
    · intro t ht
      rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 6)] at ht
      change t - 1 ≠ 0
      linarith [ht.1]
  exact hcont.intervalIntegrable

private lemma logP_continuousOn {u v : ℝ} (huv : u ≤ v) (hu : 2 ≤ u) :
    ContinuousOn (fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) (Set.uIcc u v) := by
  rw [Set.uIcc_of_le huv]
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · apply ContinuousOn.log (by fun_prop)
      intro x hx; linarith [hx.1]
    · apply ContinuousOn.log ?_ (fun x hx => ne_of_gt (div_pos (by norm_num) (by linarith [hx.1])))
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; linarith [hx.1]
  · exact continuousOn_id
  · intro x hx
    change x ≠ 0
    linarith [hx.1]

/-! ### The 16-panel lower bound for `∫_2^4 log (x-1) log (5/(x+1)) / x` -/

private lemma P_partition_lower :
    (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
      (((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i) : ℚ) : ℝ)
      * (((if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j') : ℚ) : ℝ)
      * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ)
      * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) /
          ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)))
    ≤ ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
  set a : ℕ → ℝ := fun j => ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) with hadef
  have ha0 : a 0 = 2 := by
    rw [hadef]; norm_num
  have ha16 : a 16 = 4 := by
    rw [hadef]; norm_num
  have hadj : ∀ j : ℕ, a (j + 1) - a j = 2 / 16 := by
    intro j
    rw [hadef]
    push_cast
    ring
  have hint : ∀ k < 16, IntervalIntegrable
      (fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) volume (a k) (a (k + 1)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ a k := by
      rw [hadef]
      push_cast
      have h : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hle : a k ≤ a (k + 1) := by
      rw [hadef]
      push_cast
      have h : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
      linarith
    exact (logP_continuousOn hle hk2).intervalIntegrable
  have hcell : ∀ j ∈ range 16,
      (∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then (2 * ∑ k ∈ range 20,
              (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
                (2 * k + 1))
            else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
            else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then (2 * ∑ k ∈ range 20,
              (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
                (2 * k + 1))
            else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
            else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
                ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                  ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                    (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
            else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) /
            ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)))
      ≤ ∫ x in a j..a (j + 1), Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
    intro j hj
    have hj16 : j < 16 := Finset.mem_range.mp hj
    have hj0 : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
    have hp2 : (2 : ℚ) ≤ 2 + 2 * (j : ℚ) / 16 := by
      have h : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
      linarith
    have hq4 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 ≤ 4 := by
      have hj1 : ((j + 1 : ℕ) : ℚ) ≤ 16 := by
        have h : j + 1 ≤ 16 := by omega
        exact_mod_cast h
      nlinarith
    have hpq : 2 + 2 * (j : ℚ) / 16 < 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 := by
      have h : (j : ℚ) < ((j + 1 : ℕ) : ℚ) := by
        have h' : j < j + 1 := by omega
        exact_mod_cast h'
      linarith
    have hsmall : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) ≤
        (2 + 2 * (j : ℚ) / 16 - 1) / 2 := by
      have h1 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) = 2 / 16 := by
        push_cast
        ring
      rw [h1]
      nlinarith
    have hsmall2 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) ≤
        (2 + 2 * (j : ℚ) / 16) / 2 := by
      have h1 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) = 2 / 16 := by
        push_cast
        ring
      rw [h1]
      nlinarith
    have hy1 : (1 : ℚ) ≤ 2 + 2 * (j : ℚ) / 16 - 1 := by
      have h : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
      linarith
    have hyL : (1 : ℝ) ≤ ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ) := by exact_mod_cast hy1
    have hy1G : (1 : ℚ) ≤ 5 / (2 + 2 * (j : ℚ) / 16 + 1) := by
      rw [le_div_iff₀ (by positivity)]
      have h : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
      linarith
    have hyG : (1 : ℝ) ≤ ((5 / (2 + 2 * (j : ℚ) / 16 + 1) : ℚ) : ℝ) := by exact_mod_cast hy1G
    have hlL : ((2 * ∑ k ∈ range 20,
          (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
            (2 * k + 1) : ℚ) : ℝ) ≤ Real.log (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) - 1) := by
      have hc := rat_logLower_cast' 20 (2 + 2 * (j : ℚ) / 16 - 1)
      have hb := (Wu04Integral.log_bounds 20 (y := ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ)) hyL).1
      have hcast : ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ) = ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) - 1 := by
        push_cast
        ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hlL0 : (0 : ℝ) ≤ ((2 * ∑ k ∈ range 20,
          (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
            (2 * k + 1) : ℚ) : ℝ) := by
      have h := logLowerQ_nonneg 20 (2 + 2 * (j : ℚ) / 16 - 1) hy1
      exact_mod_cast h
    have hlG : ((2 * ∑ k ∈ range 20,
          (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
            (2 * k + 1) : ℚ) : ℝ) ≤ Real.log (5 / (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) + 1)) := by
      have hc := rat_logLower_cast' 20 (5 / (2 + 2 * (j : ℚ) / 16 + 1))
      have hb := (Wu04Integral.log_bounds 20 (y := ((5 / (2 + 2 * (j : ℚ) / 16 + 1) : ℚ) : ℝ)) hyG).1
      have hcast : ((5 / (2 + 2 * (j : ℚ) / 16 + 1) : ℚ) : ℝ) =
          (5 : ℝ) / (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) + 1) := by
        push_cast
        ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hpanel := P_panel_lower (p := 2 + 2 * (j : ℚ) / 16)
      (q := 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16)
      (lL := 2 * ∑ k ∈ range 20,
        (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1))
      (lG := 2 * ∑ k ∈ range 20,
        (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1))
      hp2 hq4 hpq hsmall hsmall2 hlL hlL0 hlG
    have hcast2 : ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) = a j := by rw [hadef]
    have hcast3 : ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) = a (j + 1) := by
      rw [hadef]
    simpa only [hcast2, hcast3] using hpanel
  have hsum_int : (∑ j ∈ range 16, ∫ x in a j..a (j + 1),
      Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
      = ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
    have h := sum_integral_adjacent_intervals (a := a) (n := 16)
      (f := fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) hint
    rw [ha0, ha16] at h
    exact h
  rw [← hsum_int]
  exact Finset.sum_le_sum hcell

/-! ### The inner-integral identity of `F0` -/

private lemma one_div_sub_one_int :
    (∫ t in (4:ℝ)..6, 1 / (t - 1)) = Real.log (5 / 3) := by
  have h := intervalIntegral.integral_comp_sub_right (a := (4:ℝ)) (b := 6) (fun u : ℝ => (u)⁻¹) 1
  rw [show (4:ℝ) - 1 = 3 by norm_num, show (6:ℝ) - 1 = 5 by norm_num] at h
  rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num : (0:ℝ) < 5)] at h
  simpa only [one_div] using h

private lemma one_div_sub_one_integrable : IntervalIntegrable (fun t : ℝ => 1 / (t - 1)) volume 4 6 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 6)]
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro t ht
  change t - 1 ≠ 0
  linarith [ht.1]

private lemma weight_integral : ∀ x ∈ Set.uIcc (2:ℝ) 4,
    (∫ t in (x + 2)..6, 1 / (t - 1)) = Real.log (5 / (x + 1)) := by
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)] at hx
  have h := intervalIntegral.integral_comp_sub_right (a := x + 2) (b := 6) (fun u : ℝ => (u)⁻¹) 1
  rw [show x + 2 - 1 = x + 1 by ring, show (6:ℝ) - 1 = 5 by norm_num] at h
  rw [integral_inv_of_pos (by linarith [hx.1] : (0:ℝ) < x + 1) (by norm_num : (0:ℝ) < 5)] at h
  simpa only [one_div] using h

private lemma F0_inner_identity :
    (∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)))
      = Real.log (5 / 3) + ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
  have hint2 : IntervalIntegrable
      (fun t : ℝ => (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1))) volume 4 6 := by
    simpa only [div_eq_mul_inv, one_mul] using inner_split_integrable
  have hsplit : (∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)))
      = (∫ t in (4:ℝ)..6, 1 / (t - 1))
        + ∫ t in (4:ℝ)..6, (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)) := by
    rw [← intervalIntegral.integral_add one_div_sub_one_integrable hint2]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hswap := triangle_swap (f := fun x : ℝ => Real.log (x - 1) / x) (h := fun t : ℝ => 1 / (t - 1))
    (c := 2) (A := 4) (B := 6) (hc := by norm_num) (hAB := by norm_num)
    (hf := by
      rw [show (4:ℝ) - 2 = 2 by norm_num, show (6:ℝ) - 2 = 4 by norm_num]
      exact logquot_continuousOn)
    (hh := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 6)] at ht
      change t - 1 ≠ 0
      linarith [ht.1])
  simp only [show (4:ℝ) - 2 = 2 by norm_num, show (6:ℝ) - 2 = 4 by norm_num] at hswap
  calc (∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)))
      = (∫ t in (4:ℝ)..6, 1 / (t - 1))
        + ∫ t in (4:ℝ)..6, (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)) := hsplit
    _ = Real.log (5 / 3)
        + ∫ t in (4:ℝ)..6, (∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)) := by
        rw [one_div_sub_one_int]
    _ = Real.log (5 / 3) + ∫ x in (2:ℝ)..4,
          Real.log (x - 1) / x * (∫ t in (x + 2)..6, 1 / (t - 1)) := by
        rw [hswap]
    _ = Real.log (5 / 3) + ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x hx
        change Real.log (x - 1) / x * (∫ t in (x + 2)..6, 1 / (t - 1))
          = Real.log (x - 1) * Real.log (5 / (x + 1)) / x
        rw [weight_integral x hx]
        ring

private theorem certQ :
    (13473613 / 1000000 : ℚ) ≤ 8 * ((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + (2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1))) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) := by
  decide +kernel

private lemma certQR :
    ((13473613 / 1000000 : ℚ) : ℝ) ≤ ((8 * ((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + (2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1))) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) : ℚ) : ℝ) := by
  exact_mod_cast certQ

private lemma castsplit :
    ((8 * ((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + (2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1))) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) : ℚ) : ℝ) =
      8 * (((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) : ℚ) : ℝ) + 8 * (((2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) : ℚ) : ℝ)
      + 8 * (((∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) : ℚ) : ℝ) := by
  push_cast
  ring

private lemma castsum :
    (((∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, ((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
      * (if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
      * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1))
      * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) - (2 + 2 * (j : ℚ) / 16 : ℚ)) ^ (i + j' + l + 1) /
          ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) : ℚ) : ℝ) =
      (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
      (((if i = 0 then (2 * ∑ k ∈ range 20,
            (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i)
          else -2 / ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ)) ^ i) : ℚ) : ℝ)
      * (((if j' = 0 then (2 * ∑ k ∈ range 20,
            (((5 / (2 + 2 * (j : ℚ) / 16 + 1)) - 1) / ((5 / (2 + 2 * (j : ℚ) / 16 + 1)) + 1)) ^ (2 * k + 1) /
              (2 * k + 1))
          else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j')
          else -2 / ((2 + 2 * (j : ℚ) / 16 + 1 : ℚ)) ^ j') : ℚ) : ℝ)
      * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) -
              ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) *
                ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 /
                  (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)))
          else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ)
      * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) /
          ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1))) := by
  push_cast
  ring

/-- LEAF. Wu 2004 page 42 final numerical display, F0.
The single actual integral coefficient satisfies its printed lower bound. -/
theorem numerical_F0 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    13.473613 ≤ integralTerms F f ω 0 := by

  have hF0 := Task275.F0_elementary (F := F) (f := f) h ω
  rw [hF0]
  have hform : (∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 1 - 1), Real.log (x - 1) / x) / (t - 1))
      = ∫ t in (4:ℝ)..6, (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1)) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    show (1 + ∫ x in (2:ℝ)..(t - 1 - 1), Real.log (x - 1) / x) / (t - 1)
      = (1 + ∫ x in (2:ℝ)..(t - 2), Real.log (x - 1) / x) * (1 / (t - 1))
    rw [show (t - 1 - 1 : ℝ) = t - 2 by ring]
    ring
  rw [hform, F0_inner_identity]
  -- logarithm bounds for the two constants
  have h3 : (((2 * ∑ k ∈ range 20, (((3 : ℚ) - 1) / ((3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) : ℚ) : ℝ)
      ≤ Real.log 3 := by
    have hc := rat_logLower_cast' 20 (3 : ℚ)
    have hb := (Wu04Integral.log_bounds 20 (y := ((3 : ℚ) : ℝ)) (by norm_num)).1
    have hcast : ((3 : ℚ) : ℝ) = (3 : ℝ) := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have h53 : (((2 * ∑ k ∈ range 20, (((5 / 3 : ℚ) - 1) / ((5 / 3 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) : ℚ) : ℝ)
      ≤ Real.log (5 / 3) := by
    have hc := rat_logLower_cast' 20 (5 / 3 : ℚ)
    have hb := (Wu04Integral.log_bounds 20 (y := ((5 / 3 : ℚ) : ℝ)) (by norm_num)).1
    have hcast : ((5 / 3 : ℚ) : ℝ) = (5 : ℝ) / 3 := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  -- assemble: the certificate cast to the reals, then the panel bound
  have hc := certQR
  rw [castsplit, castsum] at hc
  have hP := P_partition_lower
  have hmain : ((13473613 / 1000000 : ℚ) : ℝ) ≤
      8 * (Real.log 3 + (Real.log (5 / 3) + ∫ x in (2:ℝ)..4,
        Real.log (x - 1) * Real.log (5 / (x + 1)) / x)) := by
    nlinarith [hc, h3, h53, hP]
  calc (13.473613 : ℝ) = ((13473613 / 1000000 : ℚ) : ℝ) := by norm_num
    _ ≤ 8 * (Real.log 3 + (Real.log (5 / 3) + ∫ x in (2:ℝ)..4,
        Real.log (x - 1) * Real.log (5 / (x + 1)) / x)) := hmain

private lemma tail_weight_cont : ContinuousOn (fun t : ℝ => 1 / (t * (1 - t / 6))) (Set.uIcc (3:ℝ) 5) := by
  rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)]
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro t ht
    have h1 : t ≠ 0 := by linarith [ht.1]
    have h2 : (1 : ℝ) - t / 6 ≠ 0 := by linarith [ht.2]
    exact mul_ne_zero h1 h2

private lemma split_one_div {t : ℝ} (ht : t ≠ 0) (h6 : 6 - t ≠ 0) :
    1 / (t * (1 - t / 6)) = 1 / t + 1 / (6 - t) := by
  have h1 : (1 : ℝ) - t / 6 ≠ 0 := by
    intro hc
    apply h6
    field_simp at hc
    linarith
  rw [show t * (1 - t / 6) = t * (6 - t) / 6 by ring]
  field_simp
  ring

private lemma tail_weight_int : (∫ t in (3:ℝ)..5, 1 / (t * (1 - t / 6))) = Real.log 5 := by
  have he : (∫ t in (3:ℝ)..5, 1 / (t * (1 - t / 6)))
      = ∫ t in (3:ℝ)..5, (1 / t + 1 / (6 - t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)] at ht
    exact split_one_div (by linarith [ht.1]) (by linarith [ht.2])
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / t) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; change t ≠ 0; linarith [ht.1]
  have hi2 : IntervalIntegrable (fun t : ℝ => 1 / (6 - t)) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; change 6 - t ≠ 0; linarith [ht.2]
  rw [he, intervalIntegral.integral_add hi1 hi2]
  have h1 : (∫ t in (3:ℝ)..5, 1 / t) = Real.log (5 / 3) := by
    rw [show (∫ t in (3:ℝ)..5, 1 / t) = ∫ t in (3:ℝ)..5, (t)⁻¹ from by
      apply intervalIntegral.integral_congr; intro t _; rw [one_div]]
    rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num : (0:ℝ) < 5)]
  have h2 : (∫ t in (3:ℝ)..5, 1 / (6 - t)) = Real.log 3 := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun u : ℝ => (u)⁻¹) 6
      (a := (3:ℝ)) (b := 5)
    rw [show (6:ℝ) - 5 = 1 by norm_num, show (6:ℝ) - 3 = 3 by norm_num] at hcomp
    rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 3)] at hcomp
    rw [show (∫ t in (3:ℝ)..5, 1 / (6 - t)) = ∫ t in (3:ℝ)..5, ((fun u : ℝ => (u)⁻¹) (6 - t)) from by
      apply intervalIntegral.integral_congr; intro t _; simp only [one_div]]
    rw [hcomp]
    norm_num
  rw [h1, h2]
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

private lemma tail_weight_point : ∀ x ∈ Set.uIcc (2:ℝ) 4,
    (∫ t in (x + 1)..5, 1 / (t * (1 - t / 6))) = Real.log (5 * (5 - x) / (x + 1)) := by
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)] at hx
  have hx1 : (0:ℝ) < x + 1 := by linarith [hx.1]
  have hx5 : (0:ℝ) < 5 - x := by linarith [hx.2]
  have hupper : x + 1 ≤ 5 := by linarith [hx.2]
  have he : (∫ t in (x + 1)..5, 1 / (t * (1 - t / 6)))
      = ∫ t in (x + 1)..5, (1 / t + 1 / (6 - t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hupper] at ht
    exact split_one_div (by linarith [ht.1]) (by linarith [ht.2])
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (x + 1) 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hupper]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; change t ≠ 0; linarith [ht.1]
  have hi2 : IntervalIntegrable (fun t : ℝ => 1 / (6 - t)) volume (x + 1) 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hupper]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; change 6 - t ≠ 0; linarith [ht.2]
  rw [he, intervalIntegral.integral_add hi1 hi2]
  have h1 : (∫ t in (x + 1)..5, 1 / t) = Real.log (5 / (x + 1)) := by
    rw [show (∫ t in (x + 1)..5, 1 / t) = ∫ t in (x + 1)..5, (t)⁻¹ from by
      apply intervalIntegral.integral_congr; intro t _; rw [one_div]]
    rw [integral_inv_of_pos hx1 (by norm_num : (0:ℝ) < 5)]
  have h2 : (∫ t in (x + 1)..5, 1 / (6 - t)) = Real.log (5 - x) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun u : ℝ => (u)⁻¹) 6
      (a := x + 1) (b := 5)
    rw [show (6:ℝ) - 5 = 1 by norm_num, show (6:ℝ) - (x + 1) = 5 - x by ring] at hcomp
    rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 1) hx5] at hcomp
    rw [show (∫ t in (x + 1)..5, 1 / (6 - t)) = ∫ t in (x + 1)..5, ((fun u : ℝ => (u)⁻¹) (6 - t)) from by
      apply intervalIntegral.integral_congr; intro t _; simp only [one_div]]
    rw [hcomp]
    rw [show (5 - x) / 1 = 5 - x by norm_num]
  rw [h1, h2]
  rw [← Real.log_mul (by positivity) hx5.ne']
  congr 1
  field_simp

private lemma inner_cont3 :
    ContinuousOn (fun t : ℝ => ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) (Set.uIcc (3:ℝ) 5) := by
  have h := continuousOn_primitive_interval' logquot_integrable
    (Set.left_mem_uIcc (a := (2:ℝ)) (b := (4:ℝ)))
  refine h.comp (by fun_prop) ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)] at ht
  rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
  constructor <;> linarith [ht.1, ht.2]

private lemma F3_inner_identity :
    (∫ t in (3:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / (t * (1 - t / 6))))
      = Real.log 5 + ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x := by
  have hint2 : IntervalIntegrable
      (fun t : ℝ => (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / (t * (1 - t / 6))))
      volume 3 5 := by
    have hcont : ContinuousOn
        (fun t : ℝ => (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / (t * (1 - t / 6))))
        (Set.uIcc (3:ℝ) 5) := by
      refine ContinuousOn.mul inner_cont3 ?_
      exact (tail_weight_cont.mono (by intro t ht; exact ht))
    exact hcont.intervalIntegrable
  have hsplit : (∫ t in (3:ℝ)..5,
        (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / (t * (1 - t / 6))))
      = (∫ t in (3:ℝ)..5, 1 / (t * (1 - t / 6)))
        + ∫ t in (3:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
            (1 / (t * (1 - t / 6))) := by
    rw [← intervalIntegral.integral_add tail_weight_cont.intervalIntegrable hint2]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hswap := triangle_swap (f := fun x : ℝ => Real.log (x - 1) / x)
    (h := fun t : ℝ => 1 / (t * (1 - t / 6))) (c := 1) (A := 3) (B := 5)
    (hc := by norm_num) (hAB := by norm_num)
    (hf := by
      rw [show (3:ℝ) - 1 = 2 by norm_num, show (5:ℝ) - 1 = 4 by norm_num]
      exact logquot_continuousOn)
    (hh := by
      rw [show (3:ℝ) = 3 by norm_num]
      exact tail_weight_cont)
  simp only [show (3:ℝ) - 1 = 2 by norm_num, show (5:ℝ) - 1 = 4 by norm_num] at hswap
  calc (∫ t in (3:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
        (1 / (t * (1 - t / 6))))
      = (∫ t in (3:ℝ)..5, 1 / (t * (1 - t / 6)))
        + ∫ t in (3:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
            (1 / (t * (1 - t / 6))) := hsplit
    _ = Real.log 5 + ∫ t in (3:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
            (1 / (t * (1 - t / 6))) := by rw [tail_weight_int]
    _ = Real.log 5 + ∫ x in (2:ℝ)..4,
          Real.log (x - 1) / x * (∫ t in (x + 1)..5, 1 / (t * (1 - t / 6))) := by
        rw [hswap]
    _ = Real.log 5 + ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x hx
        change Real.log (x - 1) / x * (∫ t in (x + 1)..5, 1 / (t * (1 - t / 6)))
          = Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x
        rw [tail_weight_point x hx]
        ring

private lemma logQD_continuousOn {u v : ℝ} (huv : u ≤ v) (hu : 2 ≤ u) (hv : v ≤ 4) :
    ContinuousOn (fun x : ℝ => Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      (Set.uIcc u v) := by
  rw [Set.uIcc_of_le huv]
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · apply ContinuousOn.log (by fun_prop)
      intro x hx; linarith [hx.1]
    · apply ContinuousOn.log ?_ (fun x hx => ne_of_gt (div_pos (by nlinarith [hx.2]) (by linarith [hx.1])))
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro x hx; linarith [hx.1]
  · exact continuousOn_id
  · intro x hx
    change x ≠ 0
    linarith [hx.1]

/-! ### The panel upper bound for `∫ log (x-1) log (5(5-x)/(x+1)) / x` -/

private lemma Q_panel_upper (p q : ℚ) (hp : 2 ≤ p) (hq : q ≤ 4) (hpq : p < q)
    (hsmall : q - p ≤ (p - 1) / 2) (hsmall2 : q - p ≤ p / 2)
    (lU gU : ℚ)
    (hlU : Real.log ((p : ℝ) - 1) ≤ (lU : ℝ))
    (hlG : Real.log (5 * (5 - (p : ℝ)) / ((p : ℝ) + 1)) ≤ (gU : ℝ)) :
    (∫ x in (p : ℝ)..(q : ℝ),
        Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      ≤ ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then gU else if j' ≤ 8 then
              -((1 : ℚ) / ((j' : ℚ) * ((5 - p : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((p + 1 : ℚ)) ^ j')
              else 2 / ((5 - p : ℚ)) ^ j' + 2 / ((p + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hP1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hPQ : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hQ4 : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hs1 : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ (((p - 1) / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall
    push_cast at this ⊢
    linarith
  have hs2 : (q : ℝ) - (p : ℝ) ≤ (p : ℝ) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ ((p / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall2
    push_cast at this ⊢
    linarith
  set A : ℕ → ℝ := fun i => (((if i = 0 then lU else if i ≤ 8 then
      (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i) else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
    with hAdef
  set B : ℕ → ℝ := fun j => (((if j = 0 then gU else if j ≤ 8 then
      -((1 : ℚ) / ((j : ℚ) * ((5 - p : ℚ)) ^ j)) - ((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j)
      else 2 / ((5 - p : ℚ)) ^ j + 2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ) with hBdef
  set C : ℕ → ℝ := fun l => (((if l = 0 then
      (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
      else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ) with hCdef
  have hrow : (∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then gU else if j' ≤ 8 then
              -((1 : ℚ) / ((j' : ℚ) * ((5 - p : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((p + 1 : ℚ)) ^ j')
              else 2 / ((5 - p : ℚ)) ^ j' + 2 / ((p + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)))
      = ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
          A i * B j' * C l * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    simp only [hAdef, hBdef, hCdef]
  rw [hrow, ← int_prod3 (p : ℝ) (q : ℝ) hPQ.le A B C 10 10 9]
  refine intervalIntegral.integral_mono_on hPQ.le ?_ ?_ ?_
  · exact (logQD_continuousOn hPQ.le hp2 hQ4).intervalIntegrable
  · refine (by fun_prop : Continuous fun x : ℝ =>
      (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j' ∈ range 10, B j' * (x - (p : ℝ)) ^ j') *
        (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)).intervalIntegrable _ _
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hxp, hxq⟩ := hx
    set t : ℝ := x - (p : ℝ) with htdef
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have htH : t ≤ (q : ℝ) - (p : ℝ) := by rw [htdef]; linarith
    have hPm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hPp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
    have h5p : (0 : ℝ) < 5 - (p : ℝ) := by linarith
    set u : ℝ := t / ((p : ℝ) - 1) with hudef
    set v : ℝ := t / ((p : ℝ) + 1) with hvdef
    set sm : ℝ := t / (5 - (p : ℝ)) with hsdef
    set w : ℝ := t / (p : ℝ) with hwdef
    have hu0 : 0 ≤ u := div_nonneg ht0 hPm1.le
    have hu1 : u ≤ 1 / 2 := by
      rw [hudef, div_le_iff₀ hPm1]; nlinarith [hs1, htH]
    have hv0 : 0 ≤ v := div_nonneg ht0 hPp1.le
    have hv1 : v ≤ 1 / 2 := by
      rw [hvdef, div_le_iff₀ hPp1]; nlinarith [hs2, htH]
    have hs0 : 0 ≤ sm := div_nonneg ht0 h5p.le
    have hs1' : sm ≤ 1 / 2 := by
      rw [hsdef, div_le_iff₀ h5p]; nlinarith [htH]
    have hw0 : 0 ≤ w := div_nonneg ht0 hP0.le
    have hw1 : w ≤ 1 / 2 := by
      rw [hwdef, div_le_iff₀ hP0]; nlinarith [hs2, htH]
    -- coefficient identities
    have hArow : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i)
        = (lU : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) + 2 * u ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : A 0 = (lU : ℝ) := by simp only [hAdef, ↓reduceIte]
      have e9 : A 9 = 2 / ((p : ℝ) - 1) ^ 9 := by
        simp only [hAdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, A (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hAi : A (i + 1) = (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) - 1) ^ (i + 1) := by
          simp only [hAdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hAi]
        rw [show u ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) - 1) ^ (i + 1) from by
          rw [hudef, div_pow]]
        ring
      rw [hmid]
      rw [show 2 / ((p : ℝ) - 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * u ^ 9 from by
        rw [show u ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) - 1) ^ 9 from by rw [hudef, div_pow]]
        field_simp]
      ring
    have hBrow : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
        = (gU : ℝ) - (∑ i ∈ range 8, sm ^ (i + 1) / (i + 1))
          - (∑ i ∈ range 8, (-1 : ℝ) ^ i * v ^ (i + 1) / (i + 1)) + 2 * sm ^ 9 + 2 * v ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : B 0 = (gU : ℝ) := by simp only [hBdef, ↓reduceIte]
      have e9 : B 9 = 2 / (5 - (p : ℝ)) ^ 9 + 2 / ((p : ℝ) + 1) ^ 9 := by
        simp only [hBdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, B (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-(sm ^ (i + 1) / (i + 1)) - (-1 : ℝ) ^ i * v ^ (i + 1) / (i + 1)) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hBi : B (i + 1) = -(1 / ((i : ℝ) + 1)) / (5 - (p : ℝ)) ^ (i + 1)
            - (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) + 1) ^ (i + 1) := by
          simp only [hBdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hBi]
        rw [show sm ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / (5 - (p : ℝ)) ^ (i + 1) from by
          rw [hsdef, div_pow]]
        rw [show v ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) + 1) ^ (i + 1) from by
          rw [hvdef, div_pow]]
        ring
      rw [hmid, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      have h2a : 2 / (5 - (p : ℝ)) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * sm ^ 9 := by
        rw [hsdef, div_pow]
        ring
      have h2b : 2 / ((p : ℝ) + 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * v ^ 9 := by
        rw [hvdef, div_pow]
        ring
      have h2ab : (2 / (5 - (p : ℝ)) ^ 9 + 2 / ((p : ℝ) + 1) ^ 9) * (x - (p : ℝ)) ^ (8 + 1)
          = 2 * sm ^ 9 + 2 * v ^ 9 := by
        rw [show (8:ℕ) + 1 = 9 by norm_num, add_mul, h2a, h2b]
      rw [h2ab]
      ring
    have hCrow : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
        = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
          + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
      rw [Finset.sum_range_succ']
      have eC0 : C 0 = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
        simp only [hCdef, ↓reduceIte]
        push_cast
        ring
      rw [eC0]
      have hmid : (∑ l ∈ range 8, C (l + 1) * (x - (p : ℝ)) ^ (l + 1))
          = (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have hCl : C (l + 1) = (-1 : ℝ) ^ (l + 1) / (p : ℝ) ^ (l + 2) := by
          simp only [hCdef]
          rw [if_neg (by omega : l + 1 ≠ 0)]
          push_cast
          field_simp
        rw [hCl]
        rw [show (-w) ^ (l + 1) = (-1 : ℝ) ^ (l + 1) * (x - (p : ℝ)) ^ (l + 1) / (p : ℝ) ^ (l + 1) from by
          rw [hwdef, show -(t / (p:ℝ)) = -((x - (p:ℝ)) / (p:ℝ)) from by rw [htdef], neg_pow, div_pow]
          ring]
        field_simp
        rw [pow_succ]
        ring
      rw [hmid]
      ring
    -- the three lower bounds on the true factors
    have hAle : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) ≥ Real.log (x - 1) := by
      rw [hArow]
      have hx1 : x - 1 = ((p : ℝ) - 1) * (1 + u) := by
        rw [show 1 + u = (x - 1) / ((p : ℝ) - 1) from by
          rw [hudef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_mul (by linarith) (by linarith)]
      have h := log_one_add_le9 hu0 hu1
      linarith
    have hBle : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) ≥ Real.log (5 * (5 - x) / (x + 1)) := by
      rw [hBrow]
      have h1m : 1 - sm = (5 - x) / (5 - (p : ℝ)) := by
        rw [hsdef]
        field_simp
        ring
      have h1p : 1 + v = (x + 1) / ((p : ℝ) + 1) := by
        rw [hvdef]
        field_simp
        ring
      have hsplit : 5 * (5 - x) / (x + 1)
          = (5 * (5 - (p : ℝ)) / ((p : ℝ) + 1)) * ((1 - sm) / (1 + v)) := by
        rw [h1m, h1p]
        field_simp
      have hpos5 : (0 : ℝ) < 5 * (5 - (p : ℝ)) / ((p : ℝ) + 1) := by
        apply div_pos (by nlinarith) (by linarith)
      have h1s : (0 : ℝ) < 1 - sm := by linarith
      have h1v : (0 : ℝ) < 1 + v := by linarith
      have hdiv : (0 : ℝ) < (1 - sm) / (1 + v) := div_pos h1s h1v
      rw [hsplit, Real.log_mul hpos5.ne' hdiv.ne', Real.log_div h1s.ne' h1v.ne']
      have h1 := log_one_sub_le (s := sm) hs0 hs1' 8
      rw [show (8 : ℕ) + 1 = 9 from rfl] at h1
      have h2 := log_one_add_le9 hv0 hv1
      have h3 := log_one_add_ge9 hv0 hv1
      linarith [hlG, h1, h2, h3]
    have hCle : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≥ 1 / x := by
      rw [hCrow]
      have hsum : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := (inv_geom_bounds (p := (p : ℝ)) (h := (q : ℝ) - (p : ℝ)) hP0 (by linarith) hs2 8
        (t := t) ⟨ht0, htH⟩).2
      rw [show -(t / (p : ℝ)) = -w from by rw [hwdef]] at hg
      rw [show (p : ℝ) + t = x from by rw [htdef]; ring, hsum] at hg
      calc (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 + ∑ l ∈ range 8, (-w) ^ (l + 1)) * (1 / (p : ℝ))
            + (1 / (p : ℝ)) * ((((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
            rw [show (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) = (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 from by norm_num]
            ring
        _ ≥ 1 / x := hg
    -- nonnegativity
    have hf0 : 0 ≤ Real.log (x - 1) := Real.log_nonneg (by linarith)
    have hg0 : 0 ≤ Real.log (5 * (5 - x) / (x + 1)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have hA0 : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) := hf0.trans hAle
    have hB0 : 0 ≤ (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) := hg0.trans hBle
    have hC0 : 0 ≤ (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by
      have hx0 : (0:ℝ) < x := by linarith
      have : (0:ℝ) < 1 / x := by exact div_pos one_pos hx0
      linarith [hCle]
    have hxpos : (0 : ℝ) < x := by linarith
    -- the product comparison
    have h1 : Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1))
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 * (5 - x) / (x + 1)) :=
      mul_le_mul_of_nonneg_right hAle hg0
    have h2 : Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1))
          * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 * (5 - x) / (x + 1))
          * (1 / x) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 * (5 - x) / (x + 1))
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) :=
      mul_le_mul_of_nonneg_left hBle hA0
    have h4 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 * (5 - x) / (x + 1))
          * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (1 / x) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have h5 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
      mul_le_mul_of_nonneg_left hCle (mul_nonneg hA0 hB0)
    have h6 : Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x
        = Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) * (1 / x) := by
      simp only [div_eq_mul_inv]
      ring
    rw [h6]
    linarith [h2, h4, h5]


private lemma logQD_upper_bounds (j : ℕ) :
    Real.log ((2 + 2 * (j : ℚ) / 16 : ℚ) - 1 : ℝ) ≤
      ((2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2) : ℚ) : ℝ) := by
  have hc := rat_logUpper_cast 20 (2 + 2 * (j : ℚ) / 16 - 1)
  have hb := (Wu04Integral.log_bounds 20 (y := ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ))
    (by
      have h : (1 : ℚ) ≤ 2 + 2 * (j : ℚ) / 16 - 1 := by
        have h0 : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
        linarith
      exact_mod_cast h)).2
  have hcast : ((2 + 2 * (j : ℚ) / 16 - 1 : ℚ) : ℝ) = ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) - 1 := by
    push_cast
    ring
  rw [hcast] at hc hb
  linarith [hc, hb]

private lemma Q_partition_upper :
    (∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      ≤ ∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  set a : ℕ → ℝ := fun j => ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) with hadef
  have ha0 : a 0 = 2 := by rw [hadef]; norm_num
  have ha16 : a 16 = 4 := by rw [hadef]; norm_num
  have hint : ∀ k < 16, IntervalIntegrable
      (fun x : ℝ => Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x) volume (a k) (a (k + 1)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ a k := by
      rw [hadef]; push_cast
      have h : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hle : a k ≤ a (k + 1) := by
      rw [hadef]; push_cast
      have h : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
      linarith
    have hk4 : a (k + 1) ≤ 4 := by
      rw [hadef]; push_cast
      have hk16 : (k : ℝ) + 1 ≤ 16 := by
        have : k + 1 ≤ 16 := by omega
        exact_mod_cast this
      linarith
    exact (logQD_continuousOn hle hk2 hk4).intervalIntegrable
  have hcell : ∀ j ∈ range 16,
      (∫ x in a j..a (j + 1), Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
        ≤ ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    intro j hj
    have hj16 : j < 16 := Finset.mem_range.mp hj
    have hp2 : (2 : ℚ) ≤ 2 + 2 * (j : ℚ) / 16 := by
      have h : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
      linarith
    have hq4 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 ≤ 4 := by
      have hj1 : ((j + 1 : ℕ) : ℚ) ≤ 16 := by
        have h : j + 1 ≤ 16 := by omega
        exact_mod_cast h
      nlinarith
    have hpq : 2 + 2 * (j : ℚ) / 16 < 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 := by
      have h : (j : ℚ) < ((j + 1 : ℕ) : ℚ) := by
        have h' : j < j + 1 := by omega
        exact_mod_cast h'
      linarith
    have hsmall : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) ≤
        (2 + 2 * (j : ℚ) / 16 - 1) / 2 := by
      have h1 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) = 2 / 16 := by
        push_cast; ring
      rw [h1]; nlinarith
    have hsmall2 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) ≤
        (2 + 2 * (j : ℚ) / 16) / 2 := by
      have h1 : 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 - (2 + 2 * (j : ℚ) / 16) = 2 / 16 := by
        push_cast; ring
      rw [h1]; nlinarith
    have hlU : Real.log ((2 + 2 * (j : ℚ) / 16 : ℚ) - 1 : ℝ) ≤ ((2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2) : ℚ) : ℝ) :=
      logQD_upper_bounds j
    have hlG : Real.log (5 * (5 - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) / (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) + 1))
        ≤ ((2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2) : ℚ) : ℝ) := by
      have hc := rat_logUpper_cast 20 (5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1))
      have hy1 : (1 : ℚ) ≤ 5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1) := by
        rw [le_div_iff₀ (by positivity)]
        have h0 : 0 ≤ 2 * (j : ℚ) / 16 := by positivity
        nlinarith
      have hb := (Wu04Integral.log_bounds 20
        (y := ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1) : ℚ) : ℝ))
        (by exact_mod_cast hy1)).2
      have hcast : ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1) : ℚ) : ℝ)
          = 5 * (5 - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) / (((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) + 1) := by
        push_cast
        ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hpanel := Q_panel_upper (p := 2 + 2 * (j : ℚ) / 16)
      (q := 2 + 2 * ((j + 1 : ℕ) : ℚ) / 16)
      (lU := 2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2))
      (gU := 2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) hp2 hq4 hpq hsmall hsmall2 hlU hlG
    have hcast2 : ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ) = a j := by rw [hadef]
    have hcast3 : ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) = a (j + 1) := by rw [hadef]
    simpa only [hcast2, hcast3] using hpanel
  have hsum_int : (∑ j ∈ range 16, ∫ x in a j..a (j + 1),
      Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      = ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x := by
    have h := sum_integral_adjacent_intervals (a := a) (n := 16)
      (f := fun x : ℝ => Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x) hint
    rw [ha0, ha16] at h
    exact h
  rw [← hsum_int]
  exact Finset.sum_le_sum hcell

private theorem certQ3 :
    8 * ((2 * (∑ k ∈ range 26, ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 53 / (1 - ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 2) : ℚ) + (2 * (∑ k ∈ range 26, (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 53 / (1 - (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 2) : ℚ)) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))
      ≤ 17327241 / 1000000 := by
  decide +kernel

private lemma certQ3R :
    8 * ((2 * (∑ k ∈ range 26, ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 53 / (1 - ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 2) : ℚ) + (2 * (∑ k ∈ range 26, (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 53 / (1 - (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 2) : ℚ)) + 8 * (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))
      ≤ ((17327241 / 1000000 : ℚ) : ℝ) := by
  have h := certQ3
  exact_mod_cast h

private lemma castsumQ : ((∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) * (((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)) : ℚ) : ℝ) = ∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((2 + 2 * (j : ℚ) / 16 - 1) - 1) / ((2 + 2 * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((2 + 2 * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 41 / (1 - (((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) - 1) / ((5 * (5 - (2 + 2 * (j : ℚ) / 16)) / ((2 + 2 * (j : ℚ) / 16) + 1)) + 1)) ^ 2)) else if j' ≤ 8 then -(1 / ((j' : ℚ) * (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j')) - ((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((5 - (2 + 2 * (j : ℚ) / 16)) : ℚ)) ^ j' + 2 / (((2 + 2 * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + 2 * (j : ℚ) / 16) + ((1 : ℚ) / (2 + 2 * (j : ℚ) / 16)) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16)) ^ 9 / (1 - ((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16) - (2 + 2 * (j : ℚ) / 16)) / (2 + 2 * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / ((2 + 2 * (j : ℚ) / 16) : ℚ) ^ (l + 1)) : ℚ) : ℝ) * ((((2 + 2 * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) - ((2 + 2 * (j : ℚ) / 16 : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  push_cast
  ring

private theorem numerical_F3_priv (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : integralTerms F f ω 3 ≤ 17.327241 := by
  have hF3 := F3_elementary (F := F) (f := f) h ω
  rw [hF3]
  have hrec : (∫ t in (327/125:ℝ)..3, 1 / (t * (1 - t / 6))) = Real.log (141 / 109) := by
    rw [reciprocal_head (a := (327/125 : ℝ)) (by norm_num) (by norm_num)]
    norm_num
  have hform3 : (∫ t in (3:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) /
        (t * (1 - t / 6)))
      = ∫ t in (3:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) *
          (1 / (t * (1 - t / 6))) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [div_eq_mul_inv, one_div]
  rw [hrec, hform3, F3_inner_identity]
  -- logarithm bounds
  have h1 : Real.log (141 / 109) ≤ ((2 * (∑ k ∈ range 26, ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 53 / (1 - ((((141 / 109 : ℚ)) - 1) / (((141 / 109 : ℚ)) + 1)) ^ 2) : ℚ) : ℝ) := by
    have hc := rat_logUpper_cast 26 (141 / 109 : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((141 / 109 : ℚ) : ℝ)) (by norm_num)).2
    have hcast : ((141 / 109 : ℚ) : ℝ) = 141 / 109 := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have h2 : Real.log 5 ≤ ((2 * (∑ k ∈ range 26, (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 53 / (1 - (((5 : ℚ) - 1) / ((5 : ℚ) + 1)) ^ 2) : ℚ) : ℝ) := by
    have hc := rat_logUpper_cast 26 (5 : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((5 : ℚ) : ℝ)) (by norm_num)).2
    have hcast : ((5 : ℚ) : ℝ) = (5 : ℝ) := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have hP := Q_partition_upper
  have hc3 := certQ3R
  rw [castsumQ] at hc3
  have hmain : 8 * Real.log (141 / 109) + 8 * (Real.log 5 +
      ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x) ≤
      ((17327241 / 1000000 : ℚ) : ℝ) := by
    nlinarith [h1, h2, hP, hc3]
  calc 8 * Real.log (141 / 109) + 8 * (Real.log 5 +
        ∫ x in (2:ℝ)..4, Real.log (x - 1) * Real.log (5 * (5 - x) / (x + 1)) / x)
      ≤ ((17327241 / 1000000 : ℚ) : ℝ) := hmain
    _ = 17.327241 := by norm_num

private theorem certQ2 : 8 * ((2 * (∑ k ∈ range 26, (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 53 / (1 - (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 2)) - (2 * (∑ k ∈ range 26, (((141 / 109 : ℚ) - 1) / ((141 / 109 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)))) ≤ 3104857 / 1000000 := by
  decide +kernel

private lemma log_step_F2 : 8 * (Real.log (82 / 43) - Real.log (141 / 109)) ≤ 3104857 / 1000000 := by
  have ha : Real.log (82 / 43) ≤ ((2 * (∑ k ∈ range 26, (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 53 / (1 - (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 2)) : ℝ) := by
    have hc := rat_logUpper_cast 26 (82 / 43 : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((82 / 43 : ℚ) : ℝ)) (by norm_num)).2
    have hcast : ((82 / 43 : ℚ) : ℝ) = 82 / 43 := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have hb2 : ((2 * (∑ k ∈ range 26, (((141 / 109 : ℚ) - 1) / ((141 / 109 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1))) : ℝ) ≤ Real.log (141 / 109) := by
    have hc := rat_logLower_cast' 26 (141 / 109 : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((141 / 109 : ℚ) : ℝ)) (by norm_num)).1
    have hcast : ((141 / 109 : ℚ) : ℝ) = 141 / 109 := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have hcert : 8 * ((2 * (∑ k ∈ range 26, (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 53 / (1 - (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 2)) - (2 * (∑ k ∈ range 26, (((141 / 109 : ℚ) - 1) / ((141 / 109 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)))) ≤ (3104857 / 1000000 : ℚ) := certQ2
  have hcertR : 8 * ((2 * (∑ k ∈ range 26, (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 53 / (1 - (((82 / 43 : ℚ) - 1) / ((82 / 43 : ℚ) + 1)) ^ 2)) - (2 * (∑ k ∈ range 26, (((141 / 109 : ℚ) - 1) / ((141 / 109 : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)))) ≤ ((3104857 / 1000000 : ℚ) : ℝ) := by
    have h := hcert
    exact_mod_cast h
  linarith [ha, hb2, hcertR]

/-! ### The panel upper bound for `∫ log (x-1) log (5/(x+1)) / x` -/

private lemma P_panel_upper (p q : ℚ) (hp : 2 ≤ p) (hq : q ≤ 4) (hpq : p < q)
    (hsmall : q - p ≤ (p - 1) / 2) (hsmall2 : q - p ≤ p / 2)
    (lU gU : ℚ)
    (hlU : Real.log ((p : ℝ) - 1) ≤ (lU : ℝ))
    (hlG : Real.log (5 / ((p : ℝ) + 1)) ≤ (gU : ℝ)) :
    (∫ x in (p : ℝ)..(q : ℝ), Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
      ≤ ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then gU else if j' ≤ 8 then
              -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((p + 1 : ℚ)) ^ j')
              else 2 / ((p + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hP1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hPQ : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hQ4 : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hs1 : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ (((p - 1) / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall
    push_cast at this ⊢
    linarith
  have hs2 : (q : ℝ) - (p : ℝ) ≤ (p : ℝ) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ ((p / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall2
    push_cast at this ⊢
    linarith
  set A : ℕ → ℝ := fun i => (((if i = 0 then lU else if i ≤ 8 then
      (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i) else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
    with hAdef
  set B : ℕ → ℝ := fun j => (((if j = 0 then gU else if j ≤ 8 then
      -((-1 : ℚ) ^ (j - 1)) / ((j : ℚ) * ((p + 1 : ℚ)) ^ j)
      else 2 / ((p + 1 : ℚ)) ^ j) : ℚ) : ℝ) with hBdef
  set C : ℕ → ℝ := fun l => (((if l = 0 then
      (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
      else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ) with hCdef
  have hrow : (∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if j' = 0 then gU else if j' ≤ 8 then
              -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * ((p + 1 : ℚ)) ^ j')
              else 2 / ((p + 1 : ℚ)) ^ j') : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)))
      = ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10,
          A i * B j' * C l * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    simp only [hAdef, hBdef, hCdef]
  rw [hrow, ← int_prod3 (p : ℝ) (q : ℝ) hPQ.le A B C 10 10 9]
  refine intervalIntegral.integral_mono_on hPQ.le ?_ ?_ ?_
  · exact (logP_continuousOn hPQ.le hp2).intervalIntegrable
  · refine (by fun_prop : Continuous fun x : ℝ =>
      (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j' ∈ range 10, B j' * (x - (p : ℝ)) ^ j') *
        (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)).intervalIntegrable _ _
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hxp, hxq⟩ := hx
    set t : ℝ := x - (p : ℝ) with htdef
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have htH : t ≤ (q : ℝ) - (p : ℝ) := by rw [htdef]; linarith
    have hPm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hPp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
    set u : ℝ := t / ((p : ℝ) - 1) with hudef
    set v : ℝ := t / ((p : ℝ) + 1) with hvdef
    set w : ℝ := t / (p : ℝ) with hwdef
    have hu0 : 0 ≤ u := div_nonneg ht0 hPm1.le
    have hu1 : u ≤ 1 / 2 := by
      rw [hudef, div_le_iff₀ hPm1]; nlinarith [hs1, htH]
    have hv0 : 0 ≤ v := div_nonneg ht0 hPp1.le
    have hv1 : v ≤ 1 / 2 := by
      rw [hvdef, div_le_iff₀ hPp1]; nlinarith [hs2, htH]
    have hw0 : 0 ≤ w := div_nonneg ht0 hP0.le
    have hw1 : w ≤ 1 / 2 := by
      rw [hwdef, div_le_iff₀ hP0]; nlinarith [hs2, htH]
    have hArow : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i)
        = (lU : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) + 2 * u ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : A 0 = (lU : ℝ) := by simp only [hAdef, ↓reduceIte]
      have e9 : A 9 = 2 / ((p : ℝ) - 1) ^ 9 := by
        simp only [hAdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, A (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hAi : A (i + 1) = (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) - 1) ^ (i + 1) := by
          simp only [hAdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hAi]
        rw [show u ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) - 1) ^ (i + 1) from by
          rw [hudef, div_pow]]
        ring
      rw [hmid]
      rw [show 2 / ((p : ℝ) - 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * u ^ 9 from by
        rw [show u ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) - 1) ^ 9 from by rw [hudef, div_pow]]
        field_simp]
      ring
    have hBrow : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
        = (gU : ℝ) - (∑ i ∈ range 8, (-1 : ℝ) ^ i * v ^ (i + 1) / (i + 1)) + 2 * v ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : B 0 = (gU : ℝ) := by simp only [hBdef, ↓reduceIte]
      have e9 : B 9 = 2 / ((p : ℝ) + 1) ^ 9 := by
        simp only [hBdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, B (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, -((-1 : ℝ) ^ i * v ^ (i + 1) / (i + 1)) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hBi : B (i + 1) = -((-1 : ℝ) ^ i) / ((i : ℝ) + 1) / ((p : ℝ) + 1) ^ (i + 1) := by
          simp only [hBdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hBi]
        rw [show v ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) + 1) ^ (i + 1) from by
          rw [hvdef, div_pow]]
        ring
      rw [hmid, Finset.sum_neg_distrib]
      have h2a : 2 / ((p : ℝ) + 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * v ^ 9 := by
        rw [hvdef, div_pow]
        ring
      rw [h2a]
      ring
    have hCrow : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
        = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
          + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
      rw [Finset.sum_range_succ']
      have eC0 : C 0 = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
        simp only [hCdef, ↓reduceIte]
        push_cast
        ring
      rw [eC0]
      have hmid : (∑ l ∈ range 8, C (l + 1) * (x - (p : ℝ)) ^ (l + 1))
          = (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have hCl : C (l + 1) = (-1 : ℝ) ^ (l + 1) / (p : ℝ) ^ (l + 2) := by
          simp only [hCdef]
          rw [if_neg (by omega : l + 1 ≠ 0)]
          push_cast
          field_simp
        rw [hCl]
        rw [show (-w) ^ (l + 1) = (-1 : ℝ) ^ (l + 1) * (x - (p : ℝ)) ^ (l + 1) / (p : ℝ) ^ (l + 1) from by
          rw [hwdef, show -(t / (p:ℝ)) = -((x - (p:ℝ)) / (p:ℝ)) from by rw [htdef], neg_pow, div_pow]
          ring]
        field_simp
        rw [pow_succ]
        ring
      rw [hmid]
      ring
    have hAle : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) ≥ Real.log (x - 1) := by
      rw [hArow]
      have hx1 : x - 1 = ((p : ℝ) - 1) * (1 + u) := by
        rw [show 1 + u = (x - 1) / ((p : ℝ) - 1) from by
          rw [hudef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_mul (by linarith) (by linarith)]
      have h := log_one_add_le9 hu0 hu1
      linarith
    have hBle : (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) ≥ Real.log (5 / (x + 1)) := by
      rw [hBrow]
      have h1p : 1 + v = (x + 1) / ((p : ℝ) + 1) := by
        rw [hvdef]; field_simp; ring
      have hsplit : 5 / (x + 1) = (5 / ((p : ℝ) + 1)) * (1 / (1 + v)) := by
        rw [h1p]; field_simp
      have hpos5 : (0 : ℝ) < 5 / ((p : ℝ) + 1) := by positivity
      have h1v : (0 : ℝ) < 1 + v := by linarith
      rw [hsplit, Real.log_mul hpos5.ne' (by positivity), Real.log_div one_pos.ne' h1v.ne',
        Real.log_one]
      have h2 := log_one_add_le9 hv0 hv1
      have h3 := log_one_add_ge9 hv0 hv1
      linarith [hlG, h2, h3]
    have hCle : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≥ 1 / x := by
      rw [hCrow]
      have hsum : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := (inv_geom_bounds (p := (p : ℝ)) (h := (q : ℝ) - (p : ℝ)) hP0 (by linarith) hs2 8
        (t := t) ⟨ht0, htH⟩).2
      rw [show -(t / (p : ℝ)) = -w from by rw [hwdef]] at hg
      rw [show (p : ℝ) + t = x from by rw [htdef]; ring, hsum] at hg
      calc (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 + ∑ l ∈ range 8, (-w) ^ (l + 1)) * (1 / (p : ℝ))
            + (1 / (p : ℝ)) * ((((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by ring
        _ ≥ 1 / x := hg
    have hf0 : 0 ≤ Real.log (x - 1) := Real.log_nonneg (by linarith)
    have hg0 : 0 ≤ Real.log (5 / (x + 1)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hA0 : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) := hf0.trans hAle
    have hB0 : 0 ≤ (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) := hg0.trans hBle
    have hC0 : 0 ≤ (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by
      have hx0 : (0:ℝ) < x := by linarith
      have : (0:ℝ) < 1 / x := by exact div_pos one_pos hx0
      linarith [hCle]
    have h1 : Real.log (x - 1) * Real.log (5 / (x + 1))
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 / (x + 1)) :=
      mul_le_mul_of_nonneg_right hAle hg0
    have hx0 : (0:ℝ) < x := by linarith
    have h2 : Real.log (x - 1) * Real.log (5 / (x + 1)) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 / (x + 1)) * (1 / x) :=
      mul_le_mul_of_nonneg_right h1 (by exact le_of_lt (div_pos one_pos hx0))
    have h3 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 / (x + 1))
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j) :=
      mul_le_mul_of_nonneg_left hBle hA0
    have h4 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * Real.log (5 / (x + 1)) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (1 / x) :=
      mul_le_mul_of_nonneg_right h3 (by exact le_of_lt (div_pos one_pos hx0))
    have h5 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j ∈ range 10, B j * (x - (p : ℝ)) ^ j)
          * (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
      mul_le_mul_of_nonneg_left hCle (mul_nonneg hA0 hB0)
    have h6 : Real.log (x - 1) * Real.log (5 / (x + 1)) / x
        = Real.log (x - 1) * Real.log (5 / (x + 1)) * (1 / x) := by
      simp only [div_eq_mul_inv]
      ring
    rw [h6]
    linarith [h2, h4, h5]

/-! ### The panel upper bound for `∫ log (x-1) / x` (the `J` terms of `F1`) -/

private lemma J_panel_upper (p q : ℚ) (hp : 2 ≤ p) (hq : q ≤ 4) (hpq : p < q)
    (hsmall : q - p ≤ (p - 1) / 2) (hsmall2 : q - p ≤ p / 2)
    (lU : ℚ) (hlU : Real.log ((p : ℝ) - 1) ≤ (lU : ℝ)) :
    (∫ x in (p : ℝ)..(q : ℝ), Real.log (x - 1) / x)
      ≤ ∑ l ∈ range 9, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hPQ : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hq4 : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hs1 : (q : ℝ) - (p : ℝ) ≤ ((p : ℝ) - 1) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ (((p - 1) / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall
    push_cast at this ⊢
    linarith
  have hs2 : (q : ℝ) - (p : ℝ) ≤ (p : ℝ) / 2 := by
    have : ((q - p : ℚ) : ℝ) ≤ ((p / 2 : ℚ) : ℝ) := by exact_mod_cast hsmall2
    push_cast at this ⊢
    linarith
  set A : ℕ → ℝ := fun i => (((if i = 0 then lU else if i ≤ 8 then
      (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i) else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
    with hAdef
  set B : ℕ → ℝ := fun _ => 1 with hBdef
  set C : ℕ → ℝ := fun l => (((if l = 0 then
      (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
      else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ) with hCdef
  have hrow : (∑ l ∈ range 9, ∑ i ∈ range 10,
        (((if i = 0 then lU else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * ((p - 1 : ℚ)) ^ i)
              else 2 / ((p - 1 : ℚ)) ^ i) : ℚ) : ℝ)
        * (((if l = 0 then (1 : ℚ) / p + ((1 : ℚ) / p) * (((q - p) / p) ^ 9 / (1 - (q - p) / p))
              else (-1 : ℚ) ^ l / (p : ℚ) ^ (l + 1)) : ℚ) : ℝ)
        * (((q : ℝ) - (p : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)))
      = ∑ l ∈ range 9, ∑ j' ∈ range 1, ∑ i ∈ range 10,
          A i * B j' * C l * (((q : ℝ) - (p : ℝ)) ^ (i + j' + l + 1) /
            ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    simp only [hAdef, hBdef, hCdef, Finset.sum_range_one]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun i _ => ?_))
    norm_num
  rw [hrow, ← int_prod3 (p : ℝ) (q : ℝ) hPQ.le A B C 10 1 9]
  refine intervalIntegral.integral_mono_on hPQ.le ?_ ?_ ?_
  · exact (logquot_continuousOn.mono (by
      intro x hx
      rw [Set.uIcc_of_le hPQ.le] at hx
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
      exact ⟨by linarith [hx.1], by linarith [hx.2, hq4]⟩)).intervalIntegrable
  · refine (by fun_prop : Continuous fun x : ℝ =>
      (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ j' ∈ range 1, B j' * (x - (p : ℝ)) ^ j') *
        (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)).intervalIntegrable _ _
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hxp, hxq⟩ := hx
    set t : ℝ := x - (p : ℝ) with htdef
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have htH : t ≤ (q : ℝ) - (p : ℝ) := by rw [htdef]; linarith
    have hPm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hPp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
    set u : ℝ := t / ((p : ℝ) - 1) with hudef
    set w : ℝ := t / (p : ℝ) with hwdef
    have hu0 : 0 ≤ u := div_nonneg ht0 hPm1.le
    have hu1 : u ≤ 1 / 2 := by
      rw [hudef, div_le_iff₀ hPm1]; nlinarith [hs1, htH]
    have hw0 : 0 ≤ w := div_nonneg ht0 hP0.le
    have hw1 : w ≤ 1 / 2 := by
      rw [hwdef, div_le_iff₀ hP0]; nlinarith [hs2, htH]
    have hBone : (∑ j' ∈ range 1, B j' * (x - (p : ℝ)) ^ j') = 1 := by
      simp only [Finset.sum_range_one, hBdef]
      norm_num
    have hArow : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i)
        = (lU : ℝ) + (∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)) + 2 * u ^ 9 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have e0 : A 0 = (lU : ℝ) := by simp only [hAdef, ↓reduceIte]
      have e9 : A 9 = 2 / ((p : ℝ) - 1) ^ 9 := by
        simp only [hAdef]
        rw [if_neg (by norm_num : (9 : ℕ) ≠ 0), if_neg (by norm_num : ¬ (9 : ℕ) ≤ 8)]
        push_cast
        ring
      rw [e0, e9]
      have hmid : (∑ i ∈ range 8, A (i + 1) * (x - (p : ℝ)) ^ (i + 1))
          = ∑ i ∈ range 8, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi8 : i + 1 ≤ 8 := by simpa using Finset.mem_range.mp hi
        have hAi : A (i + 1) = (-1 : ℝ) ^ i / ((i : ℝ) + 1) / ((p : ℝ) - 1) ^ (i + 1) := by
          simp only [hAdef]
          rw [if_neg (by omega : i + 1 ≠ 0), if_pos hi8]
          push_cast
          field_simp
        rw [hAi]
        rw [show u ^ (i + 1) = (x - (p : ℝ)) ^ (i + 1) / ((p : ℝ) - 1) ^ (i + 1) from by
          rw [hudef, div_pow]]
        ring
      rw [hmid]
      rw [show 2 / ((p : ℝ) - 1) ^ 9 * (x - (p : ℝ)) ^ 9 = 2 * u ^ 9 from by
        rw [show u ^ 9 = (x - (p : ℝ)) ^ 9 / ((p : ℝ) - 1) ^ 9 from by rw [hudef, div_pow]]
        field_simp]
      ring
    have hCrow : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l)
        = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
          + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
      rw [Finset.sum_range_succ']
      have eC0 : C 0 = (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
            (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
        simp only [hCdef, ↓reduceIte]
        push_cast
        ring
      rw [eC0]
      have hmid : (∑ l ∈ range 8, C (l + 1) * (x - (p : ℝ)) ^ (l + 1))
          = (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have hCl : C (l + 1) = (-1 : ℝ) ^ (l + 1) / (p : ℝ) ^ (l + 2) := by
          simp only [hCdef]
          rw [if_neg (by omega : l + 1 ≠ 0)]
          push_cast
          field_simp
        rw [hCl]
        rw [show (-w) ^ (l + 1) = (-1 : ℝ) ^ (l + 1) * (x - (p : ℝ)) ^ (l + 1) / (p : ℝ) ^ (l + 1) from by
          rw [hwdef, show -(t / (p:ℝ)) = -((x - (p:ℝ)) / (p:ℝ)) from by rw [htdef], neg_pow, div_pow]
          ring]
        field_simp
        rw [pow_succ]
        ring
      rw [hmid]
      ring
    have hAle : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) ≥ Real.log (x - 1) := by
      rw [hArow]
      have hx1 : x - 1 = ((p : ℝ) - 1) * (1 + u) := by
        rw [show 1 + u = (x - 1) / ((p : ℝ) - 1) from by
          rw [hudef, htdef]; field_simp; ring]
        field_simp
      rw [hx1, Real.log_mul (by linarith) (by linarith)]
      have h := log_one_add_le9 hu0 hu1
      linarith
    have hCle : (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) ≥ 1 / x := by
      rw [hCrow]
      have hsum : (∑ l ∈ range 9, (-w) ^ l) = 1 + ∑ l ∈ range 8, (-w) ^ (l + 1) := by
        rw [Finset.sum_range_succ']
        norm_num
        ring
      have hg := (inv_geom_bounds (p := (p : ℝ)) (h := (q : ℝ) - (p : ℝ)) hP0 (by linarith) hs2 8
        (t := t) ⟨ht0, htH⟩).2
      rw [show -(t / (p : ℝ)) = -w from by rw [hwdef]] at hg
      rw [show (p : ℝ) + t = x from by rw [htdef]; ring, hsum] at hg
      calc (1 / (p : ℝ) + (1 / (p : ℝ)) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ 9 /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ)))
            + (1 / (p : ℝ)) * (∑ l ∈ range 8, (-w) ^ (l + 1))
          = (1 + ∑ l ∈ range 8, (-w) ^ (l + 1)) * (1 / (p : ℝ))
            + (1 / (p : ℝ)) * ((((q : ℝ) - (p : ℝ)) / (p : ℝ)) ^ (8 + 1) /
              (1 - ((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by ring
        _ ≥ 1 / x := hg
    have hf0 : 0 ≤ Real.log (x - 1) := Real.log_nonneg (by linarith)
    have hA0 : 0 ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) := hf0.trans hAle
    have hx0 : (0:ℝ) < x := by linarith
    have hC0 : 0 ≤ (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by
      have : (0:ℝ) < 1 / x := by exact div_pos one_pos hx0
      linarith [hCle]
    have h1 : Real.log (x - 1) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (1 / x) :=
      mul_le_mul_of_nonneg_right hAle (by exact le_of_lt (div_pos one_pos hx0))
    have h2 : (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) :=
      mul_le_mul_of_nonneg_left hCle hA0
    have h3 : Real.log (x - 1) / x = Real.log (x - 1) * (1 / x) := by
      simp only [div_eq_mul_inv]
      ring
    have h4 : (∑ j' ∈ range 1, B j' * (x - (p : ℝ)) ^ j') = 1 := hBone
    rw [h3]
    calc Real.log (x - 1) * (1 / x)
        ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) * (1 / x) := h1
      _ ≤ (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := h2
      _ = (∑ i ∈ range 10, A i * (x - (p : ℝ)) ^ i) *
            (∑ j' ∈ range 1, B j' * (x - (p : ℝ)) ^ j') *
            (∑ l ∈ range 9, C l * (x - (p : ℝ)) ^ l) := by rw [hBone]; ring

/-! ### The `F1` panel partitions and leaf -/

private lemma P_partition_F1 :
    (∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x) ≤ ∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16) : ℚ) : ℝ) - (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  set a : ℕ → ℝ := fun j => ((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) with hadef
  have ha0 : a 0 = 67/29 := by rw [hadef]; norm_num
  have ha16 : a 16 = 4 := by rw [hadef]; norm_num
  have hint : ∀ k < 16, IntervalIntegrable
      (fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) volume (a k) (a (k + 1)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ a k := by
      rw [hadef]; push_cast
      have h : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hle : a k ≤ a (k + 1) := by
      rw [hadef]; push_cast
      have h : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
      linarith
    exact (logP_continuousOn hle hk2).intervalIntegrable
  have hcell : ∀ j ∈ range 16,
      (∫ x in a j..a (j + 1), Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
        ≤ ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16) : ℚ) : ℝ) - (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
    intro j hj
    have hj16 : j < 16 := Finset.mem_range.mp hj
    have hp2 : (2 : ℚ) ≤ 67 / 29 + (49 / 29) * (j : ℚ) / 16 := by
      have h : 0 ≤ (49 / 29) * (j : ℚ) / 16 := by positivity
      linarith
    have hq4 : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 ≤ 4 := by
      have hj1 : ((j + 1 : ℕ) : ℚ) ≤ 16 := by
        have h : j + 1 ≤ 16 := by omega
        exact_mod_cast h
      nlinarith
    have hpq : 67 / 29 + (49 / 29) * (j : ℚ) / 16 < 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 := by
      have h : (j : ℚ) < ((j + 1 : ℕ) : ℚ) := by
        have h' : j < j + 1 := by omega
        exact_mod_cast h'
      linarith
    have hsmall : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 - (67 / 29 + (49 / 29) * (j : ℚ) / 16)
        ≤ (67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) / 2 := by
      have h1 : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 - (67 / 29 + (49 / 29) * (j : ℚ) / 16)
          = 49 / 464 := by push_cast; ring
      rw [h1]; nlinarith
    have hsmall2 : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 - (67 / 29 + (49 / 29) * (j : ℚ) / 16)
        ≤ (67 / 29 + (49 / 29) * (j : ℚ) / 16) / 2 := by
      have h1 : 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 - (67 / 29 + (49 / 29) * (j : ℚ) / 16)
          = 49 / 464 := by push_cast; ring
      rw [h1]; nlinarith
    have hlU : Real.log ((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) - 1 : ℝ)
        ≤ (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2) : ℚ) := by
      have hc := rat_logUpper_cast 20 (67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1)
      have hy1 : (1 : ℚ) ≤ 67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1 := by
        have h : 0 ≤ (49 / 29) * (j : ℚ) / 16 := by positivity
        linarith
      have hb := (Wu04Integral.log_bounds 20
        (y := ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1 : ℚ) : ℝ)) (by exact_mod_cast hy1)).2
      have hcast : ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1 : ℚ) : ℝ)
          = ((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) - 1 := by push_cast; ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hlG : Real.log (5 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) + 1))
        ≤ (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2) : ℚ) := by
      have hc := rat_logUpper_cast 20 (5 / (67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))
      have hy1 : (1 : ℚ) ≤ 5 / (67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) := by
        rw [le_div_iff₀ (by positivity)]
        have h : 0 ≤ (49 / 29) * (j : ℚ) / 16 := by positivity
        linarith
      have hb := (Wu04Integral.log_bounds 20
        (y := ((5 / (67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ) : ℝ)) (by exact_mod_cast hy1)).2
      have hcast : ((5 / (67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ) : ℝ)
          = 5 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) + 1) := by push_cast; ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hpanel := P_panel_upper (p := 67 / 29 + (49 / 29) * (j : ℚ) / 16)
      (q := 67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)
      (lU := 2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) (gU := 2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2))
      hp2 hq4 hpq hsmall hsmall2 hlU hlG
    have hcast2 : ((67 / 29 + (49 / 29) * (j : ℚ) / 16 : ℚ) : ℝ) = a j := by rw [hadef]
    have hcast3 : ((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16 : ℚ) : ℝ) = a (j + 1) := by rw [hadef]
    simpa only [hcast2, hcast3] using hpanel
  have hsum_int : (∑ j ∈ range 16, ∫ x in a j..a (j + 1),
      Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
      = ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
    have h := sum_integral_adjacent_intervals (a := a) (n := 16)
      (f := fun x : ℝ => Real.log (x - 1) * Real.log (5 / (x + 1)) / x) hint
    rw [ha0, ha16] at h
    exact h
  rw [← hsum_int]
  exact Finset.sum_le_sum hcell

private lemma J_partition_F1 :
    (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) ≤ ∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := by
  set a : ℕ → ℝ := fun j => ((2 + (9 / 29) * (j : ℚ) / 8 : ℚ) : ℝ) with hadef
  have ha0 : a 0 = 2 := by rw [hadef]; norm_num
  have ha8 : a 8 = 67/29 := by rw [hadef]; norm_num
  have hint : ∀ k < 8, IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume (a k) (a (k + 1)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ a k := by
      rw [hadef]; push_cast
      have h : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hle : a k ≤ a (k + 1) := by
      rw [hadef]; push_cast
      have h : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
      linarith
    have hk4 : a (k + 1) ≤ 4 := by
      rw [hadef]; push_cast
      have hk8 : (k : ℝ) + 1 ≤ 8 := by
        have : k + 1 ≤ 8 := by omega
        exact_mod_cast this
      linarith
    exact (logquot_continuousOn.mono (by
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
      exact ⟨by linarith [hx.1], by linarith [hx.2, hk4]⟩)).intervalIntegrable
  have hcell : ∀ j ∈ range 8,
      (∫ x in a j..a (j + 1), Real.log (x - 1) / x)
        ≤ ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := by
    intro j hj
    have hj8 : j < 8 := Finset.mem_range.mp hj
    have hp2 : (2 : ℚ) ≤ 2 + (9 / 29) * (j : ℚ) / 8 := by
      have h : 0 ≤ (9 / 29) * (j : ℚ) / 8 := by positivity
      linarith
    have hq4 : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 ≤ 4 := by
      have hj1 : ((j + 1 : ℕ) : ℚ) ≤ 8 := by
        have h : j + 1 ≤ 8 := by omega
        exact_mod_cast h
      nlinarith
    have hpq : 2 + (9 / 29) * (j : ℚ) / 8 < 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 := by
      have h : (j : ℚ) < ((j + 1 : ℕ) : ℚ) := by
        have h' : j < j + 1 := by omega
        exact_mod_cast h'
      linarith
    have hsmall : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 - (2 + (9 / 29) * (j : ℚ) / 8)
        ≤ (2 + (9 / 29) * (j : ℚ) / 8 - 1) / 2 := by
      have h1 : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 - (2 + (9 / 29) * (j : ℚ) / 8) = 9 / 232 := by
        push_cast; ring
      rw [h1]; nlinarith
    have hsmall2 : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 - (2 + (9 / 29) * (j : ℚ) / 8)
        ≤ (2 + (9 / 29) * (j : ℚ) / 8) / 2 := by
      have h1 : 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 - (2 + (9 / 29) * (j : ℚ) / 8) = 9 / 232 := by
        push_cast; ring
      rw [h1]; nlinarith
    have hlU : Real.log ((2 + (9 / 29) * (j : ℚ) / 8 : ℚ) - 1 : ℝ) ≤ (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2) : ℚ) := by
      have hc := rat_logUpper_cast 20 (2 + (9 / 29) * (j : ℚ) / 8 - 1)
      have hy1 : (1 : ℚ) ≤ 2 + (9 / 29) * (j : ℚ) / 8 - 1 := by
        have h : 0 ≤ (9 / 29) * (j : ℚ) / 8 := by positivity
        linarith
      have hb := (Wu04Integral.log_bounds 20
        (y := ((2 + (9 / 29) * (j : ℚ) / 8 - 1 : ℚ) : ℝ)) (by exact_mod_cast hy1)).2
      have hcast : ((2 + (9 / 29) * (j : ℚ) / 8 - 1 : ℚ) : ℝ)
          = ((2 + (9 / 29) * (j : ℚ) / 8 : ℚ) : ℝ) - 1 := by push_cast; ring
      rw [hcast] at hc hb
      linarith [hc, hb]
    have hpanel := J_panel_upper (p := 2 + (9 / 29) * (j : ℚ) / 8)
      (q := 2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) (lU := 2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2))
      hp2 hq4 hpq hsmall hsmall2 hlU
    have hcast2 : ((2 + (9 / 29) * (j : ℚ) / 8 : ℚ) : ℝ) = a j := by rw [hadef]
    have hcast3 : ((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8 : ℚ) : ℝ) = a (j + 1) := by rw [hadef]
    simpa only [hcast2, hcast3] using hpanel
  have hsum_int : (∑ j ∈ range 8, ∫ x in a j..a (j + 1), Real.log (x - 1) / x)
      = ∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x := by
    have h := sum_integral_adjacent_intervals (a := a) (n := 8)
      (f := fun x : ℝ => Real.log (x - 1) / x) hint
    rw [ha0, ha8] at h
    exact h
  rw [← hsum_int]
  exact Finset.sum_le_sum hcell

private lemma castsumP : ((∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) * ((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)) : ℚ) : ℝ) = ∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16) : ℚ) : ℝ) - (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ) : ℝ)) ^ (i + j' + l + 1) / ((i : ℝ) + (j' : ℝ) + (l : ℝ) + 1)) := by
  push_cast
  ring

private lemma castsumJ : ((∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) * (if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) * ((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) ^ (i + l + 1) / ((i : ℚ) + (l : ℚ) + 1)) : ℚ) : ℝ) =
      ∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := by
  push_cast
  ring

private lemma F1_inner_identity :
    (∫ t in (96/29:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t))
      = Real.log (5 / (96/29)) + Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        + ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
  have ha : (96/29:ℝ) ≤ 5 := by norm_num
  have hA_cont : ContinuousOn (fun t : ℝ => ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x)
      (Set.uIcc (96/29:ℝ) 5) := by
    have h := continuousOn_primitive_interval' logquot_integrable
      (Set.left_mem_uIcc (a := (2:ℝ)) (b := (4:ℝ)))
    refine h.comp (by fun_prop) ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (96/29:ℝ) ≤ 5)] at ht
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
    constructor <;> linarith [ht.1, ht.2]
  have hinv_cont : ContinuousOn (fun t : ℝ => 1 / t) (Set.uIcc (96/29:ℝ) 5) := by
    rw [Set.uIcc_of_le ha]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; change t ≠ 0; linarith [ht.1]
  have hint2 : IntervalIntegrable
      (fun t : ℝ => (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t)) volume (96/29) 5 :=
    (hA_cont.mul hinv_cont).intervalIntegrable
  have hsplit : (∫ t in (96/29:ℝ)..5,
        (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t))
      = (∫ t in (96/29:ℝ)..5, 1 / t)
        + ∫ t in (96/29:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t) := by
    rw [← intervalIntegral.integral_add hinv_cont.intervalIntegrable hint2]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hlog : (∫ t in (96/29:ℝ)..5, 1 / t) = Real.log (5 / (96/29)) := by
    rw [show (∫ t in (96/29:ℝ)..5, 1 / t) = ∫ t in (96/29:ℝ)..5, (t)⁻¹ from by
      apply intervalIntegral.integral_congr; intro t _; rw [one_div]]
    rw [integral_inv_of_pos (by norm_num : (0:ℝ) < 96/29) (by norm_num : (0:ℝ) < 5)]
  have hAsplit : ∀ t ∈ Set.uIcc (96/29:ℝ) 5,
      (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x)
        = (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
          + ∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x := by
    intro t ht
    rw [Set.uIcc_of_le ha] at ht
    have h1 : (2:ℝ) ≤ 67/29 := by norm_num
    have h2 : (67/29:ℝ) ≤ t - 1 := by linarith [ht.1]
    have hi1 : IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume 2 (67/29) :=
      logquot_continuousOn.mono (by
        intro x hx
        rw [Set.uIcc_of_le h1] at hx
        rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
        exact ⟨hx.1, by linarith [hx.2]⟩) |>.intervalIntegrable
    have hi2 : IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume (67/29) (t - 1) :=
      logquot_continuousOn.mono (by
        intro x hx
        rw [Set.uIcc_of_le h2] at hx
        rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
        exact ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩) |>.intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hperm : (∫ t in (96/29:ℝ)..5, (∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t))
      = (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) * (∫ t in (96/29:ℝ)..5, 1 / t)
        + ∫ t in (96/29:ℝ)..5, (∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t) := by
    have e1 : (∫ t in (96/29:ℝ)..5, (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) * (1 / t))
        = (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) * (∫ t in (96/29:ℝ)..5, 1 / t) := by
      rw [intervalIntegral.integral_const_mul]
    have e2 : IntervalIntegrable
        (fun t : ℝ => (∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t)) volume (96/29) 5 := by
      have hA2 : ContinuousOn (fun t : ℝ => ∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x)
          (Set.uIcc (96/29:ℝ) 5) := by
        have h67 : IntervalIntegrable (fun x : ℝ => Real.log (x - 1) / x) volume (67/29) 4 := by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le (by norm_num : (67/29:ℝ) ≤ 4)]
          apply ContinuousOn.div
          · apply ContinuousOn.log (by fun_prop)
            intro x hx; linarith [hx.1]
          · exact continuousOn_id
          · intro x hx; change x ≠ 0; linarith [hx.1]
        have h := continuousOn_primitive_interval' h67
          (Set.left_mem_uIcc (a := (67/29:ℝ)) (b := (4:ℝ)))
        refine h.comp (by fun_prop) ?_
        intro t ht
        rw [Set.uIcc_of_le ha] at ht
        rw [Set.uIcc_of_le (by norm_num : (67/29:ℝ) ≤ 4)]
        constructor <;> linarith [ht.1, ht.2]
      exact (hA2.mul hinv_cont).intervalIntegrable
    rw [← e1]
    rw [← intervalIntegral.integral_add
      (hinv_cont.intervalIntegrable.const_mul _) e2]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only []
    rw [hAsplit t ht]
    ring
  have hswap := triangle_swap (f := fun x : ℝ => Real.log (x - 1) / x) (h := fun t : ℝ => 1 / t)
    (c := 1) (A := 96/29) (B := 5) (hc := by norm_num) (hAB := by norm_num)
    (hf := by
      rw [show (96/29:ℝ) - 1 = 67/29 by norm_num, show (5:ℝ) - 1 = 4 by norm_num]
      exact logquot_continuousOn.mono (by
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (67/29:ℝ) ≤ 4)] at hx
        rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
        exact ⟨by linarith [hx.1], hx.2⟩))
    (hh := by
      rw [show (96/29:ℝ) = 96/29 by norm_num]
      exact hinv_cont)
  simp only [show (96/29:ℝ) - 1 = 67/29 by norm_num, show (5:ℝ) - 1 = 4 by norm_num] at hswap
  have hweight : ∀ x ∈ Set.uIcc (2:ℝ) 4, (∫ t in (x + 1)..5, 1 / t) = Real.log (5 / (x + 1)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)] at hx
    rw [show (∫ t in (x + 1)..5, 1 / t) = ∫ t in (x + 1)..5, (t)⁻¹ from by
      apply intervalIntegral.integral_congr; intro t _; rw [one_div]]
    rw [integral_inv_of_pos (by linarith [hx.1] : (0:ℝ) < x + 1) (by norm_num : (0:ℝ) < 5)]
  have hPform : (∫ t in (96/29:ℝ)..5, (∫ x in (67/29:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t))
      = ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x := by
    rw [hswap]
    apply intervalIntegral.integral_congr
    intro x hx
    change Real.log (x - 1) / x * (∫ t in (x + 1)..5, 1 / t)
      = Real.log (x - 1) * Real.log (5 / (x + 1)) / x
    rw [hweight x (by
      rw [Set.uIcc_of_le (by norm_num : (67/29:ℝ) ≤ 4)] at hx
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)]
      exact ⟨by linarith [hx.1], hx.2⟩)]
    ring
  rw [hsplit, hlog, hperm, hlog, hPform]
  ring

private theorem certF1 :
    8 * ((2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) + (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) * (∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) * (if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) * ((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) ^ (i + l + 1) / ((i : ℚ) + (l : ℚ) + 1))) + (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) * ((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) ≤ 3891854 / 1000000 := by
  decide +kernel

private lemma certF1R :
    8 * ((2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) + (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) * (∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) * (if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) * ((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) ^ (i + l + 1) / ((i : ℚ) + (l : ℚ) + 1))) + (∑ j ∈ range 16, ∑ l ∈ range 9, ∑ j' ∈ range 10, ∑ i ∈ range 10, (if i = 0 then (2 * (∑ k ∈ range 20, (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 41 / (1 - (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) - 1) / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 - 1) : ℚ)) ^ i) * (if j' = 0 then (2 * (∑ k ∈ range 20, (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 41 / (1 - (((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) - 1) / ((5 / ((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1))) + 1)) ^ 2)) else if j' ≤ 8 then -((-1 : ℚ) ^ (j' - 1)) / ((j' : ℚ) * (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') else 2 / (((67 / 29 + (49 / 29) * (j : ℚ) / 16 + 1) : ℚ)) ^ j') * (if l = 0 then (1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16) + ((1 : ℚ) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) * (((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16)) ^ 9 / (1 - (((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) / (67 / 29 + (49 / 29) * (j : ℚ) / 16))) else (-1 : ℚ) ^ l / (((67 / 29 + (49 / 29) * (j : ℚ) / 16) : ℚ)) ^ (l + 1)) * ((((67 / 29 + (49 / 29) * ((j + 1 : ℕ) : ℚ) / 16)) - ((67 / 29 + (49 / 29) * (j : ℚ) / 16))) ^ (i + j' + l + 1) / ((i : ℚ) + (j' : ℚ) + (l : ℚ) + 1)))) ≤ ((3891854 / 1000000 : ℚ) : ℝ) := by
  have h := certF1
  exact_mod_cast h

theorem numerical_F1_aux (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : integralTerms F f ω 1 ≤ 3.891854 := by
  have hF1 := F1_elementary (F := F) (f := f) h ω
  rw [hF1]
  rw [show (1 / (2 * kappa2) - 1 : ℝ) = 96/29 by norm_num [kappa2],
    show (1 / (2 * kappa1) - 1 : ℝ) = 5 by norm_num [kappa1]]
  have hform : (∫ t in (96/29:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) / t)
      = ∫ t in (96/29:ℝ)..5, (1 + ∫ x in (2:ℝ)..(t - 1), Real.log (x - 1) / x) * (1 / t) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [div_eq_mul_inv, one_div]
  rw [hform, F1_inner_identity]
  -- log bounds and the two panel bounds
  have h1 : Real.log (5 / (96/29)) ≤ ((2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2)) : ℝ) := by
    have hc := rat_logUpper_cast 26 (5 / (96 / 29) : ℚ)
    have hb := (Wu04Integral.log_bounds 26 (y := ((5 / (96 / 29) : ℚ) : ℝ)) (by norm_num)).2
    have hcast : ((5 / (96 / 29) : ℚ) : ℝ) = 5 / (96/29) := by norm_num
    rw [hcast] at hc hb
    linarith [hc, hb]
  have hP := P_partition_F1
  have hJ := J_partition_F1
  have hc := certF1R
  rw [castsumP, castsumJ] at hc
  have h5a : (0:ℝ) ≤ (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) := by
    have := (Wu04Integral.log_bounds 26 (y := ((5 / (96 / 29) : ℚ) : ℝ)) (by norm_num)).1
    have hc2 := rat_logLower_cast' 26 (5 / (96 / 29) : ℚ)
    nlinarith [this, hc2]
  have hlog0 : (0:ℝ) ≤ Real.log (5 / (96/29)) := Real.log_nonneg (by norm_num)
  have hJ0 : (0:ℝ) ≤ ∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    apply div_nonneg _ (by linarith [hx.1])
    apply Real.log_nonneg
    linarith [hx.1]
  have hprod : Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
      ≤ (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) * (∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1))) := by
    have hJsum : (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) ≤ ∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1)) := hJ
    have h2 : Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        ≤ (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x) :=
      mul_le_mul_of_nonneg_right h1 hJ0
    have h3 : (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        ≤ (2 * (∑ k ∈ range 26, (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 53 / (1 - (((5 / (96 / 29) : ℚ) - 1) / ((5 / (96 / 29) : ℚ) + 1)) ^ 2) : ℝ) * (∑ j ∈ range 8, ∑ l ∈ range 9, ∑ i ∈ range 10, (((if i = 0 then (2 * (∑ k ∈ range 20, (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ (2 * k + 1) / (2 * k + 1)) + 2 * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 41 / (1 - (((2 + (9 / 29) * (j : ℚ) / 8 - 1) - 1) / ((2 + (9 / 29) * (j : ℚ) / 8 - 1) + 1)) ^ 2)) else if i ≤ 8 then (-1 : ℚ) ^ (i - 1) / ((i : ℚ) * (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) else 2 / (((2 + (9 / 29) * (j : ℚ) / 8 - 1) : ℚ)) ^ i) : ℚ) : ℝ) * (((if l = 0 then (1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8) + ((1 : ℚ) / (2 + (9 / 29) * (j : ℚ) / 8)) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8)) ^ 9 / (1 - (((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8)) - ((2 + (9 / 29) * (j : ℚ) / 8))) / (2 + (9 / 29) * (j : ℚ) / 8))) else (-1 : ℚ) ^ l / (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ)) ^ (l + 1)) : ℚ) : ℝ) * (((((2 + (9 / 29) * ((j + 1 : ℕ) : ℚ) / 8) : ℚ) : ℝ) - (((2 + (9 / 29) * (j : ℚ) / 8) : ℚ) : ℝ)) ^ (i + l + 1) / ((i : ℝ) + (l : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hJsum h5a
    linarith
  have hmain : 8 * (Real.log (5 / (96/29)) +
      (Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        + ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x))
      ≤ ((3891854 / 1000000 : ℚ) : ℝ) := by
    nlinarith [h1, hP, hJ, hc, h5a, hlog0, hJ0, hprod]
  calc 8 * (Real.log (5 / (96/29)) + Real.log (5 / (96/29)) *
        (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
        + ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x)
      = 8 * (Real.log (5 / (96/29)) +
          (Real.log (5 / (96/29)) * (∫ x in (2:ℝ)..(67/29), Real.log (x - 1) / x)
            + ∫ x in (67/29:ℝ)..4, Real.log (x - 1) * Real.log (5 / (x + 1)) / x)) := by ring
    _ ≤ ((3891854 / 1000000 : ℚ) : ℝ) := hmain
    _ = 3.891854 := by norm_num

/-! ### NEW: absolute-value series bounds for centre-free panels -/

private lemma slog_abs {s : ℝ} (hs : |s| ≤ 1 / 2) (n : ℕ) :
    |Real.log (1 + s) - ∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)|
      ≤ 2 * |s| ^ (n + 1) := by
  have hs1 : |s| < 1 := by linarith [abs_nonneg s]
  have h := Real.abs_log_sub_add_sum_range_le (x := -s) (by rwa [abs_neg]) n
  have hsum : (∑ i ∈ range n, (-s) ^ (i + 1) / (i + 1) : ℝ)
      = -(∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [neg_pow]
    have h1 : (-1 : ℝ) ^ (i + 1) = -((-1) ^ i) := by rw [pow_succ]; ring
    rw [h1]; ring
  have h' : |(∑ i ∈ range n, (-s) ^ (i + 1) / (i + 1)) + Real.log (1 + s)|
      ≤ |s| ^ (n + 1) / (1 - |s|) := by
    simpa only [abs_neg, sub_neg_eq_add] using h
  have he : Real.log (1 + s) - ∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)
      = (∑ i ∈ range n, (-s) ^ (i + 1) / (i + 1)) + Real.log (1 + s) := by
    rw [hsum]; ring
  rw [he]
  refine h'.trans ?_
  have hden : (0 : ℝ) < 1 - |s| := by linarith [abs_nonneg s]
  rw [div_le_iff₀ hden]
  nlinarith [abs_nonneg s, pow_nonneg (abs_nonneg s) (n + 1)]

private lemma slog_ge {s : ℝ} (hs : |s| ≤ 1 / 2) (n : ℕ) :
    (∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) - 2 * |s| ^ (n + 1)
      ≤ Real.log (1 + s) := by
  have h := (abs_le.mp (slog_abs hs n)).1
  linarith

private lemma slog_le {s : ℝ} (hs : |s| ≤ 1 / 2) (n : ℕ) :
    Real.log (1 + s) ≤ (∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1))
      + 2 * |s| ^ (n + 1) := by
  have h := (abs_le.mp (slog_abs hs n)).2
  linarith

private lemma geom_abs {u ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hu : |u| ≤ ρ) (L : ℕ) :
    |(∑ l ∈ range L, u ^ l) - 1 / (1 - u)| ≤ ρ ^ L / (1 - ρ) := by
  have hul : |u| < 1 := lt_of_le_of_lt hu hρ1
  have hu1 : u < 1 := lt_of_le_of_lt (le_abs_self u) hul
  have hne : (1 : ℝ) - u ≠ 0 := by linarith
  have hpos : (0 : ℝ) < 1 - u := by linarith
  have hrhopos : (0 : ℝ) < 1 - ρ := by linarith
  have hsum : (∑ l ∈ range L, u ^ l) = (1 - u ^ L) / (1 - u) := by
    rw [eq_div_iff hne]
    have hm := geom_sum_mul u L
    nlinarith [hm]
  have hval : (∑ l ∈ range L, u ^ l) - 1 / (1 - u) = -(u ^ L / (1 - u)) := by
    rw [hsum]
    field_simp
    ring
  rw [hval, abs_neg, abs_div, abs_pow, abs_of_pos hpos]
  have h2 : |u| ^ L ≤ ρ ^ L := pow_le_pow_left₀ (abs_nonneg u) hu L
  refine le_trans (div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg u) L) hrhopos ?_)
    (div_le_div_of_nonneg_right h2 hrhopos.le)
  linarith [le_abs_self u]

private lemma rgeom_abs {c d : ℝ} (hc : 0 < c) (hd0 : 0 ≤ d) (hd : d ≤ c / 2) (L : ℕ)
    {t : ℝ} (ht : |t| ≤ d) :
    |1 / (c + t) - (1 / c) * (∑ l ∈ range L, (-(t / c)) ^ l)|
      ≤ (1 / c) * ((d / c) ^ L / (1 - d / c)) := by
  have hcne : c ≠ 0 := hc.ne'
  have htle : t ≤ d := le_trans (le_abs_self t) ht
  have htge : -d ≤ t := (abs_le.mp ht).1
  have hdc : d < c := by linarith
  have hcp : (0 : ℝ) < c + t := by linarith
  have hρ0 : 0 ≤ d / c := div_nonneg hd0 hc.le
  have hρ1 : d / c < 1 := by rw [div_lt_one hc]; linarith
  have hu : |-(t / c)| ≤ d / c := by
    rw [abs_neg, abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right ht hc.le
  have h := geom_abs hρ0 hρ1 hu L
  have h1 : (1 : ℝ) - -(t / c) = (c + t) / c := by
    field_simp
    ring
  have hrw : 1 / (c + t) = (1 / c) * (1 / (1 - -(t / c))) := by
    have hcne : c ≠ 0 := hc.ne'
    have hcpne : c + t ≠ 0 := ne_of_gt hcp
    calc 1 / (c + t) = (1 / c) * ((c : ℝ) / (c + t)) := by field_simp <;> ring
      _ = (1 / c) * (1 / (1 - -(t / c))) := by rw [h1, one_div_div]
  have h' : |1 / (1 - -(t / c)) - ∑ l ∈ range L, (-(t / c)) ^ l| ≤ (d / c) ^ L / (1 - d / c) := by
    rw [abs_sub_comm]; exact h
  have hmul : (1 / c) * (1 / (1 - -(t / c))) - (1 / c) * (∑ l ∈ range L, (-(t / c)) ^ l)
      = (1 / c) * (1 / (1 - -(t / c)) - ∑ l ∈ range L, (-(t / c)) ^ l) := by ring
  rw [hrw, hmul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / c)]
  exact mul_le_mul_of_nonneg_left h' (le_of_lt (by positivity : (0 : ℝ) < 1 / c))

private lemma ipow_c (p q c : ℝ) (n : ℕ) :
    (∫ x in p..q, (x - c) ^ n) = ((q - c) ^ (n + 1) - (p - c) ^ (n + 1)) / (n + 1) := by
  have h := intervalIntegral.integral_comp_sub_right (a := p) (b := q) (fun y : ℝ => y ^ n) c
  simp only [integral_pow] at h
  rw [h]

private lemma iprod3_c (p q c : ℝ) (hpq : p ≤ q) (A B C : ℕ → ℝ) (na nb nc : ℕ) :
    (∫ x in p..q, (∑ i ∈ range na, A i * (x - c) ^ i) * (∑ j ∈ range nb, B j * (x - c) ^ j) *
        (∑ l ∈ range nc, C l * (x - c) ^ l))
      = ∑ l ∈ range nc, ∑ j ∈ range nb, ∑ i ∈ range na,
          A i * B j * C l * (((q - c) ^ (i + j + l + 1) - (p - c) ^ (i + j + l + 1)) /
            ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)) := by
  have hcongr : (∫ x in p..q, (∑ i ∈ range na, A i * (x - c) ^ i) *
      (∑ j ∈ range nb, B j * (x - c) ^ j) * (∑ l ∈ range nc, C l * (x - c) ^ l))
      = ∫ x in p..q, (∑ l ∈ range nc, ∑ j ∈ range nb, ∑ i ∈ range na,
          A i * B j * C l * (x - c) ^ (i + j + l)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact poly3_eq c x A B C na nb nc
  rw [hcongr, intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [intervalIntegral.integral_const_mul, ipow_c]
        push_cast
        ring
      · intro i _
        exact (by fun_prop : Continuous fun x : ℝ =>
          A i * B j * C l * (x - c) ^ (i + j + l)).intervalIntegrable _ _
    · intro j _
      exact (by fun_prop : Continuous fun x : ℝ =>
        ∑ i ∈ range na, A i * B j * C l * (x - c) ^ (i + j + l)).intervalIntegrable _ _
  · intro l _
    exact (by fun_prop : Continuous fun x : ℝ =>
      ∑ j ∈ range nb, ∑ i ∈ range na, A i * B j * C l * (x - c) ^ (i + j + l)).intervalIntegrable _ _

private lemma neg_div_pow (t c : ℝ) (n : ℕ) : (-(t / c)) ^ n = (-1 : ℝ) ^ n * (t ^ n / c ^ n) := by
  rw [show (-(t / c)) = (-1) * (t / c) by ring, mul_pow, div_pow]

private lemma mul_div_pow (A t c : ℝ) (n : ℕ) : (A / c) ^ n * t ^ n = (A * t / c) ^ n := by
  rw [← mul_pow]; ring

private lemma six_one_div_mul {x : ℝ} (hx : x ≠ 0) (hX : 6 - 12 * x ≠ 0) :
    1 / (x * (6 - 12 * x)) = (1 / 6 : ℝ) * (1 / x) + 2 * (1 / (6 - 12 * x)) := by
  have h1 : (1 / 6 : ℝ) * (1 / x) = 1 / (6 * x) := by
    field_simp
  have h2 : 2 * (1 / (6 - 12 * x)) = 2 / (6 - 12 * x) := by
    rw [one_div]
    ring
  rw [h1, h2, div_add_div _ _ (mul_ne_zero (by norm_num) hx) hX]
  have hnum : (1 * (6 - 12 * x) + 6 * x * 2 : ℝ) = 6 := by ring
  rw [hnum]
  field_simp <;> ring_nf

private lemma one_div_c_cancel {c x : ℝ} (hc : c ≠ 0) (hx : x ≠ 0) :
    (1 / 6 : ℝ) * (1 / c) * (c / x) = (1 / 6) * (1 / x) := by
  field_simp <;> ring_nf

private lemma six_c_cancel {c x : ℝ} (hc : 6 - 12 * c ≠ 0) (hx : 6 - 12 * x ≠ 0) :
    (2 / (6 - 12 * c)) * ((6 - 12 * c) / (6 - 12 * x)) = 2 * (1 / (6 - 12 * x)) := by
  field_simp <;> ring_nf

/-! ### NEW: generic panel bound, lower direction -/

private lemma panel_low (p q c d a r eB lA lB mlA : ℚ) (na nb nc : ℕ)
    (hpq : p ≤ q) (hpc : p ≤ c) (hcq : c ≤ q)
    (hp16 : 1 / 6 ≤ p) (hq3 : q ≤ 1 / 3)
    (hd0 : 0 ≤ d) (hdp : c - p ≤ d) (hdq : q - c ≤ d)
    (hGA1 : 1 ≤ 5 - 12 * c) (hGB : 0 < c - a) (hr0 : 0 < r) (hap : a < p)
    (hdist : d ≤ (c - a) / 2) (hdist2 : d ≤ c / 2) (hdist3 : 12 * d ≤ (5 - 12 * c) / 2)
    (hlAlo : (lA : ℝ) ≤ Real.log (5 - 12 * (c : ℝ)))
    (hlAhi : Real.log (5 - 12 * (c : ℝ)) ≤ (lA : ℝ) + 1 / 1000000)
    (hmlA : (mlA : ℝ) ≤ Real.log (((5 - 12 * q : ℚ) : ℝ))) (hmlA0 : 0 ≤ mlA)
    (hminA : 4 * ((12 * (d : ℝ)) / (5 - 12 * (c : ℝ))) ^ (na + 1) + 1 / 1000000 ≤ (mlA : ℝ))
    (hlB : (eB : ℝ) * ((lB : ℝ) - Real.log ((((c - a) / r : ℚ)) : ℝ)) ≤ 0)
    (heB : eB = 1 ∨ eB = -1)
    (hfB : ∀ x ∈ Set.Icc (p : ℝ) (q : ℝ), 0 ≤ (eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ)))
    (hnc : 1 ≤ nc)
    (htail : (1 / 6) / (c : ℝ) * (((d : ℝ) / (c : ℝ)) ^ (nc + 1) / (1 - (d : ℝ) / (c : ℝ)))
        + 2 / (6 - 12 * (c : ℝ)) *
            (((12 * (d : ℝ)) / (6 - 12 * (c : ℝ))) ^ (nc + 1) /
              (1 - 12 * (d : ℝ) / (6 - 12 * (c : ℝ)))) ≤ 1 / 10) :
    (∑ l ∈ range (nc + 1), ∑ j ∈ range (nb + 1), ∑ i ∈ range (na + 1),
        (((if i = 0 then lA - 2 * ((12*d)/(5 - 12*c))^(na+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/(5-12*c))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then eB*lB - 2 * (d/(c - a))^(nb+1) else eB * (-1 : ℚ)^(j-1) * ((1:ℚ)/(c - a))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/c + 2/(6 - 12*c) - ((1:ℚ)/6/c * ((d/c)^(nc+1)/(1 - d/c)) + 2/(6 - 12*c) * ((12*d/(6 - 12*c))^(nc+1)/(1 - 12*d/(6 - 12*c)))) else (1:ℚ)/6 * (-1 : ℚ)^l / c^(l+1) + (2/(6-12*c)) * ((12:ℚ)/(6-12*c))^l) : ℚ) : ℝ) *
          ((((q : ℝ) - (c : ℝ)) ^ (i + j + l + 1) - ((p : ℝ) - (c : ℝ)) ^ (i + j + l + 1)) /
            ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)))
      ≤ ∫ x in (p : ℝ)..(q : ℝ),
          Real.log (5 - 12 * x) * ((eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ))) /
            ((6 - 12 * x) * x) := by
  have hpqR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
  have hp16R : (1 : ℝ) / 6 ≤ (p : ℝ) := by
    have h : ((1 / 6 : ℚ) : ℝ) ≤ ((p : ℚ) : ℝ) := by exact_mod_cast hp16
    simpa using h
  have hq3R : (q : ℝ) ≤ 1 / 3 := by
    have h : ((q : ℚ) : ℝ) ≤ ((1 / 3 : ℚ) : ℝ) := by exact_mod_cast hq3
    simpa using h
  have hpcR : (p : ℝ) ≤ (c : ℝ) := by exact_mod_cast hpc
  have hcqR : (c : ℝ) ≤ (q : ℝ) := by exact_mod_cast hcq
  have hc13 : (c : ℝ) ≤ 1 / 3 := le_trans hcqR hq3R
  have hp0R : (0 : ℝ) < (p : ℝ) := by linarith
  have hc0 : (0 : ℝ) < (c : ℝ) := by linarith
  have hd0R : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
  have hdpR : (c : ℝ) - (p : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdp
  have hdqR : (q : ℝ) - (c : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdq
  have hGA1R : (1 : ℝ) ≤ 5 - 12 * (c : ℝ) := by
    have h : ((1 : ℚ) : ℝ) ≤ ((5 - 12 * c : ℚ) : ℝ) := by exact_mod_cast hGA1
    simpa using h
  have hGA0 : (0 : ℝ) < 5 - 12 * (c : ℝ) := by linarith
  have hGB0 : (0 : ℝ) < (c : ℝ) - (a : ℝ) := by
    have h : ((0 : ℚ) : ℝ) < ((c - a : ℚ) : ℝ) := by exact_mod_cast hGB
    simpa using h
  have hGC0 : (0 : ℝ) < 6 - 12 * (c : ℝ) := by linarith
  have hr0R : (0 : ℝ) < (r : ℝ) := by
    have h : ((0 : ℚ) : ℝ) < ((r : ℚ) : ℝ) := by exact_mod_cast hr0
    simpa using h
  have hapR : (a : ℝ) < (p : ℝ) := by
    have h : ((a : ℚ) : ℝ) < ((p : ℚ) : ℝ) := by exact_mod_cast hap
    simpa using h
  have hdistR : (d : ℝ) ≤ ((c : ℝ) - (a : ℝ)) / 2 := by
    have h : ((d : ℚ) : ℝ) ≤ (((c - a) / 2 : ℚ) : ℝ) := by exact_mod_cast hdist
    simpa using h
  have hdist2R : (d : ℝ) ≤ (c : ℝ) / 2 := by
    have h : ((d : ℚ) : ℝ) ≤ ((c / 2 : ℚ) : ℝ) := by exact_mod_cast hdist2
    simpa using h
  have hdist3R : 12 * (d : ℝ) ≤ (5 - 12 * (c : ℝ)) / 2 := by
    have h : ((12 * d : ℚ) : ℝ) ≤ (((5 - 12 * c) / 2 : ℚ) : ℝ) := by exact_mod_cast hdist3
    simpa using h
  set A : ℕ → ℝ := fun i => (((if i = 0 then lA - 2 * ((12*d)/(5 - 12*c))^(na+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/(5-12*c))^i / (i:ℚ)) : ℚ) : ℝ) with hAc
  set B : ℕ → ℝ := fun j => (((if j = 0 then eB*lB - 2 * (d/(c - a))^(nb+1) else eB * (-1 : ℚ)^(j-1) * ((1:ℚ)/(c - a))^j / (j:ℚ)) : ℚ) : ℝ) with hBc
  set C : ℕ → ℝ := fun l => (((if l = 0 then (1:ℚ)/6/c + 2/(6 - 12*c) - ((1:ℚ)/6/c * ((d/c)^(nc+1)/(1 - d/c)) + 2/(6 - 12*c) * ((12*d/(6 - 12*c))^(nc+1)/(1 - 12*d/(6 - 12*c)))) else (1:ℚ)/6 * (-1 : ℚ)^l / c^(l+1) + (2/(6-12*c)) * ((12:ℚ)/(6-12*c))^l) : ℚ) : ℝ) with hCc
  have hrow : (∑ l ∈ range (nc + 1), ∑ j ∈ range (nb + 1), ∑ i ∈ range (na + 1),
        (((if i = 0 then lA - 2 * ((12*d)/(5 - 12*c))^(na+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/(5-12*c))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then eB*lB - 2 * (d/(c - a))^(nb+1) else eB * (-1 : ℚ)^(j-1) * ((1:ℚ)/(c - a))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/c + 2/(6 - 12*c) - ((1:ℚ)/6/c * ((d/c)^(nc+1)/(1 - d/c)) + 2/(6 - 12*c) * ((12*d/(6 - 12*c))^(nc+1)/(1 - 12*d/(6 - 12*c)))) else (1:ℚ)/6 * (-1 : ℚ)^l / c^(l+1) + (2/(6-12*c)) * ((12:ℚ)/(6-12*c))^l) : ℚ) : ℝ) *
          ((((q : ℝ) - (c : ℝ)) ^ (i + j + l + 1) - ((p : ℝ) - (c : ℝ)) ^ (i + j + l + 1)) /
            ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)))
      = ∑ l ∈ range (nc + 1), ∑ j ∈ range (nb + 1), ∑ i ∈ range (na + 1),
          A i * B j * C l *
            ((((q : ℝ) - (c : ℝ)) ^ (i + j + l + 1) - ((p : ℝ) - (c : ℝ)) ^ (i + j + l + 1)) /
              ((i : ℝ) + (j : ℝ) + (l : ℝ) + 1)) := by
    simp only [hAc, hBc, hCc]
  rw [hrow, ← iprod3_c (p : ℝ) (q : ℝ) (c : ℝ) hpqR A B C (na + 1) (nb + 1) (nc + 1)]
  refine intervalIntegral.integral_mono_on hpqR ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ =>
      (∑ i ∈ range (na + 1), A i * (x - (c : ℝ)) ^ i) *
        (∑ j ∈ range (nb + 1), B j * (x - (c : ℝ)) ^ j) *
        (∑ l ∈ range (nc + 1), C l * (x - (c : ℝ)) ^ l)).intervalIntegrable _ _
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpqR]
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact ContinuousOn.log (by fun_prop) (fun x hx => by linarith [hx.2, hq3R])
      · apply ContinuousOn.mul continuousOn_const
        exact ContinuousOn.log (by fun_prop)
          (fun x hx => ne_of_gt (div_pos (by linarith [hx.1, hapR]) hr0R))
    · exact (by fun_prop : ContinuousOn (fun x : ℝ => (6 - 12 * x) * x) (Set.Icc (p:ℝ) (q:ℝ)))
    · intro x hx
      have h1 : (6 : ℝ) - 12 * x ≠ 0 := by
        have hp : (0 : ℝ) < 6 - 12 * x := by linarith [hx.2, hq3R]
        linarith
      have h2 : x ≠ 0 := by linarith [hx.1, hp16R]
      exact mul_ne_zero h1 h2
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hxp, hxq⟩ := hx
    set t : ℝ := x - (c : ℝ) with htdef
    have ht_lo : -((d : ℝ)) ≤ t := by rw [htdef]; linarith
    have ht_hi : t ≤ (d : ℝ) := by rw [htdef]; linarith
    have htabs : |t| ≤ (d : ℝ) := abs_le.mpr ⟨ht_lo, ht_hi⟩
    have hx16 : (1 : ℝ) / 6 ≤ x := le_trans hp16R hxp
    have hx13 : x ≤ 1 / 3 := le_trans hxq hq3R
    have hx0' : (0 : ℝ) < x := by linarith
    set sA : ℝ := -(12 * t) / (5 - 12 * (c : ℝ)) with hsA
    set sB : ℝ := t / ((c : ℝ) - (a : ℝ)) with hsB
    have hsAabs : |sA| ≤ 12 * (d : ℝ) / (5 - 12 * (c : ℝ)) := by
      have h1 : |sA| = 12 * |t| / (5 - 12 * (c : ℝ)) := by
        rw [hsA, abs_div, abs_of_pos hGA0, abs_neg, abs_mul,
          abs_of_pos (by norm_num : (0:ℝ) < 12)]
      rw [h1]
      exact div_le_div_of_nonneg_right (by linarith [htabs]) hGA0.le
    have hsA12 : |sA| ≤ 1 / 2 := by
      have h2 : 12 * (d : ℝ) / (5 - 12 * (c : ℝ)) ≤ 1 / 2 := by
        rw [div_le_iff₀ hGA0]; linarith
      linarith
    have hsBabs : |sB| ≤ (d : ℝ) / ((c : ℝ) - (a : ℝ)) := by
      rw [hsB, abs_div, abs_of_pos hGB0]
      exact div_le_div_of_nonneg_right htabs hGB0.le
    have hsB12 : |sB| ≤ 1 / 2 := by
      have h2 : (d : ℝ) / ((c : ℝ) - (a : ℝ)) ≤ 1 / 2 := by
        rw [div_le_iff₀ hGB0]; linarith
      linarith
    have h1sA : (0 : ℝ) < 1 + sA := by
      have := neg_abs_le sA; linarith
    have h1sB : (0 : ℝ) < 1 + sB := by
      have := neg_abs_le sB; linarith
    have hlog5 : (5 - 12 * (c : ℝ)) * (1 + sA) = 5 - 12 * x := by
      rw [hsA, htdef]; field_simp; ring
    have hlogA : Real.log (5 - 12 * x)
        = Real.log (5 - 12 * (c : ℝ)) + Real.log (1 + sA) := by
      rw [← hlog5, Real.log_mul (ne_of_gt hGA0) (ne_of_gt h1sA)]
    have hxA : x - (a : ℝ) = ((c : ℝ) - (a : ℝ)) * (1 + sB) := by
      rw [hsB, htdef]; field_simp; ring
    have hlogB : Real.log ((x - (a : ℝ)) / (r : ℝ))
        = Real.log (((c : ℝ) - (a : ℝ)) / (r : ℝ)) + Real.log (1 + sB) := by
      rw [show (x - (a:ℝ))/(r:ℝ) = (((c:ℝ)-(a:ℝ))/(r:ℝ)) * (1 + sB) by rw [hxA]; ring,
        Real.log_mul (by positivity) (ne_of_gt h1sB)]
    have hA0 : A 0 = (lA : ℝ) - 2 * ((12 * (d : ℝ)) / (5 - 12 * (c : ℝ))) ^ (na + 1) := by
      simp only [hAc, ↓reduceIte]
      push_cast
      ring
    have hAstep : ∀ i : ℕ, A (i + 1)
        = (-1 : ℝ) ^ i * (-(12 : ℝ) / (5 - 12 * (c : ℝ))) ^ (i + 1) / ((i : ℝ) + 1) := by
      intro i
      simp only [hAc]
      rw [if_neg (by omega : i + 1 ≠ 0), Nat.succ_sub_one]
      push_cast
      ring
    have hAsum : (∑ i ∈ range na, A (i + 1) * t ^ (i + 1))
        = ∑ i ∈ range na, (-1 : ℝ) ^ i * sA ^ (i + 1) / ((i : ℝ) + 1) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hAstep i]
      have e1 : (-(12 : ℝ) / (5 - 12 * (c : ℝ))) ^ (i + 1) * t ^ (i + 1) = sA ^ (i + 1) := by
        rw [← mul_pow, show (-(12 : ℝ) / (5 - 12 * (c : ℝ))) * t = sA by rw [hsA]; ring]
      calc (-1 : ℝ) ^ i * (-(12 : ℝ) / (5 - 12 * (c : ℝ))) ^ (i + 1) / ((i : ℝ) + 1) * t ^ (i + 1)
          = (-1 : ℝ) ^ i * ((-(12 : ℝ) / (5 - 12 * (c : ℝ))) ^ (i + 1) * t ^ (i + 1)) /
              ((i : ℝ) + 1) := by ring
        _ = (-1 : ℝ) ^ i * sA ^ (i + 1) / ((i : ℝ) + 1) := by rw [e1]
    have hArow : (∑ i ∈ range (na + 1), A i * t ^ i)
        = ((lA : ℝ) - 2 * ((12 * (d : ℝ)) / (5 - 12 * (c : ℝ))) ^ (na + 1))
          + ∑ i ∈ range na, (-1 : ℝ) ^ i * sA ^ (i + 1) / ((i : ℝ) + 1) := by
      rw [Finset.sum_range_succ', hA0, pow_zero, mul_one, hAsum, add_comm]
    have hAle : (∑ i ∈ range (na + 1), A i * t ^ i) ≤ Real.log (5 - 12 * x) := by
      rw [hArow, hlogA]
      have hge := slog_ge hsA12 na
      have hpow : |sA| ^ (na + 1) ≤ (12 * (d : ℝ) / (5 - 12 * (c : ℝ))) ^ (na + 1) :=
        pow_le_pow_left₀ (abs_nonneg sA) hsAabs (na + 1)
      linarith [hge, hpow, hlAlo]
    have hB0 : B 0 = (eB : ℝ) * (lB : ℝ) - 2 * ((d : ℝ) / ((c : ℝ) - (a : ℝ))) ^ (nb + 1) := by
      simp only [hBc, ↓reduceIte]
      push_cast
      ring
    have hBstep : ∀ j : ℕ, B (j + 1)
        = (eB : ℝ) * (-1 : ℝ) ^ j * (1 / ((c : ℝ) - (a : ℝ))) ^ (j + 1) / ((j : ℝ) + 1) := by
      intro j
      simp only [hBc]
      rw [if_neg (by omega : j + 1 ≠ 0), Nat.succ_sub_one]
      push_cast
      ring
    have hBsum : (∑ j ∈ range nb, B (j + 1) * t ^ (j + 1))
        = (eB : ℝ) * ∑ j ∈ range nb, (-1 : ℝ) ^ j * sB ^ (j + 1) / ((j : ℝ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hBstep j]
      have e1 : (1 / ((c : ℝ) - (a : ℝ))) ^ (j + 1) * t ^ (j + 1) = sB ^ (j + 1) := by
        rw [← mul_pow, show (1 / ((c : ℝ) - (a : ℝ))) * t = sB by rw [hsB]; ring]
      calc (eB : ℝ) * (-1 : ℝ) ^ j * (1 / ((c : ℝ) - (a : ℝ))) ^ (j + 1) / ((j : ℝ) + 1) * t ^ (j + 1)
          = (eB : ℝ) * ((-1 : ℝ) ^ j * ((1 / ((c : ℝ) - (a : ℝ))) ^ (j + 1) * t ^ (j + 1))) /
              ((j : ℝ) + 1) := by ring
        _ = (eB : ℝ) * ((-1 : ℝ) ^ j * sB ^ (j + 1)) / ((j : ℝ) + 1) := by rw [e1]
        _ = (eB : ℝ) * ((-1 : ℝ) ^ j * sB ^ (j + 1) / ((j : ℝ) + 1)) := by ring
    have hBrow : (∑ j ∈ range (nb + 1), B j * t ^ j)
        = ((eB : ℝ) * (lB : ℝ) - 2 * ((d : ℝ) / ((c : ℝ) - (a : ℝ))) ^ (nb + 1))
          + (eB : ℝ) * ∑ j ∈ range nb, (-1 : ℝ) ^ j * sB ^ (j + 1) / ((j : ℝ) + 1) := by
      rw [Finset.sum_range_succ', hB0, pow_zero, mul_one, hBsum, add_comm]
    have heB1 : |(eB : ℝ)| = 1 := by
      rcases heB with h | h <;> rw [h] <;> norm_num
    have hBle : (∑ j ∈ range (nb + 1), B j * t ^ j)
        ≤ (eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ)) := by
      rw [hBrow, hlogB]
      have h := slog_abs hsB12 nb
      have hpow : |sB| ^ (nb + 1) ≤ ((d : ℝ) / ((c : ℝ) - (a : ℝ))) ^ (nb + 1) :=
        pow_le_pow_left₀ (abs_nonneg sB) hsBabs (nb + 1)
      set X : ℝ := ∑ j ∈ range nb, (-1 : ℝ) ^ j * sB ^ (j + 1) / ((j : ℝ) + 1) with hX
      have hkey : (eB : ℝ) * X - (eB : ℝ) * Real.log (1 + sB)
          ≤ 2 * ((d : ℝ) / ((c : ℝ) - (a : ℝ))) ^ (nb + 1) := by
        have h1 : (eB : ℝ) * (X - Real.log (1 + sB)) ≤ |X - Real.log (1 + sB)| := by
          calc (eB : ℝ) * (X - Real.log (1 + sB))
              ≤ |(eB : ℝ) * (X - Real.log (1 + sB))| := le_abs_self _
            _ = |X - Real.log (1 + sB)| := by rw [abs_mul, heB1, one_mul]
        have h2 : |X - Real.log (1 + sB)| ≤ 2 * ((d : ℝ) / ((c : ℝ) - (a : ℝ))) ^ (nb + 1) := by
          rw [abs_sub_comm]
          exact h.trans (by linarith)
        nlinarith [h1, h2]
      have hcastB : ((((c - a) / r : ℚ)) : ℝ) = ((c : ℝ) - (a : ℝ)) / (r : ℝ) := by
        push_cast
        ring
      have hlB' : (eB : ℝ) * ((lB : ℝ) - Real.log (((c : ℝ) - (a : ℝ)) / (r : ℝ))) ≤ 0 := by
        rw [← hcastB]
        exact hlB
      linarith [hkey, hlB']
    have hC0 : C 0 = (1/6 : ℝ) * (1 / (c : ℝ)) + 2 / (6 - 12 * (c : ℝ)) - ((((1:ℚ)/6/c * ((d/c)^(nc+1)/(1 - d/c)) + 2/(6 - 12*c) * ((12*d/(6 - 12*c))^(nc+1)/(1 - 12*d/(6 - 12*c)))) : ℚ) : ℝ) := by
      simp only [hCc, ↓reduceIte]
      push_cast
      ring_nf
    have hCstep : ∀ l : ℕ, C (l + 1)
        = (1/6 : ℝ) * (-1 : ℝ) ^ (l + 1) / ((c : ℝ) ^ (l + 1) * (c : ℝ))
          + (2 / (6 - 12 * (c : ℝ))) * (12 / (6 - 12 * (c : ℝ))) ^ (l + 1) := by
      intro l
      simp only [hCc]
      rw [if_neg (by omega : l + 1 ≠ 0)]
      push_cast
      rw [pow_succ]
      ring
    have hCsumL : (∑ l ∈ range nc, C (l + 1) * t ^ (l + 1))
        = ∑ l ∈ range nc, ((1/6 : ℝ) * (1 / (c : ℝ)) * (-(t / (c : ℝ))) ^ (l + 1)
            + (2 / (6 - 12 * (c : ℝ))) * (12 * t / (6 - 12 * (c : ℝ))) ^ (l + 1)) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hCstep l, add_mul]
      have e1 : (1/6 : ℝ) * (-1 : ℝ) ^ (l + 1) / ((c : ℝ) ^ (l + 1) * (c : ℝ)) * t ^ (l + 1)
          = (1/6 : ℝ) * (1 / (c : ℝ)) * (-(t / (c : ℝ))) ^ (l + 1) := by
        rw [neg_div_pow]
        ring
      have e2 : (2 / (6 - 12 * (c : ℝ))) * (12 / (6 - 12 * (c : ℝ))) ^ (l + 1) * t ^ (l + 1)
          = (2 / (6 - 12 * (c : ℝ))) * (12 * t / (6 - 12 * (c : ℝ))) ^ (l + 1) := by
        calc (2 / (6 - 12 * (c : ℝ))) * (12 / (6 - 12 * (c : ℝ))) ^ (l + 1) * t ^ (l + 1)
            = (2 / (6 - 12 * (c : ℝ))) *
                ((12 / (6 - 12 * (c : ℝ))) ^ (l + 1) * t ^ (l + 1)) := by ring
          _ = (2 / (6 - 12 * (c : ℝ))) * (12 * t / (6 - 12 * (c : ℝ))) ^ (l + 1) := by
              rw [mul_div_pow]
      rw [e1, e2]
    have hCpeel : (∑ l ∈ range (nc + 1), C l * t ^ l)
        = ((1/6 : ℝ) * (1 / (c : ℝ)) + 2 / (6 - 12 * (c : ℝ)) - ((((1:ℚ)/6/c * ((d/c)^(nc+1)/(1 - d/c)) + 2/(6 - 12*c) * ((12*d/(6 - 12*c))^(nc+1)/(1 - 12*d/(6 - 12*c)))) : ℚ) : ℝ))
          + ∑ l ∈ range nc, ((1/6 : ℝ) * (1 / (c : ℝ)) * (-(t / (c : ℝ))) ^ (l + 1)
              + (2 / (6 - 12 * (c : ℝ))) * (12 * t / (6 - 12 * (c : ℝ))) ^ (l + 1)) := by
      have hp1 : (∑ l ∈ range (nc + 1), C l * t ^ l)
          = C 0 + ∑ l ∈ range nc, C (l + 1) * t ^ (l + 1) := by
        rw [Finset.sum_range_succ', pow_zero, mul_one, add_comm]
      rw [hp1, hC0, hCsumL, Finset.sum_add_distrib]
    have hCcomb : (∑ l ∈ range (nc + 1), C l * t ^ l)
        = (1/6 : ℝ) * (1 / (c : ℝ)) * (∑ l ∈ range (nc + 1), (-(t / (c : ℝ))) ^ l)
          + (2 / (6 - 12 * (c : ℝ))) *
              (∑ l ∈ range (nc + 1), (12 * t / (6 - 12 * (c : ℝ))) ^ l)
          - ((((1:ℚ)/6/c * ((d/c)^(nc+1)/(1 - d/c)) + 2/(6 - 12*c) * ((12*d/(6 - 12*c))^(nc+1)/(1 - 12*d/(6 - 12*c)))) : ℚ) : ℝ) := by
      have hd : (∑ l ∈ range nc, ((1/6 : ℝ) * (1 / (c : ℝ)) * (-(t / (c : ℝ))) ^ (l + 1)
              + (2 / (6 - 12 * (c : ℝ))) * (12 * t / (6 - 12 * (c : ℝ))) ^ (l + 1)))
          = (1/6 : ℝ) * (1 / (c : ℝ)) * (∑ l ∈ range nc, (-(t / (c : ℝ))) ^ (l + 1))
            + (2 / (6 - 12 * (c : ℝ))) * (∑ l ∈ range nc, (12 * t / (6 - 12 * (c : ℝ))) ^ (l + 1)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have g1 : (∑ l ∈ range (nc + 1), (-(t / (c : ℝ))) ^ l)
          = 1 + ∑ l ∈ range nc, (-(t / (c : ℝ))) ^ (l + 1) := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
      have g2 : (∑ l ∈ range (nc + 1), (12 * t / (6 - 12 * (c : ℝ))) ^ l)
          = 1 + ∑ l ∈ range nc, (12 * t / (6 - 12 * (c : ℝ))) ^ (l + 1) := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
      rw [hCpeel, hd, g1, g2]
      ring
    have hu1 : |-(t / (c : ℝ))| ≤ (d : ℝ) / (c : ℝ) := by
      rw [abs_neg, abs_div, abs_of_pos hc0]
      exact div_le_div_of_nonneg_right htabs hc0.le
    have hu2 : |12 * t / (6 - 12 * (c : ℝ))| ≤ 12 * (d : ℝ) / (6 - 12 * (c : ℝ)) := by
      have h1 : |12 * t / (6 - 12 * (c : ℝ))| = 12 * |t| / (6 - 12 * (c : ℝ)) := by
        rw [abs_div, abs_mul, abs_of_pos hGC0, abs_of_pos (by norm_num : (0:ℝ) < 12)]
      rw [h1]
      exact div_le_div_of_nonneg_right (by linarith [htabs]) hGC0.le
    have hρ1 : (d : ℝ) / (c : ℝ) < 1 := by
      rw [div_lt_one hc0]; linarith
    have hρ2 : 12 * (d : ℝ) / (6 - 12 * (c : ℝ)) < 1 := by
      rw [div_lt_one hGC0]; linarith [hGA1R]
    have hg1 := geom_abs (u := -(t / (c : ℝ))) (ρ := (d : ℝ) / (c : ℝ))
      (div_nonneg hd0R hc0.le) hρ1 hu1 (nc + 1)
    have hg2 := geom_abs (u := 12 * t / (6 - 12 * (c : ℝ))) (ρ := 12 * (d : ℝ) / (6 - 12 * (c : ℝ)))
      (div_nonneg (mul_nonneg (by norm_num) hd0R) hGC0.le) hρ2 hu2 (nc + 1)
    have hxg1 : (1 : ℝ) / (1 - -(t / (c : ℝ))) = (c : ℝ) / x := by
      have h1 : (1 : ℝ) - -(t / (c : ℝ)) = x / (c : ℝ) := by
        rw [htdef]
        have hcne : (c : ℝ) ≠ 0 := ne_of_gt hc0
        field_simp <;> ring
      rw [h1, one_div_div]
    have hxg2 : (1 : ℝ) / (1 - 12 * t / (6 - 12 * (c : ℝ)))
        = (6 - 12 * (c : ℝ)) / (6 - 12 * x) := by
      have h1 : (1 : ℝ) - 12 * t / (6 - 12 * (c : ℝ)) = (6 - 12 * x) / (6 - 12 * (c : ℝ)) := by
        rw [htdef]
        have h1ne : (6 - 12 * (c : ℝ)) ≠ 0 := ne_of_gt hGC0
        field_simp <;> ring
      rw [h1, one_div_div]
    have hc1 : (0 : ℝ) ≤ (1/6 : ℝ) * (1 / (c : ℝ)) :=
      mul_nonneg (by norm_num) (le_of_lt (one_div_pos.mpr hc0))
    have hc2 : (0 : ℝ) ≤ 2 / (6 - 12 * (c : ℝ)) := div_nonneg (by norm_num) hGC0.le
    have htailR : ((((1:ℚ)/6/c * ((d/c)^(nc+1)/(1 - d/c)) + 2/(6 - 12*c) * ((12*d/(6 - 12*c))^(nc+1)/(1 - 12*d/(6 - 12*c)))) : ℚ) : ℝ) ≤ 1 / 10 := by
      have h := htail
      push_cast at h ⊢
      linarith
    have hA1 : (1/6 : ℝ) * (1 / (c : ℝ)) * (1 / (1 - -(t / (c : ℝ)))) = (1/6) * (1/x) := by
      rw [hxg1, one_div_c_cancel (ne_of_gt hc0) (ne_of_gt hx0')]
    have hA2 : (2 / (6 - 12 * (c : ℝ))) * (1 / (1 - 12 * t / (6 - 12 * (c : ℝ))))
        = 2 * (1 / (6 - 12 * x)) := by
      rw [hxg2, six_c_cancel (ne_of_gt hGC0) (by
        have h : (0:ℝ) < 6 - 12 * x := by linarith
        linarith)]
    have hpf : (1/6 : ℝ) * (1/x) + 2 * (1 / (6 - 12 * x)) = 1 / (x * (6 - 12 * x)) := by
      rw [six_one_div_mul (ne_of_gt hx0') (by
        have h : (0:ℝ) < 6 - 12 * x := by linarith
        linarith)]
    have hTQcast : ((((1:ℚ)/6/c * ((d/c)^(nc+1)/(1 - d/c)) + 2/(6 - 12*c) * ((12*d/(6 - 12*c))^(nc+1)/(1 - 12*d/(6 - 12*c)))) : ℚ) : ℝ)
        = (1/6 : ℝ) * (1 / (c : ℝ)) * (((d : ℝ) / (c : ℝ)) ^ (nc + 1) / (1 - (d : ℝ) / (c : ℝ)))
          + (2 / (6 - 12 * (c : ℝ))) * (((12 * (d : ℝ)) / (6 - 12 * (c : ℝ))) ^ (nc + 1) /
              (1 - 12 * (d : ℝ) / (6 - 12 * (c : ℝ)))) := by
      push_cast
      ring
    have hS1up : (∑ l ∈ range (nc + 1), (-(t / (c : ℝ))) ^ l)
        ≤ (1 / (1 - -(t / (c : ℝ))))
          + ((d : ℝ) / (c : ℝ)) ^ (nc + 1) / (1 - (d : ℝ) / (c : ℝ)) := by
      have h := (abs_le.mp hg1).2; linarith
    have hS2up : (∑ l ∈ range (nc + 1), (12 * t / (6 - 12 * (c : ℝ))) ^ l)
        ≤ (1 / (1 - 12 * t / (6 - 12 * (c : ℝ))))
          + (12 * (d : ℝ) / (6 - 12 * (c : ℝ))) ^ (nc + 1) /
              (1 - 12 * (d : ℝ) / (6 - 12 * (c : ℝ))) := by
      have h := (abs_le.mp hg2).2; linarith
    have hS1lo : (1 / (1 - -(t / (c : ℝ))))
          - ((d : ℝ) / (c : ℝ)) ^ (nc + 1) / (1 - (d : ℝ) / (c : ℝ))
        ≤ (∑ l ∈ range (nc + 1), (-(t / (c : ℝ))) ^ l) := by
      have h := (abs_le.mp hg1).1; linarith
    have hS2lo : (1 / (1 - 12 * t / (6 - 12 * (c : ℝ))))
          - (12 * (d : ℝ) / (6 - 12 * (c : ℝ))) ^ (nc + 1) /
              (1 - 12 * (d : ℝ) / (6 - 12 * (c : ℝ)))
        ≤ (∑ l ∈ range (nc + 1), (12 * t / (6 - 12 * (c : ℝ))) ^ l) := by
      have h := (abs_le.mp hg2).1; linarith
    have hcle : (∑ l ∈ range (nc + 1), C l * t ^ l) ≤ 1 / (x * (6 - 12 * x)) := by
      rw [hCcomb]
      have hm1 := mul_le_mul_of_nonneg_left hS1up hc1
      have hm2 := mul_le_mul_of_nonneg_left hS2up hc2
      linarith [hm1, hm2, hA1, hA2, hpf, htailR, hTQcast]
    have hCnonneg : 0 ≤ ∑ l ∈ range (nc + 1), C l * t ^ l := by
      rw [hCcomb]
      have hm1 := mul_le_mul_of_nonneg_left hS1lo hc1
      have hm2 := mul_le_mul_of_nonneg_left hS2lo hc2
      have hCx : (4/3 : ℝ) ≤ 1 / (x * (6 - 12 * x)) := by
        have hden : (0 : ℝ) < x * (6 - 12 * x) := mul_pos hx0' (by linarith)
        rw [le_div_iff₀ hden]
        nlinarith [sq_nonneg (4 * x - 1), hden]
      linarith [hm1, hm2, hCx, hpf, hA1, hA2, htailR, hTQcast]
    have hAnonneg : 0 ≤ ∑ i ∈ range (na + 1), A i * t ^ i := by
      rw [hArow]
      have hge := slog_le hsA12 na
      have hpow : |sA| ^ (na + 1) ≤ (12 * (d : ℝ) / (5 - 12 * (c : ℝ))) ^ (na + 1) :=
        pow_le_pow_left₀ (abs_nonneg sA) hsAabs (na + 1)
      have hlogq : Real.log (5 - 12 * (q : ℝ)) ≤ Real.log (5 - 12 * (c : ℝ)) + Real.log (1 + sA) := by
        rw [← hlogA]
        apply Real.log_le_log (by linarith)
        linarith
      have hmlA' : (mlA : ℝ) ≤ Real.log (5 - 12 * (q : ℝ)) := by
        have h := hmlA
        rw [show (((5 - 12 * q : ℚ) : ℝ)) = 5 - 12 * (q : ℝ) from by push_cast; ring] at h
        exact h
      linarith [hge, hpow, hlAhi, hmlA', hminA, hlogq]
    have hfA : 0 ≤ Real.log (5 - 12 * x) := by
      apply Real.log_nonneg; linarith
    have hfBx : 0 ≤ (eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ)) := hfB x ⟨hxp, hxq⟩
    have hfC : 0 ≤ 1 / (x * (6 - 12 * x)) := by
      have hden : (0 : ℝ) < x * (6 - 12 * x) := mul_pos hx0' (by linarith)
      exact le_of_lt (one_div_pos.mpr hden)
    have hkey : Real.log (5 - 12 * x) * ((eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ))) /
          ((6 - 12 * x) * x)
        = Real.log (5 - 12 * x) * ((eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ))) *
            (1 / (x * (6 - 12 * x))) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring_nf
    rw [hkey]
    by_cases hBnn : 0 ≤ ∑ j ∈ range (nb + 1), B j * t ^ j
    · have h1 : (∑ i ∈ range (na + 1), A i * t ^ i) * (∑ j ∈ range (nb + 1), B j * t ^ j)
          ≤ Real.log (5 - 12 * x) * (∑ j ∈ range (nb + 1), B j * t ^ j) :=
        mul_le_mul_of_nonneg_right hAle hBnn
      have h2 : (∑ i ∈ range (na + 1), A i * t ^ i) * (∑ j ∈ range (nb + 1), B j * t ^ j) *
            (∑ l ∈ range (nc + 1), C l * t ^ l)
          ≤ Real.log (5 - 12 * x) * (∑ j ∈ range (nb + 1), B j * t ^ j) *
            (∑ l ∈ range (nc + 1), C l * t ^ l) :=
        mul_le_mul_of_nonneg_right h1 hCnonneg
      have h3 : Real.log (5 - 12 * x) * (∑ j ∈ range (nb + 1), B j * t ^ j)
          ≤ Real.log (5 - 12 * x) * ((eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ))) :=
        mul_le_mul_of_nonneg_left hBle hfA
      have h4 : Real.log (5 - 12 * x) * (∑ j ∈ range (nb + 1), B j * t ^ j) *
            (∑ l ∈ range (nc + 1), C l * t ^ l)
          ≤ Real.log (5 - 12 * x) * ((eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ))) *
            (∑ l ∈ range (nc + 1), C l * t ^ l) :=
        mul_le_mul_of_nonneg_right h3 hCnonneg
      have h5 : Real.log (5 - 12 * x) * ((eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ))) *
            (∑ l ∈ range (nc + 1), C l * t ^ l)
          ≤ Real.log (5 - 12 * x) * ((eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ))) *
            (1 / (x * (6 - 12 * x))) :=
        mul_le_mul_of_nonneg_left hcle (mul_nonneg hfA hfBx)
      exact le_trans h2 (le_trans h4 h5)
    · have hBlt : (∑ j ∈ range (nb + 1), B j * t ^ j) < 0 := not_le.mp hBnn
      have hAC : 0 ≤ (∑ i ∈ range (na + 1), A i * t ^ i) * (∑ l ∈ range (nc + 1), C l * t ^ l) :=
        mul_nonneg hAnonneg hCnonneg
      have hzero : (∑ i ∈ range (na + 1), A i * t ^ i) * (∑ j ∈ range (nb + 1), B j * t ^ j) *
            (∑ l ∈ range (nc + 1), C l * t ^ l) ≤ 0 := by
        rw [show (∑ i ∈ range (na + 1), A i * t ^ i) * (∑ j ∈ range (nb + 1), B j * t ^ j) *
              (∑ l ∈ range (nc + 1), C l * t ^ l)
            = ((∑ i ∈ range (na + 1), A i * t ^ i) * (∑ l ∈ range (nc + 1), C l * t ^ l)) *
              (∑ j ∈ range (nb + 1), B j * t ^ j) from by ring]
        exact mul_nonpos_of_nonneg_of_nonpos hAC hBlt.le
      have hpos : 0 ≤ Real.log (5 - 12 * x) * ((eB : ℝ) * Real.log ((x - (a : ℝ)) / (r : ℝ))) *
          (1 / (x * (6 - 12 * x))) := mul_nonneg (mul_nonneg hfA hfBx) hfC
      exact le_trans hzero hpos
private lemma int_one_div_mul_sub {σ p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q < σ) :
    (∫ u in p..q, 1 / (u * (σ - u))) =
      (Real.log (q / (σ - q)) - Real.log (p / (σ - p))) / σ := by
  have hσ : 0 < σ := by linarith
  have hq0 : 0 < q := hp.trans_le hpq
  have hs : (0:ℝ) < σ - q := by linarith
  have hsp : (0:ℝ) < σ - p := by linarith
  have hi1 : IntervalIntegrable (fun u : ℝ => 1 / u) volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpq]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro u hu; change u ≠ 0; linarith [hu.1]
  have hi2 : IntervalIntegrable (fun u : ℝ => 1 / (σ - u)) volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpq]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u hu; change σ - u ≠ 0; linarith [hu.2]
  have hpt : (∫ u in p..q, 1 / (u * (σ - u)))
      = ∫ u in p..q, (1/σ) * (1/u + 1/(σ-u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hpq] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hsu : σ - u ≠ 0 := by linarith [hu.2]
    field_simp
    ring
  rw [hpt, intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2]
  have e1 : (∫ u in p..q, 1 / u) = Real.log (q / p) := by
    rw [show (∫ u in p..q, 1 / u) = ∫ u in p..q, (u)⁻¹ from by
      apply intervalIntegral.integral_congr; intro u _; rw [one_div]]
    rw [integral_inv_of_pos hp hq0]
  have e2 : (∫ u in p..q, 1 / (σ - u)) = Real.log ((σ - p) / (σ - q)) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun v : ℝ => (v)⁻¹) σ
      (a := p) (b := q)
    rw [show (σ:ℝ) - q = σ - q by ring, show (σ:ℝ) - p = σ - p by ring] at hcomp
    rw [integral_inv_of_pos hs hsp] at hcomp
    rw [show (∫ u in p..q, 1 / (σ - u)) = ∫ u in p..q, ((fun v : ℝ => (v)⁻¹) (σ - u)) from by
      apply intervalIntegral.integral_congr; intro u _; simp only [one_div]]
    rw [hcomp]
  rw [e1, e2]
  have key : Real.log (q / p) + Real.log ((σ - p) / (σ - q))
      = Real.log (q / (σ - q)) - Real.log (p / (σ - p)) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [key]
  ring

/-- The inner substitution `σ = t + u` of the `F4` integral. -/
private lemma F4_inner_subst (t : ℝ) :
    (∫ u in t..(29/250), Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u))
      = ∫ σ in (2*t)..(t + 29/250),
          Real.log (5 - 12*σ) / ((6 - 12*σ) * (σ - t)) := by
  have h := intervalIntegral.integral_comp_add_right (a := t) (b := (29/250 : ℝ)) (d := t)
    (f := fun y : ℝ => Real.log (5 - 12*y) / ((6 - 12*y) * (y - t)))
  have hL : (∫ u in t..(29/250), Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u))
      = ∫ u in t..(29/250),
          (fun y : ℝ => Real.log (5 - 12*y) / ((6 - 12*y) * (y - t))) (u + t) := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only []
    rw [show (5:ℝ) - 12*(u+t) = 5 - 12*(t+u) by ring,
      show (6:ℝ) - 12*(u+t) = 6 - 12*(t+u) by ring,
      show (u + t - t : ℝ) = u by ring]
  rw [hL, h]
  rw [show t + t = 2*t by ring, show (29/250:ℝ) + t = t + 29/250 by ring]

/-- The same substitution for `F5`'s inner integral. -/
private lemma F5_inner_subst (t : ℝ) :
    (∫ u in (29/250)..(1/3 - t), Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u))
      = ∫ σ in (t + 29/250)..(1/3),
          Real.log (5 - 12*σ) / ((6 - 12*σ) * (σ - t)) := by
  have h := intervalIntegral.integral_comp_add_right (a := (29/250 : ℝ)) (b := 1/3 - t) (d := t)
    (f := fun y : ℝ => Real.log (5 - 12*y) / ((6 - 12*y) * (y - t)))
  have hL : (∫ u in (29/250)..(1/3 - t), Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u))
      = ∫ u in (29/250)..(1/3 - t),
          (fun y : ℝ => Real.log (5 - 12*y) / ((6 - 12*y) * (y - t))) (u + t) := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only []
    rw [show (5:ℝ) - 12*(u+t) = 5 - 12*(t+u) by ring,
      show (6:ℝ) - 12*(u+t) = 6 - 12*(t+u) by ring,
      show (u + t - t : ℝ) = u by ring]
  rw [hL, h]
  rw [show (29/250:ℝ) + t = t + 29/250 by ring, show (1/3:ℝ) - t + t = 1/3 by ring]

open LeanLab.ChenDoubleSieve.Task275

/-! ### New in this session: the `σ = t + u` slice machinery for `F4`/`F5` -/

private lemma int_indicator_le {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (f : ℝ → ℝ) :
    (∫ x in a..b, (if x ≤ c then f x else 0)) = ∫ x in a..c, f x := by
  have h := intervalIntegral.integral_indicator (μ := volume) (f := f) (a₁ := a) (a₂ := c) (a₃ := b)
    ⟨hac, hcb⟩
  rw [← h]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Set.indicator, Set.mem_ofPred_eq]

private lemma int_indicator_ge {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (f : ℝ → ℝ) :
    (∫ x in a..b, (if c ≤ x then f x else 0)) = ∫ x in c..b, f x := by
  have key : ∀ x : ℝ, (if c ≤ x then f x else 0)
      = (fun y : ℝ => if y ≤ a + b - c then f (a + b - y) else 0) (a + b - x) := by
    intro x
    show (if c ≤ x then f x else 0)
      = (if a + b - x ≤ a + b - c then f (a + b - (a + b - x)) else 0)
    have hx : a + b - (a + b - x) = x := by ring
    rw [hx]
    by_cases h : c ≤ x
    · have h2 : a + b - x ≤ a + b - c := by linarith
      rw [if_pos h, if_pos h2]
    · have h2 : ¬ (a + b - x ≤ a + b - c) := by linarith
      rw [if_neg h, if_neg h2]
  rw [show (∫ x in a..b, (if c ≤ x then f x else 0))
      = ∫ x in a..b, (fun y : ℝ => if y ≤ a + b - c then f (a + b - y) else 0) (a + b - x) from by
    apply intervalIntegral.integral_congr
    intro x _
    exact key x]
  have h2 : (∫ x in a..b, (fun y : ℝ => if y ≤ a + b - c then f (a + b - y) else 0) (a + b - x))
      = ∫ x in a + b - b..a + b - a,
          (fun y : ℝ => if y ≤ a + b - c then f (a + b - y) else 0) x :=
    intervalIntegral.integral_comp_sub_left
      (f := fun y : ℝ => if y ≤ a + b - c then f (a + b - y) else 0) (d := a + b)
  rw [h2]
  rw [show a + b - b = a from by ring, show a + b - a = b from by ring]
  rw [show (∫ x in a..b, (fun y : ℝ => if y ≤ a + b - c then f (a + b - y) else 0) x)
      = ∫ x in a..b, (if x ≤ a + b - c then f (a + b - x) else 0) from by
    apply intervalIntegral.integral_congr
    intro x _
    rfl]
  rw [int_indicator_le (by linarith : a ≤ a + b - c) (by linarith : a + b - c ≤ b)]
  have h4 : (∫ x in a..a + b - c, f (a + b - x))
      = ∫ x in a + b - (a + b - c)..a + b - a, f x :=
    intervalIntegral.integral_comp_sub_left (f := f) (d := a + b)
  rw [h4]
  rw [show a + b - (a + b - c) = c from by ring, show a + b - a = b from by ring]

/-- Fubini's theorem over the triangle `A ≤ t ≤ B`, `α t + β ≤ x ≤ D`.
The inner integral is elementary in `x` for fixed `x`'s *partner* variable,
so this is the form needed for the `σ = t + u` slices. -/
private lemma swap_affine {H : ℝ → ℝ → ℝ} {A B D α β : ℝ}
    (hα : 0 < α) (hAB : A ≤ B) (hD : α * B + β ≤ D)
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
      (Set.Icc A B ×ˢ Set.Icc (α * A + β) D)) :
    (∫ t in A..B, ∫ x in (α * t + β)..D, H t x)
      = ∫ x in (α * A + β)..D, ∫ t in A..min B ((x - β) / α), H t x := by
  have hcD : α * A + β ≤ D := by nlinarith
  set R : Set (ℝ × ℝ) := Set.Icc A B ×ˢ Set.Icc (α * A + β) D with hRdef
  have hRmeas : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hRcpt : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hScl : IsClosed {p : ℝ × ℝ | α * p.1 + β ≤ p.2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  -- integrability of the indicator extension on the closed rectangle
  have hfin : IsFiniteMeasure (volume.restrict R) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hRcpt.measure_lt_top⟩
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => if α * p.1 + β ≤ p.2 then H p.1 p.2 else 0)
      (volume.restrict R) :=
    (hH.aestronglyMeasurable hRmeas).indicator hScl.measurableSet
  obtain ⟨M, hM⟩ := hRcpt.exists_bound_of_continuousOn hH
  have hbdd : ∀ᵐ p ∂(volume.restrict R),
      ‖(if α * p.1 + β ≤ p.2 then H p.1 p.2 else 0)‖ ≤ max M 0 := by
    filter_upwards [ae_restrict_mem hRmeas] with p hp
    by_cases h : α * p.1 + β ≤ p.2
    · rw [if_pos h]; exact (hM p hp).trans (le_max_left _ _)
    · rw [if_neg h]; simp
  have hint1 : IntegrableOn (fun p : ℝ × ℝ => if α * p.1 + β ≤ p.2 then H p.1 p.2 else 0)
      R := MeasureTheory.Integrable.of_bound hmeas (max M 0) hbdd
  have hInt : IntegrableOn
      (Function.uncurry fun t x : ℝ => if α * t + β ≤ x then H t x else 0)
      (Set.uIoc A B ×ˢ Set.uIoc (α * A + β) D) := by
    refine hint1.mono_set ?_
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    simp only [hRdef, Set.mem_prod, Set.mem_Icc, Set.uIoc, min_eq_left hAB, max_eq_right hAB,
      min_eq_left hcD, max_eq_right hcD, Set.mem_Ioc] at h1 h2 ⊢
    exact ⟨⟨le_of_lt h1.1, h1.2⟩, ⟨le_of_lt h2.1, h2.2⟩⟩
  -- step 1: extend the inner integral to the fixed range
  have hstep1 : (∫ t in A..B, ∫ x in (α * t + β)..D, H t x)
      = ∫ t in A..B, ∫ x in (α * A + β)..D,
          (if α * t + β ≤ x then H t x else 0) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    exact (int_indicator_ge (by nlinarith [ht.1]) (by nlinarith [ht.2]) (fun x => H t x)).symm
  rw [hstep1]
  rw [intervalIntegral_intervalIntegral_swap hInt]
  -- step 2: evaluate the inner `t`-integral
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hcD] at hx
  have hxA : A ≤ (x - β) / α := by
    rw [le_div_iff₀ hα]; nlinarith [hx.1]
  have hcond : ∀ t : ℝ, (α * t + β ≤ x ↔ t ≤ (x - β) / α) := by
    intro t
    rw [le_div_iff₀ hα]
    constructor <;> intro h <;> linarith
  show (∫ t in A..B, (if α * t + β ≤ x then H t x else 0))
      = ∫ t in A..min B ((x - β) / α), H t x
  have hcongr : (∫ t in A..B, (if α * t + β ≤ x then H t x else 0))
      = ∫ t in A..B, (if t ≤ min B ((x - β) / α) then H t x else 0) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    show (if α * t + β ≤ x then H t x else 0)
      = (if t ≤ min B ((x - β) / α) then H t x else 0)
    by_cases h : α * t + β ≤ x
    · have hb : t ≤ B := ht.2
      have hc : t ≤ (x - β) / α := (hcond t).mp h
      rw [if_pos h, if_pos (le_min hb hc)]
    · have hc : ¬ t ≤ min B ((x - β) / α) := by
        intro hlt
        exact h ((hcond t).mpr (le_trans hlt (min_le_right B _)))
      rw [if_neg h, if_neg hc]
  rw [hcongr]
  exact int_indicator_le (le_min hAB hxA) (min_le_left B _) (fun t => H t x)
private lemma intervalIntegrable_param {H : ℝ → ℝ → ℝ} {A B D α β : ℝ}
    (hα : 0 < α) (hAB : A ≤ B) (hD : α * B + β ≤ D)
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
      (Set.Icc A B ×ˢ Set.Icc (α * A + β) D)) :
    IntervalIntegrable (fun t => ∫ x in (α * t + β)..D, H t x) volume A B := by
  have hcD : α * A + β ≤ D := by nlinarith
  set R : Set (ℝ × ℝ) := Set.Icc A B ×ˢ Set.Icc (α * A + β) D with hRdef
  have hRmeas : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hRcpt : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hScl : IsClosed {p : ℝ × ℝ | α * p.1 + β ≤ p.2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hfin : IsFiniteMeasure (volume.restrict R) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hRcpt.measure_lt_top⟩
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => if α * p.1 + β ≤ p.2 then H p.1 p.2 else 0)
      (volume.restrict R) :=
    (hH.aestronglyMeasurable hRmeas).indicator hScl.measurableSet
  obtain ⟨M, hM⟩ := hRcpt.exists_bound_of_continuousOn hH
  have hbdd : ∀ᵐ p ∂(volume.restrict R),
      ‖(if α * p.1 + β ≤ p.2 then H p.1 p.2 else 0)‖ ≤ max M 0 := by
    filter_upwards [ae_restrict_mem hRmeas] with p hp
    by_cases h : α * p.1 + β ≤ p.2
    · rw [if_pos h]; exact (hM p hp).trans (le_max_left _ _)
    · rw [if_neg h]; simp
  have hint1 : IntegrableOn (fun p : ℝ × ℝ => if α * p.1 + β ≤ p.2 then H p.1 p.2 else 0)
      R := MeasureTheory.Integrable.of_bound hmeas (max M 0) hbdd
  have hInt : IntegrableOn
      (Function.uncurry fun t x : ℝ => if α * t + β ≤ x then H t x else 0)
      (Set.uIoc A B ×ˢ Set.uIoc (α * A + β) D) := by
    refine hint1.mono_set ?_
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    simp only [hRdef, Set.mem_prod, Set.mem_Icc, Set.uIoc, min_eq_left hAB, max_eq_right hAB,
      min_eq_left hcD, max_eq_right hcD, Set.mem_Ioc] at h1 h2 ⊢
    exact ⟨⟨le_of_lt h1.1, h1.2⟩, ⟨le_of_lt h2.1, h2.2⟩⟩
  have hInt' : Integrable (Function.uncurry fun t x : ℝ => if α * t + β ≤ x then H t x else 0)
      ((volume.restrict (Set.uIoc A B)).prod (volume.restrict (Set.uIoc (α * A + β) D))) := by
    rw [Measure.prod_restrict]
    exact hInt
  have hfib := hInt'.integral_prod_left
  rw [intervalIntegrable_iff]
  refine hfib.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  simp only [Function.uncurry]
  rw [Set.uIoc_of_le hAB] at ht
  obtain ⟨hlt, hle⟩ := ht
  have ht1 : A ≤ t := le_of_lt hlt
  have ht2 : t ≤ B := hle
  have hstep1 : (∫ x, (if α * t + β ≤ x then H t x else 0)
      ∂(volume.restrict (Set.uIoc (α * A + β) D)))
      = ∫ x in (α * A + β)..D, (if α * t + β ≤ x then H t x else 0) := by
    rw [Set.uIoc_of_le hcD]
    exact (intervalIntegral.integral_of_le hcD).symm
  have hstep2 : (∫ x in (α * A + β)..D, (if α * t + β ≤ x then H t x else 0))
      = ∫ x in (α * t + β)..D, H t x :=
    int_indicator_ge (by nlinarith : α * A + β ≤ α * t + β)
      (by nlinarith : α * t + β ≤ D) (fun x => H t x)
  exact hstep1.trans hstep2


/-- Continuity of the `F4`/`F5` kernel on the rectangles used below. -/
private lemma Hcont {A B C D : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hBC : B < C)
    (hCD : C ≤ D) (hD : 12 * D < 5) :
    ContinuousOn (fun p : ℝ × ℝ => Real.log (5 - 12 * p.2) / ((6 - 12 * p.2) * (p.2 - p.1) * p.1))
      (Set.Icc A B ×ˢ Set.Icc C D) := by
  have hkey : ∀ p ∈ Set.Icc A B ×ˢ Set.Icc C D,
      (0:ℝ) < 5 - 12 * p.2 ∧ (0:ℝ) < 6 - 12 * p.2 ∧ (0:ℝ) < p.2 - p.1 ∧ (0:ℝ) < p.1 := by
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp
    obtain ⟨⟨hp1a, hp1b⟩, hp2a, hp2b⟩ := hp
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine ContinuousOn.div (ContinuousOn.log (by fun_prop) ?_) (by fun_prop) ?_
  · intro p hp
    have := (hkey p hp).1
    intro h
    linarith
  · intro p hp
    obtain ⟨-, h2, h3, h4⟩ := hkey p hp
    have h5 : (0:ℝ) < (6 - 12 * p.2) * (p.2 - p.1) * p.1 := by positivity
    intro h
    linarith [h ▸ h5]

/-- `F4` after the elementary reduction, in terms of `ψ` and the kernel. -/
private lemma F4_form (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) :
    integralTerms F f ω 4 = 48 * (∫ t in kappa1..kappa2,
      (∫ u in t..kappa2, Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u)) / t) := by
  rw [F4_elementary h ω]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  show (∫ u in t..kappa2, Real.log ((1/2 - t - u) / kappa1 - 1) / (((1/2 - t - u) / kappa1) * u)) / t
      = (∫ u in t..kappa2, Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u)) / t
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  show Real.log ((1/2 - t - u) / kappa1 - 1) / (((1/2 - t - u) / kappa1) * u)
      = Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u)
  rw [show (1/2 - t - u) / kappa1 - 1 = 5 - 12*(t+u) by
        norm_num [kappa1]; ring,
      show (1/2 - t - u) / kappa1 = 6 - 12*(t+u) by
        norm_num [kappa1]; ring]


/-! ### `P1` : numerical tools and the rational certificate -/

private lemma log_add_bounds {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    |Real.log (1 + s) - ∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)|
      ≤ 2 * s ^ (n + 1) := by
  have hx : |-s| < 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have hsum : (∑ i ∈ range n, (-s) ^ (i + 1) / (i + 1) : ℝ)
      = -(∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [neg_pow]
    have : (-1 : ℝ) ^ (i + 1) = -((-1) ^ i) := by rw [pow_succ]; ring
    rw [this]; ring
  have h1s : (1 : ℝ) - -s = 1 + s := by ring
  rw [hsum, h1s, abs_neg, abs_of_nonneg h0] at h
  calc |Real.log (1 + s) - ∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)|
      = |-(∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) + Real.log (1 + s)| := by
        rw [neg_add_eq_sub, abs_sub_comm]
    _ ≤ s ^ (n + 1) / (1 - s) := h
    _ ≤ 2 * s ^ (n + 1) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg h0 (n + 1), h0]

private lemma log_add_ge {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    (∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) - 2 * s ^ (n + 1) ≤ Real.log (1 + s) := by
  have h := (abs_le.mp (log_add_bounds h0 h1 n)).1
  linarith

private lemma log_add_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    Real.log (1 + s) ≤ (∑ i ∈ range n, (-1 : ℝ) ^ i * s ^ (i + 1) / (i + 1)) + 2 * s ^ (n + 1) := by
  have h := (abs_le.mp (log_add_bounds h0 h1 n)).2
  linarith

private lemma log_sub_bounds {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    |Real.log (1 - s) + ∑ i ∈ range n, s ^ (i + 1) / (i + 1)| ≤ 2 * s ^ (n + 1) := by
  have hx : |s| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0] at h
  calc |Real.log (1 - s) + ∑ i ∈ range n, s ^ (i + 1) / (i + 1)|
      = |(∑ i ∈ range n, s ^ (i + 1) / (i + 1)) + Real.log (1 - s)| := by rw [add_comm]
    _ ≤ s ^ (n + 1) / (1 - s) := h
    _ ≤ 2 * s ^ (n + 1) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg h0 (n + 1), h0]

private lemma log_sub_ge {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (n : ℕ) :
    -(∑ i ∈ range n, s ^ (i + 1) / (i + 1)) - 2 * s ^ (n + 1) ≤ Real.log (1 - s) := by
  have h := (abs_le.mp (log_sub_bounds h0 h1 n)).1
  linarith

private lemma one_div_one_sub_ge {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (L : ℕ) :
    (∑ l ∈ range (L + 1), r ^ l) ≤ 1 / (1 - r) := by
  have hpos : (0:ℝ) < 1 - r := by linarith
  have hmul := geom_sum_mul r (L + 1)
  have hmul' : (1 - r) * (∑ l ∈ range (L + 1), r ^ l) = 1 - r ^ (L + 1) := by
    nlinarith [hmul]
  rw [le_div_iff₀ hpos, mul_comm, hmul']
  have hnn : (0:ℝ) ≤ r ^ (L + 1) := pow_nonneg h0 _
  linarith

private lemma L3_ge : (1098 / 1000 : ℚ) ≤
    2 * ∑ j ∈ range 30, ((3 - 1 : ℚ) / (3 + 1)) ^ (2 * j + 1) / (2 * j + 1) := by
  decide +kernel


/-! ### The rational certificate for `P1` -/

private lemma P1_cert :
    (8176817 / 1000000000 : ℚ) ≤
      ((∑ l ∈ range 15, ∑ j ∈ range 14, ∑ i ∈ range 28,
        (if i = 0 then (0:ℚ) else if i ≤ 26 then (-1:ℚ)^(i-1)/(i:ℚ)
           else if i = 27 then -2 else 0)
        * (if j = 0 then 2 * (∑ j' ∈ range 30, ((3-1:ℚ)/(3+1))^(2*j'+1)/(2*j'+1))
           else if j ≤ 12 then -1/((3:ℚ)^j * (j:ℚ))
           else if j = 13 then -2/((3:ℚ)^13 * 13) else 0)
        * (if l = 0 then (1/2:ℚ) - (1/2) * (((49/125:ℚ)/2)^15 / (1 - (49/125:ℚ)/2))
           else (1/2) * (-(1/2:ℚ))^l)
        * ((49/125:ℚ)^(i+j+l+1) / (((i+j+l+1 : ℕ) : ℚ))))
      + (∑ l ∈ range 14, ∑ j ∈ range 14, ∑ i ∈ range 28,
        (if i = 0 then (0:ℚ) else if i ≤ 26 then (-1:ℚ)^(i-1)/(i:ℚ)
           else if i = 27 then -2 else 0)
        * (if j = 0 then 2 * (∑ j' ∈ range 30, ((3-1:ℚ)/(3+1))^(2*j'+1)/(2*j'+1))
           else if j ≤ 12 then -1/((3:ℚ)^j * (j:ℚ))
           else if j = 13 then -2/((3:ℚ)^13 * 13) else 0)
        * ((1/4:ℚ) * (1/4:ℚ)^l)
        * ((49/125:ℚ)^(i+j+l+1) / (((i+j+l+1 : ℕ) : ℚ))))) / 6 := by
  decide +kernel




/-! ## Session 2: exact reduction of `F4` and `F5` to `σ`-integrals -/

private lemma F4_minA {s : ℝ} (hs : s ∈ Set.uIcc (2 * kappa1) (2 * kappa2)) :
    min kappa2 (s / 2) = s / 2 := by
  rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : (2:ℝ) * kappa1 ≤ 2 * kappa2)] at hs
  refine min_eq_right ?_
  rw [div_le_iff₀ (by norm_num)]
  linarith [hs.2]

private lemma F4_minB {s : ℝ} (hs : s ∈ Set.uIcc (kappa1 + kappa2) (2 * kappa2)) :
    min kappa2 (s - kappa2) = s - kappa2 := by
  rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : kappa1 + kappa2 ≤ 2 * kappa2)] at hs
  exact min_eq_right (by linarith [hs.2])

private lemma F5_minB {s : ℝ} (hs : s ∈ Set.uIcc (2 * kappa2) (1/3)) :
    min kappa2 (s - kappa2) = kappa2 := by
  rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : (2:ℝ) * kappa2 ≤ 1/3)] at hs
  exact min_eq_left (by linarith [hs.1])

/-- First triangle swap for `F4`: `2 t ≤ σ ≤ 2 κ₂`. -/
private lemma F4_swapA :
    (∫ t in kappa1..kappa2, ∫ s in (2 * t)..(2 * kappa2),
        Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = ∫ s in (2 * kappa1)..(2 * kappa2),
          ∫ t in kappa1..(min kappa2 (s / 2)),
            Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t) := by
  have h := swap_affine (H := fun t s : ℝ =>
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
    (A := kappa1) (B := kappa2) (D := 2 * kappa2) (α := 2) (β := 0) (by norm_num)
    (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
    (Hcont (by norm_num [kappa1]) (by norm_num [kappa1, kappa2])
      (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2]))
  simpa using h

/-- Second triangle swap, the `σ - κ₂` piece of `F4`. -/
private lemma F4_swapB :
    (∫ t in kappa1..kappa2, ∫ s in (t + kappa2)..(2 * kappa2),
        Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = ∫ s in (kappa1 + kappa2)..(2 * kappa2),
          ∫ t in kappa1..(min kappa2 (s - kappa2)),
            Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t) := by
  have h := swap_affine (H := fun t s : ℝ =>
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
    (A := kappa1) (B := kappa2) (D := 2 * kappa2) (α := 1) (β := kappa2) (by norm_num)
    (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
    (Hcont (by norm_num [kappa1]) (by norm_num [kappa1, kappa2])
      (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2]))
  simpa using h

/-- The triangle swap for `F5`. -/
private lemma F5_swap :
    (∫ t in kappa1..kappa2, ∫ s in (t + kappa2)..(1/3),
        Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = ∫ s in (kappa1 + kappa2)..(1/3),
          ∫ t in kappa1..(min kappa2 (s - kappa2)),
            Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t) := by
  have h := swap_affine (H := fun t s : ℝ =>
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
    (A := kappa1) (B := kappa2) (D := 1/3) (α := 1) (β := kappa2) (by norm_num)
    (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
    (Hcont (by norm_num [kappa1]) (by norm_num [kappa1, kappa2])
      (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2]))
  simpa using h

/-! ### Continuity of the two `σ`-integrands on the full range -/

/-- The `F4`/`F5` logarithmic weight `L(σ) = log(5-12σ)/(6-12σ)`. -/
private lemma Lcont_basic {u v : ℝ} (hu : 0 < u) (hv : v ≤ 1/3) :
    ContinuousOn (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s)) (Set.Icc u v) := by
  have hbase : ∀ s ∈ Set.Icc u v, (0:ℝ) < 5 - 12 * s ∧ (0:ℝ) < 6 - 12 * s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    exact ⟨by linarith [h2, hv], by linarith [h2, hv]⟩
  refine ContinuousOn.div (ContinuousOn.log (by fun_prop) ?_) (by fun_prop) ?_
  · intro s hs
    exact ne_of_gt (hbase s hs).1
  · intro s hs
    exact ne_of_gt (hbase s hs).2

private lemma PA_cont :
    ContinuousOn (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) *
        (Real.log ((s - kappa1) / kappa1) / s)) (Set.Icc (2 * kappa1) (2 * kappa2)) := by
  have hk1 : (0:ℝ) < kappa1 := by norm_num [kappa1]
  have hpos : ∀ s ∈ Set.Icc (2 * kappa1) (2 * kappa2), (0:ℝ) < s - kappa1 ∧ (0:ℝ) < s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    refine ⟨by linarith [hk1], by linarith [hk1]⟩
  refine ContinuousOn.mul (Lcont_basic (by norm_num [kappa1]) (by norm_num [kappa1, kappa2])) ?_
  refine ContinuousOn.div ?_ continuousOn_id ?_
  · refine ContinuousOn.log ?_ ?_
    · exact ((continuous_id.sub continuous_const).div_const _).continuousOn
    · intro s hs
      exact div_ne_zero (ne_of_gt (hpos s hs).1) (ne_of_gt hk1)
  · intro s hs
    exact ne_of_gt (hpos s hs).2

private lemma QB_cont :
    ContinuousOn (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) *
        (Real.log ((s - kappa2) / kappa2) / s)) (Set.Icc (2 * kappa1) (2 * kappa2)) := by
  have hk2 : (0:ℝ) < kappa2 := by norm_num [kappa2]
  have hpos : ∀ s ∈ Set.Icc (2 * kappa1) (2 * kappa2), (0:ℝ) < s - kappa2 ∧ (0:ℝ) < s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    norm_num [kappa1, kappa2] at h1 ⊢
    exact ⟨by linarith, by linarith⟩
  refine ContinuousOn.mul (Lcont_basic (by norm_num [kappa1]) (by norm_num [kappa1, kappa2])) ?_
  refine ContinuousOn.div ?_ continuousOn_id ?_
  · refine ContinuousOn.log ?_ ?_
    · exact ((continuous_id.sub continuous_const).div_const _).continuousOn
    · intro s hs
      exact div_ne_zero (ne_of_gt (hpos s hs).1) (ne_of_gt hk2)
  · intro s hs
    exact ne_of_gt (hpos s hs).2

private lemma QD_cont :
    ContinuousOn (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) *
        (Real.log (kappa2 / (s - kappa2)) / s)) (Set.Icc (kappa1 + kappa2) (2 * kappa2)) := by
  have hpos : ∀ s ∈ Set.Icc (kappa1 + kappa2) (2 * kappa2),
      (0:ℝ) < s - kappa2 ∧ (0:ℝ) < s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    norm_num [kappa1, kappa2] at h1 ⊢
    exact ⟨by linarith, by linarith⟩
  refine ContinuousOn.mul
    (Lcont_basic (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])) ?_
  refine ContinuousOn.div ?_ continuousOn_id ?_
  · refine ContinuousOn.log ?_ ?_
    · exact ContinuousOn.div continuousOn_const (by fun_prop) (fun s hs => ne_of_gt (hpos s hs).1)
    · intro s hs
      exact div_ne_zero (by norm_num [kappa2]) (ne_of_gt (hpos s hs).1)
  · intro s hs
    exact ne_of_gt (hpos s hs).2

/-- Continuity of `L(σ)·(log((σ-κ₂)/κ₂) + log((σ-κ₁)/κ₁))/σ`. -/
private lemma PC_cont :
    ContinuousOn (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) *
        (Real.log ((s - kappa2) / kappa2) / s + Real.log ((s - kappa1) / kappa1) / s))
      (Set.Icc (kappa1 + kappa2) (2 * kappa2)) := by
  have h1 : ∀ s ∈ Set.Icc (kappa1 + kappa2) (2 * kappa2), (0:ℝ) < s - kappa2 := by
    intro s hs
    have := hs.1; norm_num [kappa1, kappa2] at this ⊢
    linarith
  have h2 : ∀ s ∈ Set.Icc (kappa1 + kappa2) (2 * kappa2), (0:ℝ) < s - kappa1 := by
    intro s hs
    have := hs.1; norm_num [kappa1, kappa2] at this ⊢
    linarith
  have h3 : ∀ s ∈ Set.Icc (kappa1 + kappa2) (2 * kappa2), (0:ℝ) < s := by
    intro s hs
    have := hs.1; norm_num [kappa1, kappa2] at this ⊢
    linarith
  refine ContinuousOn.mul
    (Lcont_basic (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])) ?_
  refine ContinuousOn.add ?_ ?_
  · refine ContinuousOn.div ?_ continuousOn_id (fun s hs => ne_of_gt (h3 s hs))
    refine ContinuousOn.log ?_ ?_
    · exact ContinuousOn.div (by fun_prop) continuousOn_const (fun s hs => by norm_num [kappa2])
    · intro s hs
      exact div_ne_zero (ne_of_gt (h1 s hs)) (by norm_num [kappa2])
  · refine ContinuousOn.div ?_ continuousOn_id (fun s hs => ne_of_gt (h3 s hs))
    refine ContinuousOn.log ?_ ?_
    · exact ContinuousOn.div (by fun_prop) continuousOn_const (fun s hs => by norm_num [kappa1])
    · intro s hs
      exact div_ne_zero (ne_of_gt (h2 s hs)) (by norm_num [kappa1])

/-- Continuity of `L(σ)·(log(κ₂/(σ-κ₂)) + log((σ-κ₁)/κ₁))/σ`. -/
private lemma PE_cont :
    ContinuousOn (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) *
        (Real.log (kappa2 / (s - kappa2)) / s + Real.log ((s - kappa1) / kappa1) / s))
      (Set.Icc (2 * kappa2) (1/3)) := by
  have h1 : ∀ s ∈ Set.Icc (2 * kappa2) (1/3), (0:ℝ) < s - kappa2 := by
    intro s hs
    have := hs.1; norm_num [kappa2] at this ⊢
    linarith
  have h2 : ∀ s ∈ Set.Icc (2 * kappa2) (1/3), (0:ℝ) < s - kappa1 := by
    intro s hs
    have := hs.1; norm_num [kappa1, kappa2] at this ⊢
    linarith
  have h3 : ∀ s ∈ Set.Icc (2 * kappa2) (1/3), (0:ℝ) < s := by
    intro s hs
    have := hs.1; norm_num [kappa2] at this ⊢
    linarith
  refine ContinuousOn.mul
    (Lcont_basic (by norm_num [kappa2]) (by norm_num : (1:ℝ)/3 ≤ 1/3)) ?_
  refine ContinuousOn.add ?_ ?_
  · refine ContinuousOn.div ?_ continuousOn_id (fun s hs => ne_of_gt (h3 s hs))
    refine ContinuousOn.log ?_ ?_
    · exact ContinuousOn.div continuousOn_const (by fun_prop) (fun s hs => ne_of_gt (h1 s hs))
    · intro s hs
      exact div_ne_zero (by norm_num [kappa2]) (ne_of_gt (h1 s hs))
  · refine ContinuousOn.div ?_ continuousOn_id (fun s hs => ne_of_gt (h3 s hs))
    refine ContinuousOn.log ?_ ?_
    · exact ContinuousOn.div (by fun_prop) continuousOn_const (fun s hs => by norm_num [kappa1])
    · intro s hs
      exact div_ne_zero (ne_of_gt (h2 s hs)) (by norm_num [kappa1])

/-- The elementary `t`-integral on the first `F4` slice. -/
private lemma F4_inner_A {s : ℝ} (hs : s ∈ Set.uIcc (2 * kappa1) (2 * kappa2)) :
    (∫ t in kappa1..(min kappa2 (s / 2)),
        Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s) := by
  have hk1 : (0:ℝ) < kappa1 := by norm_num [kappa1]
  rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : (2:ℝ) * kappa1 ≤ 2 * kappa2)] at hs
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : (0:ℝ) < s := by linarith [hs1, hk1]
  have hsm : min kappa2 (s / 2) = s / 2 := by rw [min_comm]; exact min_eq_left (by linarith [hs2])
  rw [hsm]
  have hcongr : (∫ t in kappa1..(s / 2),
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = Real.log (5 - 12 * s) / (6 - 12 * s) * (∫ t in kappa1..(s / 2), 1 / (t * (s - t))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : kappa1 ≤ s / 2)] at ht
    simp only []
    have ht1 : kappa1 ≤ t := ht.1
    have ht2 : t ≤ s / 2 := ht.2
    have ht0 : t ≠ 0 := by intro h; rw [h] at ht1; linarith [hk1]
    have hst : s - t ≠ 0 := by intro h; linarith
    have h6 : (6 - 12 * s) ≠ 0 := by
      have h := hs2; norm_num [kappa2] at h; intro hh; nlinarith
    field_simp
    try ring
  rw [hcongr, int_one_div_mul_sub (σ := s) (p := kappa1) (q := s / 2) hk1
    (by linarith) (by linarith)]
  have key : -Real.log (kappa1 / (s - kappa1)) = Real.log ((s - kappa1) / kappa1) := by
    rw [eq_comm, ← Real.log_inv, inv_div]
  rw [show s / 2 / (s - s / 2) = 1 by rw [show s - s / 2 = s / 2 by ring]; exact div_self (by intro h; linarith), Real.log_one, zero_sub, key]
  try ring

/-- The elementary `t`-integral on the `σ - κ₂` slice. -/
private lemma F4_inner_B {s : ℝ} (hs : s ∈ Set.uIcc (kappa1 + kappa2) (2 * kappa2)) :
    (∫ t in kappa1..(min kappa2 (s - kappa2)),
        Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa2) / kappa2) / s + Real.log ((s - kappa1) / kappa1) / s) := by
  have hk1 : (0:ℝ) < kappa1 := by norm_num [kappa1]
  rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : kappa1 + kappa2 ≤ 2 * kappa2)] at hs
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : (0:ℝ) < s := by linarith [hs1, hk1]
  have hsm : min kappa2 (s - kappa2) = s - kappa2 := by rw [min_comm]; exact min_eq_left (by linarith [hs2])
  rw [hsm]
  have hcongr : (∫ t in kappa1..(s - kappa2),
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = Real.log (5 - 12 * s) / (6 - 12 * s) * (∫ t in kappa1..(s - kappa2), 1 / (t * (s - t))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : kappa1 ≤ s - kappa2)] at ht
    simp only []
    have ht1 : kappa1 ≤ t := ht.1
    have ht2 : t ≤ s - kappa2 := ht.2
    have ht0 : t ≠ 0 := by intro h; rw [h] at ht1; linarith [hk1]
    have hst : s - t ≠ 0 := by intro h; linarith
    have h6 : (6 - 12 * s) ≠ 0 := by
      have h := hs2; norm_num [kappa2] at h; intro hh; nlinarith
    field_simp
    try ring
  rw [hcongr, int_one_div_mul_sub (σ := s) (p := kappa1) (q := s - kappa2) hk1
    (by linarith) (by linarith)]
  have key : -Real.log (kappa1 / (s - kappa1)) = Real.log ((s - kappa1) / kappa1) := by
    rw [eq_comm, ← Real.log_inv, inv_div]
  rw [show s - (s - kappa2) = kappa2 by ring]
  have e : Real.log ((s - kappa2) / kappa2) - Real.log (kappa1 / (s - kappa1))
      = Real.log ((s - kappa2) / kappa2) + Real.log ((s - kappa1) / kappa1) := by
    linarith [key]
  rw [e]
  ring

/-- On `[2 κ₂, 1/3]` the upper limit of the `t`-integral is the constant `κ₂`. -/
private lemma F5_inner_C {s : ℝ} (hs : s ∈ Set.uIcc (2 * kappa2) (1/3)) :
    (∫ t in kappa1..(min kappa2 (s - kappa2)),
        Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log (kappa2 / (s - kappa2)) / s + Real.log ((s - kappa1) / kappa1) / s) := by
  have hk1 : (0:ℝ) < kappa1 := by norm_num [kappa1]
  rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : (2:ℝ) * kappa2 ≤ 1/3)] at hs
  obtain ⟨hs1, hs2⟩ := hs
  have hk2 : (0:ℝ) < kappa2 := by norm_num [kappa2]
  have hk12 : kappa1 ≤ kappa2 := by norm_num [kappa1, kappa2]
  have hs0 : (0:ℝ) < s := by linarith [hs1, hk2]
  have hsm : min kappa2 (s - kappa2) = kappa2 := min_eq_left (by linarith [hs1])
  rw [hsm]
  have hcongr : (∫ t in kappa1..(kappa2),
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = Real.log (5 - 12 * s) / (6 - 12 * s) * (∫ t in kappa1..(kappa2), 1 / (t * (s - t))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hk12] at ht
    simp only []
    have ht1 : kappa1 ≤ t := ht.1
    have ht2 : t ≤ kappa2 := ht.2
    have ht0 : t ≠ 0 := by intro h; rw [h] at ht1; linarith [hk1]
    have hst : s - t ≠ 0 := by intro h; nlinarith [hs1, ht2, hk2]
    have h6 : (6 - 12 * s) ≠ 0 := by
      have h := hs2; norm_num [kappa2] at h; intro hh; nlinarith
    field_simp
    try ring
  rw [hcongr, int_one_div_mul_sub (σ := s) (p := kappa1) (q := kappa2) hk1
    (by linarith) (by linarith)]
  have key : -Real.log (kappa1 / (s - kappa1)) = Real.log ((s - kappa1) / kappa1) := by
    rw [eq_comm, ← Real.log_inv, inv_div]
  have e : Real.log (kappa2 / (s - kappa2)) - Real.log (kappa1 / (s - kappa1))
      = Real.log (kappa2 / (s - kappa2)) + Real.log ((s - kappa1) / kappa1) := by
    linarith [key]
  rw [e]
  ring

/-- `F5` in the elementary `(5 - 12 σ)` form. -/
private lemma F5_form (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) :
    integralTerms F f ω 5 = 48 * (∫ t in kappa1..kappa2,
      (∫ u in kappa2..(1/3 - t),
        Real.log (5 - 12 * (t + u)) / ((6 - 12 * (t + u)) * u)) / t) := by
  rw [F5_elementary (F := F) (f := f) h ω]
  refine congrArg (fun z => 48 * z) ?_
  apply intervalIntegral.integral_congr
  intro t _
  refine congrArg (fun z => z / t) ?_
  rw [show (1/2 - 2 * kappa1 - t : ℝ) = 1/3 - t by norm_num [kappa1]]
  apply intervalIntegral.integral_congr
  intro u _
  simp only []
  rw [show (1/2 - t - u) / kappa1 - 1 = 5 - 12 * (t + u) by norm_num [kappa1]; ring,
    show (1/2 - t - u) / kappa1 = 6 - 12 * (t + u) by norm_num [kappa1]; ring]

/-- Integrability of the `F4`/`F5` kernel slice. -/
private lemma kern_ii {t : ℝ} (ht : t ∈ Set.Icc kappa1 kappa2) {p q : ℝ}
    (hp : 2 * kappa1 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2 * kappa2) :
    IntervalIntegrable (fun s : ℝ => Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      volume p q := by
  have hc : ContinuousOn (fun s : ℝ => Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      (Set.Icc (2 * kappa1) (2 * kappa2)) := by
    have hH := Hcont (A := kappa1) (B := kappa2) (C := 2 * kappa1) (D := 2 * kappa2)
      (by norm_num [kappa1]) (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
      (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
    have hcomp := hH.comp
      (Continuous.continuousOn (by fun_prop : Continuous fun s : ℝ => (t, s)))
      (fun s hs => ⟨ht, hs⟩)
    simpa [Function.comp_def] using hcomp
  refine (hc.mono ?_).intervalIntegrable
  intro s hs
  rw [Set.uIcc_of_le (a := p) (b := q) hpq] at hs
  exact ⟨le_trans hp hs.1, le_trans hs.2 hq⟩

/-- `F4` as a sum of two one-dimensional `σ`-integrals. -/
private lemma F4_sigma (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) :
    integralTerms F f ω 4
      = 48 * ((∫ s in (2 * kappa1)..(kappa1 + kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s))
          + (∫ s in (kappa1 + kappa2)..(2 * kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log (kappa2 / (s - kappa2)) / s))) := by
  rw [F4_form F f ω h]
  congr 1
  have hk1' : (0:ℝ) < kappa1 := by norm_num [kappa1]
  have hpt : ∀ t ∈ Set.uIcc kappa1 kappa2,
      (∫ u in t..kappa2, Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u)) / t
        = (∫ s in (2*t)..(2*kappa2), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
          - (∫ s in (t+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t)) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : kappa1 ≤ kappa2)] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have ht0 : (0:ℝ) < t := by linarith [ht1, hk1']
    have h1 : (∫ u in t..kappa2, Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u)) / t
        = ∫ s in (2*t)..(t+kappa2), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t) := by
      have hsub := F4_inner_subst t
      rw [show (29/250 : ℝ) = kappa2 from by norm_num [kappa2]] at hsub
      rw [hsub, ← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro s hs
      simp only []
      have ht0' : t ≠ 0 := ne_of_gt ht0
      field_simp
      try ring
    rw [h1]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (kern_ii (t := t) ⟨ht1, ht2⟩ (p := 2*t) (q := t+kappa2) (by linarith) (by linarith) (by linarith))
      (kern_ii (t := t) ⟨ht1, ht2⟩ (p := t+kappa2) (q := 2*kappa2) (by linarith) (by linarith) (by linarith))
    rw [show (∫ s in (2*t)..(2*kappa2), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
        = (∫ s in (2*t)..(t+kappa2), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t)) + (∫ s in (t+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t)) from hadd.symm]
    ring
  rw [intervalIntegral.integral_congr hpt]
  have hHc : ContinuousOn (fun p : ℝ × ℝ =>
      Real.log (5 - 12 * p.2) / ((6 - 12 * p.2) * (p.2 - p.1) * p.1))
      (Set.Icc kappa1 kappa2 ×ˢ Set.Icc (2 * kappa1) (2 * kappa2)) :=
    Hcont (by norm_num [kappa1]) (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
      (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
  have hHc2 : ContinuousOn (fun p : ℝ × ℝ =>
      Real.log (5 - 12 * p.2) / ((6 - 12 * p.2) * (p.2 - p.1) * p.1))
      (Set.Icc kappa1 kappa2 ×ˢ Set.Icc (kappa1 + kappa2) (2 * kappa2)) :=
    Hcont (by norm_num [kappa1]) (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
      (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
  have hii1 : IntervalIntegrable (fun t : ℝ => ∫ s in (2*t)..(2*kappa2),
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t)) volume kappa1 kappa2 := by
    simpa using intervalIntegrable_param (H := fun t s : ℝ =>
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      (A := kappa1) (B := kappa2) (D := 2 * kappa2) (α := 2) (β := 0)
      (by norm_num) (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
      (by simpa using hHc)
  have hii2 : IntervalIntegrable (fun t : ℝ => ∫ s in (t+kappa2)..(2*kappa2),
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t)) volume kappa1 kappa2 := by
    simpa using intervalIntegrable_param (H := fun t s : ℝ =>
      Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      (A := kappa1) (B := kappa2) (D := 2 * kappa2) (α := 1) (β := kappa2)
      (by norm_num) (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
      (by simpa using hHc2)
  rw [intervalIntegral.integral_sub hii1 hii2]
  rw [F4_swapA, F4_swapB]
  have e1 : (∫ s in (2*kappa1)..(2*kappa2),
        ∫ t in kappa1..(min kappa2 (s/2)), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = ∫ s in (2*kappa1)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    simpa using F4_inner_A hs
  have e2 : (∫ s in (kappa1+kappa2)..(2*kappa2),
        ∫ t in kappa1..(min kappa2 (s - kappa2)), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = ∫ s in (kappa1+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa2) / kappa2) / s) + Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    simpa [mul_add] using F4_inner_B hs
  rw [e1, e2]
  have hCB : ∀ s ∈ Set.uIcc (kappa1+kappa2) (2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa2) / kappa2) / s) = -(Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log (kappa2 / (s - kappa2)) / s)) := by
    intro s hs
    have hl : Real.log ((s - kappa2) / kappa2) = -Real.log (kappa2 / (s - kappa2)) := by
      rw [← Real.log_inv]
      congr 1
      rw [inv_div]
    rw [hl]
    ring
  have iPA : IntervalIntegrable (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s)) volume (2*kappa1) (2*kappa2) :=
    (PA_cont.mono (by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : (2:ℝ)*kappa1 ≤ 2*kappa2)] at hx
      exact hx)).intervalIntegrable
  have hmono : ∀ {p q : ℝ}, 2*kappa1 ≤ p → p ≤ q → q ≤ 2*kappa2 →
      Set.uIcc p q ⊆ Set.uIcc (2*kappa1) (2*kappa2) := by
    intro p q hp hpq hq x hx
    rw [Set.uIcc_of_le (a := p) (b := q) hpq] at hx
    rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : (2:ℝ)*kappa1 ≤ 2*kappa2)]
    exact ⟨le_trans hp hx.1, le_trans hx.2 hq⟩
  have iPA2 : IntervalIntegrable (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s)) volume (2*kappa1) (kappa1+kappa2) :=
    iPA.mono_set (hmono (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
      (by norm_num [kappa1, kappa2]))
  have iPA3 : IntervalIntegrable (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s)) volume (kappa1+kappa2) (2*kappa2) :=
    iPA.mono_set (hmono (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
      (by norm_num [kappa1, kappa2]))
  have iQB : IntervalIntegrable (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa2) / kappa2) / s)) volume (kappa1+kappa2) (2*kappa2) :=
    (QB_cont.mono (by
      intro x hx
      rw [Set.uIcc_of_le (a := kappa1 + kappa2) (b := 2*kappa2)
        (by norm_num [kappa1, kappa2])] at hx
      have hk12 : kappa1 ≤ kappa2 := by norm_num [kappa1, kappa2]
      exact ⟨by linarith [hx.1, hk12], hx.2⟩)).intervalIntegrable
  have iB : IntervalIntegrable (fun s : ℝ => Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log (kappa2 / (s - kappa2)) / s)) volume (kappa1+kappa2) (2*kappa2) :=
    (QD_cont.mono (by
      intro x hx
      rw [Set.uIcc_of_le (a := kappa1 + kappa2) (b := 2*kappa2)
        (by norm_num [kappa1, kappa2])] at hx
      exact hx)).intervalIntegrable
  have splitA : (∫ s in (2*kappa1)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s))
      = (∫ s in (2*kappa1)..(kappa1+kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s))
        + (∫ s in (kappa1+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s)) :=
    (intervalIntegral.integral_add_adjacent_intervals iPA2 iPA3).symm
  have addAC : (∫ s in (kappa1+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa2) / kappa2) / s) + Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s))
      = (∫ s in (kappa1+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa2) / kappa2) / s))
        + (∫ s in (kappa1+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s)) :=
    intervalIntegral.integral_add iQB iPA3
  have negC : (∫ s in (kappa1+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa2) / kappa2) / s))
      = -(∫ s in (kappa1+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log (kappa2 / (s - kappa2)) / s)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s hs
    exact hCB s hs
  rw [splitA, addAC, negC]
  ring

/-- `F5` as a sum of two one-dimensional `σ`-integrals. -/
private lemma F5_sigma (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) :
    integralTerms F f ω 5
      = 48 * ((∫ s in (kappa1 + kappa2)..(2 * kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa2) / kappa2) / s + Real.log ((s - kappa1) / kappa1) / s))
          + (∫ s in (2 * kappa2)..(1/3), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log (kappa2 / (s - kappa2)) / s + Real.log ((s - kappa1) / kappa1) / s))) := by
  rw [F5_form F f ω h]
  congr 1
  have hk1' : (0:ℝ) < kappa1 := by norm_num [kappa1]
  have hpt : ∀ t ∈ Set.uIcc kappa1 kappa2,
      (∫ u in kappa2..(1/3 - t),
          Real.log (5 - 12*(t+u)) / ((6 - 12*(t+u)) * u)) / t
        = ∫ s in (t+kappa2)..(1/3), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : kappa1 ≤ kappa2)] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have ht0 : (0:ℝ) < t := by linarith [ht1, hk1']
    have hsub := F5_inner_subst t
    rw [show (29/250 : ℝ) = kappa2 from by norm_num [kappa2]] at hsub
    rw [hsub, ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only []
    have ht0' : t ≠ 0 := ne_of_gt ht0
    field_simp
    try ring
  rw [intervalIntegral.integral_congr hpt]
  have hHc : ContinuousOn (fun p : ℝ × ℝ =>
      Real.log (5 - 12 * p.2) / ((6 - 12 * p.2) * (p.2 - p.1) * p.1))
      (Set.Icc kappa1 kappa2 ×ˢ Set.Icc (kappa1 + kappa2) (1/3)) :=
    Hcont (by norm_num [kappa1]) (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
      (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
  rw [show (∫ t in kappa1..kappa2, ∫ s in (t+kappa2)..(1/3), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = ∫ s in (kappa1 + kappa2)..(1/3), ∫ t in kappa1..(min kappa2 (s - kappa2)), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t) from by
    have h := swap_affine (H := fun t s : ℝ => Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      (A := kappa1) (B := kappa2) (D := 1/3) (α := 1) (β := kappa2) (by norm_num)
      (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2]) (by simpa using hHc)
    simpa using h]
  have hG1 : IntervalIntegrable (fun s : ℝ => ∫ t in kappa1..(min kappa2 (s - kappa2)), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      volume (kappa1 + kappa2) (2*kappa2) := by
    refine (PC_cont.mono ?_).intervalIntegrable.congr_ae ?_
    · intro s hs
      rw [Set.uIcc_of_le (a := kappa1 + kappa2) (b := 2*kappa2)
        (by norm_num [kappa1, kappa2])] at hs
      exact hs
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      rw [Set.uIoc_of_le (by norm_num [kappa1, kappa2] : kappa1 + kappa2 ≤ 2*kappa2)] at hs
      have hmem : s ∈ Set.uIcc (kappa1 + kappa2) (2*kappa2) := by
        rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : kappa1 + kappa2 ≤ 2*kappa2)]
        exact ⟨le_of_lt hs.1, hs.2⟩
      exact (by simpa [← mul_add] using (F4_inner_B hmem).symm)
  have hG2 : IntervalIntegrable (fun s : ℝ => ∫ t in kappa1..(min kappa2 (s - kappa2)), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      volume (2*kappa2) (1/3) := by
    refine (PE_cont.mono ?_).intervalIntegrable.congr_ae ?_
    · intro s hs
      rw [Set.uIcc_of_le (a := (2:ℝ)*kappa2) (b := 1/3)
        (by norm_num [kappa1, kappa2])] at hs
      exact hs
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      rw [Set.uIoc_of_le (by norm_num [kappa1, kappa2] : (2:ℝ)*kappa2 ≤ 1/3)] at hs
      have hmem : s ∈ Set.uIcc (2*kappa2) (1/3) := by
        rw [Set.uIcc_of_le (by norm_num [kappa1, kappa2] : (2:ℝ)*kappa2 ≤ 1/3)]
        exact ⟨le_of_lt hs.1, hs.2⟩
      exact (by simpa [← mul_add] using (F5_inner_C hmem).symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals hG1 hG2]
  have e1 : (∫ s in (kappa1+kappa2)..(2*kappa2),
        ∫ t in kappa1..(min kappa2 (s - kappa2)), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = ∫ s in (kappa1+kappa2)..(2*kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa2) / kappa2) / s + Real.log ((s - kappa1) / kappa1) / s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    simpa [mul_add] using F4_inner_B hs
  have e2 : (∫ s in (2*kappa2)..(1/3),
        ∫ t in kappa1..(min kappa2 (s - kappa2)), Real.log (5 - 12 * s) / ((6 - 12 * s) * (s - t) * t))
      = ∫ s in (2*kappa2)..(1/3), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log (kappa2 / (s - kappa2)) / s + Real.log ((s - kappa1) / kappa1) / s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact F5_inner_C hs
  rw [e1, e2]

/-! ### NEW: F4 panels, per-panel rational certificates, and the leaf -/

private lemma ii_mono {f : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable f volume a b)
    {c d : ℝ} (h1 : a ≤ c) (h2 : d ≤ b) (h3 : c ≤ d) : IntervalIntegrable f volume c d :=
  h.mono_set (by
    rw [Set.uIcc_of_le h3, Set.uIcc_of_le (le_trans h1 (le_trans h3 h2))]
    exact Set.Icc_subset_Icc h1 h2)

/-! #### panel A0 -/
private lemma A0_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3049:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3049:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3049:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3049:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((3049:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3049:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3049:ℚ)/18000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3049:ℚ)/18000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3049:ℚ)/18000) + 2/((6:ℚ) - 12*((3049:ℚ)/18000)) - ((1:ℚ)/6/((3049:ℚ)/18000) * ((((49:ℚ)/18000)/((3049:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3049:ℚ)/18000))) + 2/((6:ℚ) - 12*((3049:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3049:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3049:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3049:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3049:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3049:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((1549/9000) : ℚ) : ℝ) - (((3049/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((1/6) : ℚ) : ℝ) - (((3049/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((1/6) : ℚ) : ℝ)..(((1549/9000) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((1:ℚ)/6)) (q := ((1549:ℚ)/9000)) (c := ((3049:ℚ)/18000)) (d := ((49:ℚ)/18000))
    (a := ((1:ℚ)/12)) (r := ((1:ℚ)/12)) (eB := 1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3049:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3049:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := (2 * (∑ j ∈ range 40, (((((((3049:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3049:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1549:ℚ)/9000))) - 1) / ((((5:ℚ) - 12*((1549:ℚ)/9000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3049:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((3049:ℚ)/18000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3049:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((3049:ℚ)/18000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((3049:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3049:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((3049:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3049:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((1549:ℚ)/9000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((1549:ℚ)/9000)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3049:ℚ)/18000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1549:ℚ)/9000))) - 1) / ((((5:ℚ) - 12*((1549:ℚ)/9000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := (((((3049:ℚ)/18000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 ((((3049:ℚ)/18000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ)
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (1:ℝ) ≤ (x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ) := by
      rw [le_div_iff₀ (by norm_num)]
      push_cast
      linarith [hx.1]
    have h2 := Real.log_nonneg h1
    push_cast at h2 ⊢
    linarith [h2])
      (by norm_num)
      (by push_cast; norm_num)

private theorem A0_cert : ((70032747/250000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3049:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3049:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3049:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3049:ℚ)/18000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((3049:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3049:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3049:ℚ)/18000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3049:ℚ)/18000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((3049:ℚ)/18000) + 2/((6:ℚ) - 12*((3049:ℚ)/18000)) - ((1:ℚ)/6/((3049:ℚ)/18000) * ((((49:ℚ)/18000)/((3049:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3049:ℚ)/18000))) + 2/((6:ℚ) - 12*((3049:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3049:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3049:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3049:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3049:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3049:ℚ)/18000)))^l) : ℚ) *
      (((((1549:ℚ)/9000) - ((3049:ℚ)/18000)) ^ (i + j + l + 1) - (((1:ℚ)/6) - ((3049:ℚ)/18000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma A0_certR : (((70032747/250000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3049:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3049:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3049:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3049:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((3049:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3049:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3049:ℚ)/18000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3049:ℚ)/18000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3049:ℚ)/18000) + 2/((6:ℚ) - 12*((3049:ℚ)/18000)) - ((1:ℚ)/6/((3049:ℚ)/18000) * ((((49:ℚ)/18000)/((3049:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3049:ℚ)/18000))) + 2/((6:ℚ) - 12*((3049:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3049:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3049:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3049:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3049:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3049:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((1549/9000) : ℚ) : ℝ) - (((3049/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((1/6) : ℚ) : ℝ) - (((3049/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := A0_cert
  exact_mod_cast h

/-! #### panel A1 -/
private lemma A1_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1049:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1049:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1049:ℚ)/6000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((1049:ℚ)/6000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((1049:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((1049:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((1049:ℚ)/6000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((1049:ℚ)/6000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((1049:ℚ)/6000) + 2/((6:ℚ) - 12*((1049:ℚ)/6000)) - ((1:ℚ)/6/((1049:ℚ)/6000) * ((((49:ℚ)/18000)/((1049:ℚ)/6000))^(4+1)/(1 - ((49:ℚ)/18000)/((1049:ℚ)/6000))) + 2/((6:ℚ) - 12*((1049:ℚ)/6000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1049:ℚ)/6000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1049:ℚ)/6000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((1049:ℚ)/6000)^(l+1) + (2/((6:ℚ)-12*((1049:ℚ)/6000))) * ((12:ℚ)/((6:ℚ)-12*((1049:ℚ)/6000)))^l) : ℚ) : ℝ) *
      ((((((799/4500) : ℚ) : ℝ) - (((1049/6000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((1549/9000) : ℚ) : ℝ) - (((1049/6000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((1549/9000) : ℚ) : ℝ)..(((799/4500) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((1549:ℚ)/9000)) (q := ((799:ℚ)/4500)) (c := ((1049:ℚ)/6000)) (d := ((49:ℚ)/18000))
    (a := ((1:ℚ)/12)) (r := ((1:ℚ)/12)) (eB := 1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1049:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1049:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := (2 * (∑ j ∈ range 40, (((((((1049:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((1049:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((799:ℚ)/4500))) - 1) / ((((5:ℚ) - 12*((799:ℚ)/4500))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((1049:ℚ)/6000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((1049:ℚ)/6000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((1049:ℚ)/6000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((1049:ℚ)/6000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((1049:ℚ)/6000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((1049:ℚ)/6000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((1049:ℚ)/6000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((1049:ℚ)/6000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((799:ℚ)/4500)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((799:ℚ)/4500)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1049:ℚ)/6000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((799:ℚ)/4500))) - 1) / ((((5:ℚ) - 12*((799:ℚ)/4500))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := (((((1049:ℚ)/6000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 ((((1049:ℚ)/6000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ)
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (1:ℝ) ≤ (x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ) := by
      rw [le_div_iff₀ (by norm_num)]
      push_cast
      linarith [hx.1]
    have h2 := Real.log_nonneg h1
    push_cast at h2 ⊢
    linarith [h2])
      (by norm_num)
      (by push_cast; norm_num)

private theorem A1_cert : ((396107859/500000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1049:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1049:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1049:ℚ)/6000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((1049:ℚ)/6000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((1049:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((1049:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((1049:ℚ)/6000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((1049:ℚ)/6000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((1049:ℚ)/6000) + 2/((6:ℚ) - 12*((1049:ℚ)/6000)) - ((1:ℚ)/6/((1049:ℚ)/6000) * ((((49:ℚ)/18000)/((1049:ℚ)/6000))^(4+1)/(1 - ((49:ℚ)/18000)/((1049:ℚ)/6000))) + 2/((6:ℚ) - 12*((1049:ℚ)/6000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1049:ℚ)/6000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1049:ℚ)/6000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((1049:ℚ)/6000)^(l+1) + (2/((6:ℚ)-12*((1049:ℚ)/6000))) * ((12:ℚ)/((6:ℚ)-12*((1049:ℚ)/6000)))^l) : ℚ) *
      (((((799:ℚ)/4500) - ((1049:ℚ)/6000)) ^ (i + j + l + 1) - (((1549:ℚ)/9000) - ((1049:ℚ)/6000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma A1_certR : (((396107859/500000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1049:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1049:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1049:ℚ)/6000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((1049:ℚ)/6000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((1049:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((1049:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((1049:ℚ)/6000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((1049:ℚ)/6000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((1049:ℚ)/6000) + 2/((6:ℚ) - 12*((1049:ℚ)/6000)) - ((1:ℚ)/6/((1049:ℚ)/6000) * ((((49:ℚ)/18000)/((1049:ℚ)/6000))^(4+1)/(1 - ((49:ℚ)/18000)/((1049:ℚ)/6000))) + 2/((6:ℚ) - 12*((1049:ℚ)/6000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1049:ℚ)/6000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1049:ℚ)/6000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((1049:ℚ)/6000)^(l+1) + (2/((6:ℚ)-12*((1049:ℚ)/6000))) * ((12:ℚ)/((6:ℚ)-12*((1049:ℚ)/6000)))^l) : ℚ) : ℝ) *
      ((((((799/4500) : ℚ) : ℝ) - (((1049/6000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((1549/9000) : ℚ) : ℝ) - (((1049/6000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := A1_cert
  exact_mod_cast h

/-! #### panel A2 -/
private lemma A2_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((649:ℚ)/3600))) - 1) / ((((5:ℚ) - 12*((649:ℚ)/3600))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((649:ℚ)/3600)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((649:ℚ)/3600)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((649:ℚ)/3600) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((649:ℚ)/3600) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((649:ℚ)/3600) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((649:ℚ)/3600) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((649:ℚ)/3600) + 2/((6:ℚ) - 12*((649:ℚ)/3600)) - ((1:ℚ)/6/((649:ℚ)/3600) * ((((49:ℚ)/18000)/((649:ℚ)/3600))^(4+1)/(1 - ((49:ℚ)/18000)/((649:ℚ)/3600))) + 2/((6:ℚ) - 12*((649:ℚ)/3600)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((649:ℚ)/3600)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((649:ℚ)/3600))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((649:ℚ)/3600)^(l+1) + (2/((6:ℚ)-12*((649:ℚ)/3600))) * ((12:ℚ)/((6:ℚ)-12*((649:ℚ)/3600)))^l) : ℚ) : ℝ) *
      ((((((183/1000) : ℚ) : ℝ) - (((649/3600) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((799/4500) : ℚ) : ℝ) - (((649/3600) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((799/4500) : ℚ) : ℝ)..(((183/1000) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((799:ℚ)/4500)) (q := ((183:ℚ)/1000)) (c := ((649:ℚ)/3600)) (d := ((49:ℚ)/18000))
    (a := ((1:ℚ)/12)) (r := ((1:ℚ)/12)) (eB := 1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((649:ℚ)/3600))) - 1) / ((((5:ℚ) - 12*((649:ℚ)/3600))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := (2 * (∑ j ∈ range 40, (((((((649:ℚ)/3600) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((649:ℚ)/3600) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((183:ℚ)/1000))) - 1) / ((((5:ℚ) - 12*((183:ℚ)/1000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((649:ℚ)/3600)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((649:ℚ)/3600)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((649:ℚ)/3600)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((649:ℚ)/3600)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((649:ℚ)/3600)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((649:ℚ)/3600)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((649:ℚ)/3600)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((649:ℚ)/3600)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((183:ℚ)/1000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((183:ℚ)/1000)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((649:ℚ)/3600)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((183:ℚ)/1000))) - 1) / ((((5:ℚ) - 12*((183:ℚ)/1000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := (((((649:ℚ)/3600) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 ((((649:ℚ)/3600) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ)
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (1:ℝ) ≤ (x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ) := by
      rw [le_div_iff₀ (by norm_num)]
      push_cast
      linarith [hx.1]
    have h2 := Real.log_nonneg h1
    push_cast at h2 ⊢
    linarith [h2])
      (by norm_num)
      (by push_cast; norm_num)

private theorem A2_cert : ((619640949/500000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((649:ℚ)/3600))) - 1) / ((((5:ℚ) - 12*((649:ℚ)/3600))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((649:ℚ)/3600)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((649:ℚ)/3600)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((649:ℚ)/3600) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((649:ℚ)/3600) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((649:ℚ)/3600) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((649:ℚ)/3600) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((649:ℚ)/3600) + 2/((6:ℚ) - 12*((649:ℚ)/3600)) - ((1:ℚ)/6/((649:ℚ)/3600) * ((((49:ℚ)/18000)/((649:ℚ)/3600))^(4+1)/(1 - ((49:ℚ)/18000)/((649:ℚ)/3600))) + 2/((6:ℚ) - 12*((649:ℚ)/3600)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((649:ℚ)/3600)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((649:ℚ)/3600))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((649:ℚ)/3600)^(l+1) + (2/((6:ℚ)-12*((649:ℚ)/3600))) * ((12:ℚ)/((6:ℚ)-12*((649:ℚ)/3600)))^l) : ℚ) *
      (((((183:ℚ)/1000) - ((649:ℚ)/3600)) ^ (i + j + l + 1) - (((799:ℚ)/4500) - ((649:ℚ)/3600)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma A2_certR : (((619640949/500000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((649:ℚ)/3600))) - 1) / ((((5:ℚ) - 12*((649:ℚ)/3600))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((649:ℚ)/3600)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((649:ℚ)/3600)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((649:ℚ)/3600) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((649:ℚ)/3600) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((649:ℚ)/3600) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((649:ℚ)/3600) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((649:ℚ)/3600) + 2/((6:ℚ) - 12*((649:ℚ)/3600)) - ((1:ℚ)/6/((649:ℚ)/3600) * ((((49:ℚ)/18000)/((649:ℚ)/3600))^(4+1)/(1 - ((49:ℚ)/18000)/((649:ℚ)/3600))) + 2/((6:ℚ) - 12*((649:ℚ)/3600)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((649:ℚ)/3600)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((649:ℚ)/3600))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((649:ℚ)/3600)^(l+1) + (2/((6:ℚ)-12*((649:ℚ)/3600))) * ((12:ℚ)/((6:ℚ)-12*((649:ℚ)/3600)))^l) : ℚ) : ℝ) *
      ((((((183/1000) : ℚ) : ℝ) - (((649/3600) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((799/4500) : ℚ) : ℝ) - (((649/3600) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := A2_cert
  exact_mod_cast h

/-! #### panel A3 -/
private lemma A3_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3343:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3343:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3343:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3343:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((3343:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3343:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3343:ℚ)/18000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3343:ℚ)/18000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3343:ℚ)/18000) + 2/((6:ℚ) - 12*((3343:ℚ)/18000)) - ((1:ℚ)/6/((3343:ℚ)/18000) * ((((49:ℚ)/18000)/((3343:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3343:ℚ)/18000))) + 2/((6:ℚ) - 12*((3343:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3343:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3343:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3343:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3343:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3343:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((212/1125) : ℚ) : ℝ) - (((3343/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((183/1000) : ℚ) : ℝ) - (((3343/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((183/1000) : ℚ) : ℝ)..(((212/1125) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((183:ℚ)/1000)) (q := ((212:ℚ)/1125)) (c := ((3343:ℚ)/18000)) (d := ((49:ℚ)/18000))
    (a := ((1:ℚ)/12)) (r := ((1:ℚ)/12)) (eB := 1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3343:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3343:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := (2 * (∑ j ∈ range 40, (((((((3343:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3343:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((212:ℚ)/1125))) - 1) / ((((5:ℚ) - 12*((212:ℚ)/1125))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3343:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((3343:ℚ)/18000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3343:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((3343:ℚ)/18000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((3343:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3343:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((3343:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3343:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((212:ℚ)/1125)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((212:ℚ)/1125)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3343:ℚ)/18000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((212:ℚ)/1125))) - 1) / ((((5:ℚ) - 12*((212:ℚ)/1125))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := (((((3343:ℚ)/18000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 ((((3343:ℚ)/18000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ)
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (1:ℝ) ≤ (x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ) := by
      rw [le_div_iff₀ (by norm_num)]
      push_cast
      linarith [hx.1]
    have h2 := Real.log_nonneg h1
    push_cast at h2 ⊢
    linarith [h2])
      (by norm_num)
      (by push_cast; norm_num)

private theorem A3_cert : ((1629574479/1000000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3343:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3343:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3343:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3343:ℚ)/18000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((3343:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3343:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3343:ℚ)/18000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3343:ℚ)/18000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((3343:ℚ)/18000) + 2/((6:ℚ) - 12*((3343:ℚ)/18000)) - ((1:ℚ)/6/((3343:ℚ)/18000) * ((((49:ℚ)/18000)/((3343:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3343:ℚ)/18000))) + 2/((6:ℚ) - 12*((3343:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3343:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3343:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3343:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3343:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3343:ℚ)/18000)))^l) : ℚ) *
      (((((212:ℚ)/1125) - ((3343:ℚ)/18000)) ^ (i + j + l + 1) - (((183:ℚ)/1000) - ((3343:ℚ)/18000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma A3_certR : (((1629574479/1000000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3343:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3343:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3343:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3343:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((3343:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3343:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3343:ℚ)/18000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3343:ℚ)/18000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3343:ℚ)/18000) + 2/((6:ℚ) - 12*((3343:ℚ)/18000)) - ((1:ℚ)/6/((3343:ℚ)/18000) * ((((49:ℚ)/18000)/((3343:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3343:ℚ)/18000))) + 2/((6:ℚ) - 12*((3343:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3343:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3343:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3343:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3343:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3343:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((212/1125) : ℚ) : ℝ) - (((3343/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((183/1000) : ℚ) : ℝ) - (((3343/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := A3_cert
  exact_mod_cast h

/-! #### panel A4 -/
private lemma A4_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1147:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1147:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1147:ℚ)/6000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((1147:ℚ)/6000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((1147:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((1147:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((1147:ℚ)/6000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((1147:ℚ)/6000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((1147:ℚ)/6000) + 2/((6:ℚ) - 12*((1147:ℚ)/6000)) - ((1:ℚ)/6/((1147:ℚ)/6000) * ((((49:ℚ)/18000)/((1147:ℚ)/6000))^(4+1)/(1 - ((49:ℚ)/18000)/((1147:ℚ)/6000))) + 2/((6:ℚ) - 12*((1147:ℚ)/6000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1147:ℚ)/6000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1147:ℚ)/6000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((1147:ℚ)/6000)^(l+1) + (2/((6:ℚ)-12*((1147:ℚ)/6000))) * ((12:ℚ)/((6:ℚ)-12*((1147:ℚ)/6000)))^l) : ℚ) : ℝ) *
      ((((((349/1800) : ℚ) : ℝ) - (((1147/6000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((212/1125) : ℚ) : ℝ) - (((1147/6000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((212/1125) : ℚ) : ℝ)..(((349/1800) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((212:ℚ)/1125)) (q := ((349:ℚ)/1800)) (c := ((1147:ℚ)/6000)) (d := ((49:ℚ)/18000))
    (a := ((1:ℚ)/12)) (r := ((1:ℚ)/12)) (eB := 1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1147:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1147:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := (2 * (∑ j ∈ range 40, (((((((1147:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((1147:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((349:ℚ)/1800))) - 1) / ((((5:ℚ) - 12*((349:ℚ)/1800))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((1147:ℚ)/6000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((1147:ℚ)/6000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((1147:ℚ)/6000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((1147:ℚ)/6000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((1147:ℚ)/6000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((1147:ℚ)/6000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((1147:ℚ)/6000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((1147:ℚ)/6000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((349:ℚ)/1800)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((349:ℚ)/1800)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1147:ℚ)/6000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((349:ℚ)/1800))) - 1) / ((((5:ℚ) - 12*((349:ℚ)/1800))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := (((((1147:ℚ)/6000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 ((((1147:ℚ)/6000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ)
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (1:ℝ) ≤ (x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ) := by
      rw [le_div_iff₀ (by norm_num)]
      push_cast
      linarith [hx.1]
    have h2 := Real.log_nonneg h1
    push_cast at h2 ⊢
    linarith [h2])
      (by norm_num)
      (by push_cast; norm_num)

private theorem A4_cert : ((984933229/500000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1147:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1147:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1147:ℚ)/6000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((1147:ℚ)/6000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((1147:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((1147:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((1147:ℚ)/6000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((1147:ℚ)/6000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((1147:ℚ)/6000) + 2/((6:ℚ) - 12*((1147:ℚ)/6000)) - ((1:ℚ)/6/((1147:ℚ)/6000) * ((((49:ℚ)/18000)/((1147:ℚ)/6000))^(4+1)/(1 - ((49:ℚ)/18000)/((1147:ℚ)/6000))) + 2/((6:ℚ) - 12*((1147:ℚ)/6000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1147:ℚ)/6000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1147:ℚ)/6000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((1147:ℚ)/6000)^(l+1) + (2/((6:ℚ)-12*((1147:ℚ)/6000))) * ((12:ℚ)/((6:ℚ)-12*((1147:ℚ)/6000)))^l) : ℚ) *
      (((((349:ℚ)/1800) - ((1147:ℚ)/6000)) ^ (i + j + l + 1) - (((212:ℚ)/1125) - ((1147:ℚ)/6000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma A4_certR : (((984933229/500000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1147:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1147:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1147:ℚ)/6000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((1147:ℚ)/6000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((1147:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((1147:ℚ)/6000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((1147:ℚ)/6000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((1147:ℚ)/6000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((1147:ℚ)/6000) + 2/((6:ℚ) - 12*((1147:ℚ)/6000)) - ((1:ℚ)/6/((1147:ℚ)/6000) * ((((49:ℚ)/18000)/((1147:ℚ)/6000))^(4+1)/(1 - ((49:ℚ)/18000)/((1147:ℚ)/6000))) + 2/((6:ℚ) - 12*((1147:ℚ)/6000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1147:ℚ)/6000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1147:ℚ)/6000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((1147:ℚ)/6000)^(l+1) + (2/((6:ℚ)-12*((1147:ℚ)/6000))) * ((12:ℚ)/((6:ℚ)-12*((1147:ℚ)/6000)))^l) : ℚ) : ℝ) *
      ((((((349/1800) : ℚ) : ℝ) - (((1147/6000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((212/1125) : ℚ) : ℝ) - (((1147/6000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := A4_cert
  exact_mod_cast h

/-! #### panel A5 -/
private lemma A5_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3539:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3539:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3539:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3539:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((3539:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3539:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3539:ℚ)/18000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3539:ℚ)/18000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3539:ℚ)/18000) + 2/((6:ℚ) - 12*((3539:ℚ)/18000)) - ((1:ℚ)/6/((3539:ℚ)/18000) * ((((49:ℚ)/18000)/((3539:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3539:ℚ)/18000))) + 2/((6:ℚ) - 12*((3539:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3539:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3539:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3539:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3539:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3539:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((299/1500) : ℚ) : ℝ) - (((3539/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((349/1800) : ℚ) : ℝ) - (((3539/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((349/1800) : ℚ) : ℝ)..(((299/1500) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((349:ℚ)/1800)) (q := ((299:ℚ)/1500)) (c := ((3539:ℚ)/18000)) (d := ((49:ℚ)/18000))
    (a := ((1:ℚ)/12)) (r := ((1:ℚ)/12)) (eB := 1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3539:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3539:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := (2 * (∑ j ∈ range 40, (((((((3539:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3539:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((299:ℚ)/1500))) - 1) / ((((5:ℚ) - 12*((299:ℚ)/1500))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3539:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((3539:ℚ)/18000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3539:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((3539:ℚ)/18000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((3539:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3539:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((3539:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3539:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((299:ℚ)/1500)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((299:ℚ)/1500)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3539:ℚ)/18000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((299:ℚ)/1500))) - 1) / ((((5:ℚ) - 12*((299:ℚ)/1500))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := (((((3539:ℚ)/18000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 ((((3539:ℚ)/18000) - ((1:ℚ)/12)) / ((1:ℚ)/12) : ℚ)
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (1:ℝ) ≤ (x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ) := by
      rw [le_div_iff₀ (by norm_num)]
      push_cast
      linarith [hx.1]
    have h2 := Real.log_nonneg h1
    push_cast at h2 ⊢
    linarith [h2])
      (by norm_num)
      (by push_cast; norm_num)

private theorem A5_cert : ((2265746597/1000000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3539:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3539:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3539:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3539:ℚ)/18000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((3539:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3539:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3539:ℚ)/18000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3539:ℚ)/18000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((3539:ℚ)/18000) + 2/((6:ℚ) - 12*((3539:ℚ)/18000)) - ((1:ℚ)/6/((3539:ℚ)/18000) * ((((49:ℚ)/18000)/((3539:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3539:ℚ)/18000))) + 2/((6:ℚ) - 12*((3539:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3539:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3539:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3539:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3539:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3539:ℚ)/18000)))^l) : ℚ) *
      (((((299:ℚ)/1500) - ((3539:ℚ)/18000)) ^ (i + j + l + 1) - (((349:ℚ)/1800) - ((3539:ℚ)/18000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma A5_certR : (((2265746597/1000000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3539:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3539:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3539:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3539:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (1:ℚ)*(2 * (∑ j ∈ range 40, (((((((3539:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) - 1) / ((((((3539:ℚ)/18000) - ((1:ℚ)/12))/((1:ℚ)/12))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3539:ℚ)/18000) - ((1:ℚ)/12)))^(4+1) else 1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3539:ℚ)/18000) - ((1:ℚ)/12)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3539:ℚ)/18000) + 2/((6:ℚ) - 12*((3539:ℚ)/18000)) - ((1:ℚ)/6/((3539:ℚ)/18000) * ((((49:ℚ)/18000)/((3539:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3539:ℚ)/18000))) + 2/((6:ℚ) - 12*((3539:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3539:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3539:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3539:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3539:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3539:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((299/1500) : ℚ) : ℝ) - (((3539/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((349/1800) : ℚ) : ℝ) - (((3539/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := A5_cert
  exact_mod_cast h

/-! #### panel B0 -/
private lemma B0_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3637:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3637:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3637:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3637:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3637:ℚ)/18000) + 2/((6:ℚ) - 12*((3637:ℚ)/18000)) - ((1:ℚ)/6/((3637:ℚ)/18000) * ((((49:ℚ)/18000)/((3637:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3637:ℚ)/18000))) + 2/((6:ℚ) - 12*((3637:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3637:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3637:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3637:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3637:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3637:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((1843/9000) : ℚ) : ℝ) - (((3637/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((299/1500) : ℚ) : ℝ) - (((3637/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((299/1500) : ℚ) : ℝ)..(((1843/9000) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((299:ℚ)/1500)) (q := ((1843:ℚ)/9000)) (c := ((3637:ℚ)/18000)) (d := ((49:ℚ)/18000))
    (a := ((29:ℚ)/250)) (r := ((29:ℚ)/250)) (eB := -1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3637:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3637:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := -(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1843:ℚ)/9000))) - 1) / ((((5:ℚ) - 12*((1843:ℚ)/9000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3637:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((3637:ℚ)/18000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3637:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((3637:ℚ)/18000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((3637:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3637:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((3637:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3637:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((1843:ℚ)/9000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((1843:ℚ)/9000)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3637:ℚ)/18000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1843:ℚ)/9000))) - 1) / ((((5:ℚ) - 12*((1843:ℚ)/9000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((29:ℚ)/250) / (((3637:ℚ)/18000) - ((29:ℚ)/250)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((29:ℚ)/250) / (((3637:ℚ)/18000) - ((29:ℚ)/250)) : ℚ)
    have e : (((((3637:ℚ)/18000) - ((29:ℚ)/250)) / ((29:ℚ)/250) : ℚ) : ℝ) = (((((29:ℚ)/250) / (((3637:ℚ)/18000) - ((29:ℚ)/250)) : ℚ) : ℝ))⁻¹ := by push_cast; norm_num
    rw [e, Real.log_inv]
    simp only [Rat.cast_neg] at ⊢
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by norm_num)]
      push_cast
      linarith [hx.2]
    have h2 : (0:ℝ) ≤ (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) := by
      apply div_nonneg _ (by norm_num)
      push_cast
      linarith [hx.1]
    have h3 := Real.log_nonpos h2 h1
    push_cast at h3 ⊢
    linarith [h3])
      (by norm_num)
      (by push_cast; norm_num)

private theorem B0_cert : ((106569871/50000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3637:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3637:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3637:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3637:ℚ)/18000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((3637:ℚ)/18000) + 2/((6:ℚ) - 12*((3637:ℚ)/18000)) - ((1:ℚ)/6/((3637:ℚ)/18000) * ((((49:ℚ)/18000)/((3637:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3637:ℚ)/18000))) + 2/((6:ℚ) - 12*((3637:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3637:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3637:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3637:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3637:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3637:ℚ)/18000)))^l) : ℚ) *
      (((((1843:ℚ)/9000) - ((3637:ℚ)/18000)) ^ (i + j + l + 1) - (((299:ℚ)/1500) - ((3637:ℚ)/18000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma B0_certR : (((106569871/50000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3637:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3637:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3637:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3637:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3637:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3637:ℚ)/18000) + 2/((6:ℚ) - 12*((3637:ℚ)/18000)) - ((1:ℚ)/6/((3637:ℚ)/18000) * ((((49:ℚ)/18000)/((3637:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3637:ℚ)/18000))) + 2/((6:ℚ) - 12*((3637:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3637:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3637:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3637:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3637:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3637:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((1843/9000) : ℚ) : ℝ) - (((3637/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((299/1500) : ℚ) : ℝ) - (((3637/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := B0_cert
  exact_mod_cast h

/-! #### panel B1 -/
private lemma B1_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((83:ℚ)/400))) - 1) / ((((5:ℚ) - 12*((83:ℚ)/400))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((83:ℚ)/400)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((83:ℚ)/400)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((83:ℚ)/400) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((83:ℚ)/400) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((83:ℚ)/400) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((83:ℚ)/400) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((83:ℚ)/400) + 2/((6:ℚ) - 12*((83:ℚ)/400)) - ((1:ℚ)/6/((83:ℚ)/400) * ((((49:ℚ)/18000)/((83:ℚ)/400))^(4+1)/(1 - ((49:ℚ)/18000)/((83:ℚ)/400))) + 2/((6:ℚ) - 12*((83:ℚ)/400)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((83:ℚ)/400)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((83:ℚ)/400))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((83:ℚ)/400)^(l+1) + (2/((6:ℚ)-12*((83:ℚ)/400))) * ((12:ℚ)/((6:ℚ)-12*((83:ℚ)/400)))^l) : ℚ) : ℝ) *
      ((((((473/2250) : ℚ) : ℝ) - (((83/400) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((1843/9000) : ℚ) : ℝ) - (((83/400) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((1843/9000) : ℚ) : ℝ)..(((473/2250) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((1843:ℚ)/9000)) (q := ((473:ℚ)/2250)) (c := ((83:ℚ)/400)) (d := ((49:ℚ)/18000))
    (a := ((29:ℚ)/250)) (r := ((29:ℚ)/250)) (eB := -1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((83:ℚ)/400))) - 1) / ((((5:ℚ) - 12*((83:ℚ)/400))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := -(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((83:ℚ)/400) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((83:ℚ)/400) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((473:ℚ)/2250))) - 1) / ((((5:ℚ) - 12*((473:ℚ)/2250))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((83:ℚ)/400)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((83:ℚ)/400)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((83:ℚ)/400)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((83:ℚ)/400)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((83:ℚ)/400)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((83:ℚ)/400)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((83:ℚ)/400)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((83:ℚ)/400)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((473:ℚ)/2250)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((473:ℚ)/2250)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((83:ℚ)/400)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((473:ℚ)/2250))) - 1) / ((((5:ℚ) - 12*((473:ℚ)/2250))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((29:ℚ)/250) / (((83:ℚ)/400) - ((29:ℚ)/250)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((29:ℚ)/250) / (((83:ℚ)/400) - ((29:ℚ)/250)) : ℚ)
    have e : (((((83:ℚ)/400) - ((29:ℚ)/250)) / ((29:ℚ)/250) : ℚ) : ℝ) = (((((29:ℚ)/250) / (((83:ℚ)/400) - ((29:ℚ)/250)) : ℚ) : ℝ))⁻¹ := by push_cast; norm_num
    rw [e, Real.log_inv]
    simp only [Rat.cast_neg] at ⊢
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by norm_num)]
      push_cast
      linarith [hx.2]
    have h2 : (0:ℝ) ≤ (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) := by
      apply div_nonneg _ (by norm_num)
      push_cast
      linarith [hx.1]
    have h3 := Real.log_nonpos h2 h1
    push_cast at h3 ⊢
    linarith [h3])
      (by norm_num)
      (by push_cast; norm_num)

private theorem B1_cert : ((408609069/250000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((83:ℚ)/400))) - 1) / ((((5:ℚ) - 12*((83:ℚ)/400))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((83:ℚ)/400)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((83:ℚ)/400)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((83:ℚ)/400) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((83:ℚ)/400) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((83:ℚ)/400) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((83:ℚ)/400) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((83:ℚ)/400) + 2/((6:ℚ) - 12*((83:ℚ)/400)) - ((1:ℚ)/6/((83:ℚ)/400) * ((((49:ℚ)/18000)/((83:ℚ)/400))^(4+1)/(1 - ((49:ℚ)/18000)/((83:ℚ)/400))) + 2/((6:ℚ) - 12*((83:ℚ)/400)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((83:ℚ)/400)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((83:ℚ)/400))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((83:ℚ)/400)^(l+1) + (2/((6:ℚ)-12*((83:ℚ)/400))) * ((12:ℚ)/((6:ℚ)-12*((83:ℚ)/400)))^l) : ℚ) *
      (((((473:ℚ)/2250) - ((83:ℚ)/400)) ^ (i + j + l + 1) - (((1843:ℚ)/9000) - ((83:ℚ)/400)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma B1_certR : (((408609069/250000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((83:ℚ)/400))) - 1) / ((((5:ℚ) - 12*((83:ℚ)/400))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((83:ℚ)/400)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((83:ℚ)/400)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((83:ℚ)/400) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((83:ℚ)/400) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((83:ℚ)/400) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((83:ℚ)/400) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((83:ℚ)/400) + 2/((6:ℚ) - 12*((83:ℚ)/400)) - ((1:ℚ)/6/((83:ℚ)/400) * ((((49:ℚ)/18000)/((83:ℚ)/400))^(4+1)/(1 - ((49:ℚ)/18000)/((83:ℚ)/400))) + 2/((6:ℚ) - 12*((83:ℚ)/400)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((83:ℚ)/400)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((83:ℚ)/400))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((83:ℚ)/400)^(l+1) + (2/((6:ℚ)-12*((83:ℚ)/400))) * ((12:ℚ)/((6:ℚ)-12*((83:ℚ)/400)))^l) : ℚ) : ℝ) *
      ((((((473/2250) : ℚ) : ℝ) - (((83/400) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((1843/9000) : ℚ) : ℝ) - (((83/400) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := B1_cert
  exact_mod_cast h

/-! #### panel B2 -/
private lemma B2_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3833:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3833:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3833:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3833:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3833:ℚ)/18000) + 2/((6:ℚ) - 12*((3833:ℚ)/18000)) - ((1:ℚ)/6/((3833:ℚ)/18000) * ((((49:ℚ)/18000)/((3833:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3833:ℚ)/18000))) + 2/((6:ℚ) - 12*((3833:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3833:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3833:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3833:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3833:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3833:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((647/3000) : ℚ) : ℝ) - (((3833/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((473/2250) : ℚ) : ℝ) - (((3833/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((473/2250) : ℚ) : ℝ)..(((647/3000) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((473:ℚ)/2250)) (q := ((647:ℚ)/3000)) (c := ((3833:ℚ)/18000)) (d := ((49:ℚ)/18000))
    (a := ((29:ℚ)/250)) (r := ((29:ℚ)/250)) (eB := -1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3833:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3833:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := -(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((647:ℚ)/3000))) - 1) / ((((5:ℚ) - 12*((647:ℚ)/3000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3833:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((3833:ℚ)/18000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3833:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((3833:ℚ)/18000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((3833:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3833:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((3833:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3833:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((647:ℚ)/3000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((647:ℚ)/3000)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3833:ℚ)/18000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((647:ℚ)/3000))) - 1) / ((((5:ℚ) - 12*((647:ℚ)/3000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((29:ℚ)/250) / (((3833:ℚ)/18000) - ((29:ℚ)/250)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((29:ℚ)/250) / (((3833:ℚ)/18000) - ((29:ℚ)/250)) : ℚ)
    have e : (((((3833:ℚ)/18000) - ((29:ℚ)/250)) / ((29:ℚ)/250) : ℚ) : ℝ) = (((((29:ℚ)/250) / (((3833:ℚ)/18000) - ((29:ℚ)/250)) : ℚ) : ℝ))⁻¹ := by push_cast; norm_num
    rw [e, Real.log_inv]
    simp only [Rat.cast_neg] at ⊢
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by norm_num)]
      push_cast
      linarith [hx.2]
    have h2 : (0:ℝ) ≤ (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) := by
      apply div_nonneg _ (by norm_num)
      push_cast
      linarith [hx.1]
    have h3 := Real.log_nonpos h2 h1
    push_cast at h3 ⊢
    linarith [h3])
      (by norm_num)
      (by push_cast; norm_num)

private theorem B2_cert : ((1192681691/1000000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3833:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3833:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3833:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3833:ℚ)/18000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((3833:ℚ)/18000) + 2/((6:ℚ) - 12*((3833:ℚ)/18000)) - ((1:ℚ)/6/((3833:ℚ)/18000) * ((((49:ℚ)/18000)/((3833:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3833:ℚ)/18000))) + 2/((6:ℚ) - 12*((3833:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3833:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3833:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3833:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3833:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3833:ℚ)/18000)))^l) : ℚ) *
      (((((647:ℚ)/3000) - ((3833:ℚ)/18000)) ^ (i + j + l + 1) - (((473:ℚ)/2250) - ((3833:ℚ)/18000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma B2_certR : (((1192681691/1000000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3833:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3833:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3833:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3833:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3833:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3833:ℚ)/18000) + 2/((6:ℚ) - 12*((3833:ℚ)/18000)) - ((1:ℚ)/6/((3833:ℚ)/18000) * ((((49:ℚ)/18000)/((3833:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3833:ℚ)/18000))) + 2/((6:ℚ) - 12*((3833:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3833:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3833:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3833:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3833:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3833:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((647/3000) : ℚ) : ℝ) - (((3833/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((473/2250) : ℚ) : ℝ) - (((3833/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := B2_cert
  exact_mod_cast h

/-! #### panel B3 -/
private lemma B3_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3931:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3931:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3931:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3931:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3931:ℚ)/18000) + 2/((6:ℚ) - 12*((3931:ℚ)/18000)) - ((1:ℚ)/6/((3931:ℚ)/18000) * ((((49:ℚ)/18000)/((3931:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3931:ℚ)/18000))) + 2/((6:ℚ) - 12*((3931:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3931:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3931:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3931:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3931:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3931:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((199/900) : ℚ) : ℝ) - (((3931/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((647/3000) : ℚ) : ℝ) - (((3931/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((647/3000) : ℚ) : ℝ)..(((199/900) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((647:ℚ)/3000)) (q := ((199:ℚ)/900)) (c := ((3931:ℚ)/18000)) (d := ((49:ℚ)/18000))
    (a := ((29:ℚ)/250)) (r := ((29:ℚ)/250)) (eB := -1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3931:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3931:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := -(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((199:ℚ)/900))) - 1) / ((((5:ℚ) - 12*((199:ℚ)/900))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3931:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((3931:ℚ)/18000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((3931:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((3931:ℚ)/18000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((3931:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3931:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((3931:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((3931:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((199:ℚ)/900)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((199:ℚ)/900)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3931:ℚ)/18000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((199:ℚ)/900))) - 1) / ((((5:ℚ) - 12*((199:ℚ)/900))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((29:ℚ)/250) / (((3931:ℚ)/18000) - ((29:ℚ)/250)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((29:ℚ)/250) / (((3931:ℚ)/18000) - ((29:ℚ)/250)) : ℚ)
    have e : (((((3931:ℚ)/18000) - ((29:ℚ)/250)) / ((29:ℚ)/250) : ℚ) : ℝ) = (((((29:ℚ)/250) / (((3931:ℚ)/18000) - ((29:ℚ)/250)) : ℚ) : ℝ))⁻¹ := by push_cast; norm_num
    rw [e, Real.log_inv]
    simp only [Rat.cast_neg] at ⊢
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by norm_num)]
      push_cast
      linarith [hx.2]
    have h2 : (0:ℝ) ≤ (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) := by
      apply div_nonneg _ (by norm_num)
      push_cast
      linarith [hx.1]
    have h3 := Real.log_nonpos h2 h1
    push_cast at h3 ⊢
    linarith [h3])
      (by norm_num)
      (by push_cast; norm_num)

private theorem B3_cert : ((3999819/5000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3931:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3931:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3931:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3931:ℚ)/18000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((3931:ℚ)/18000) + 2/((6:ℚ) - 12*((3931:ℚ)/18000)) - ((1:ℚ)/6/((3931:ℚ)/18000) * ((((49:ℚ)/18000)/((3931:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3931:ℚ)/18000))) + 2/((6:ℚ) - 12*((3931:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3931:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3931:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3931:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3931:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3931:ℚ)/18000)))^l) : ℚ) *
      (((((199:ℚ)/900) - ((3931:ℚ)/18000)) ^ (i + j + l + 1) - (((647:ℚ)/3000) - ((3931:ℚ)/18000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma B3_certR : (((3999819/5000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((3931:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((3931:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((3931:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((3931:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((3931:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((3931:ℚ)/18000) + 2/((6:ℚ) - 12*((3931:ℚ)/18000)) - ((1:ℚ)/6/((3931:ℚ)/18000) * ((((49:ℚ)/18000)/((3931:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((3931:ℚ)/18000))) + 2/((6:ℚ) - 12*((3931:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3931:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((3931:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((3931:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((3931:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((3931:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((199/900) : ℚ) : ℝ) - (((3931/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((647/3000) : ℚ) : ℝ) - (((3931/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := B3_cert
  exact_mod_cast h

/-! #### panel B4 -/
private lemma B4_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1343:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1343:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1343:ℚ)/6000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((1343:ℚ)/6000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((1343:ℚ)/6000) + 2/((6:ℚ) - 12*((1343:ℚ)/6000)) - ((1:ℚ)/6/((1343:ℚ)/6000) * ((((49:ℚ)/18000)/((1343:ℚ)/6000))^(4+1)/(1 - ((49:ℚ)/18000)/((1343:ℚ)/6000))) + 2/((6:ℚ) - 12*((1343:ℚ)/6000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1343:ℚ)/6000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1343:ℚ)/6000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((1343:ℚ)/6000)^(l+1) + (2/((6:ℚ)-12*((1343:ℚ)/6000))) * ((12:ℚ)/((6:ℚ)-12*((1343:ℚ)/6000)))^l) : ℚ) : ℝ) *
      ((((((2039/9000) : ℚ) : ℝ) - (((1343/6000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((199/900) : ℚ) : ℝ) - (((1343/6000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((199/900) : ℚ) : ℝ)..(((2039/9000) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((199:ℚ)/900)) (q := ((2039:ℚ)/9000)) (c := ((1343:ℚ)/6000)) (d := ((49:ℚ)/18000))
    (a := ((29:ℚ)/250)) (r := ((29:ℚ)/250)) (eB := -1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1343:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1343:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := -(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((2039:ℚ)/9000))) - 1) / ((((5:ℚ) - 12*((2039:ℚ)/9000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((1343:ℚ)/6000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((1343:ℚ)/6000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((1343:ℚ)/6000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((1343:ℚ)/6000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((1343:ℚ)/6000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((1343:ℚ)/6000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((1343:ℚ)/6000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((1343:ℚ)/6000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((2039:ℚ)/9000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((2039:ℚ)/9000)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1343:ℚ)/6000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((2039:ℚ)/9000))) - 1) / ((((5:ℚ) - 12*((2039:ℚ)/9000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((29:ℚ)/250) / (((1343:ℚ)/6000) - ((29:ℚ)/250)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((29:ℚ)/250) / (((1343:ℚ)/6000) - ((29:ℚ)/250)) : ℚ)
    have e : (((((1343:ℚ)/6000) - ((29:ℚ)/250)) / ((29:ℚ)/250) : ℚ) : ℝ) = (((((29:ℚ)/250) / (((1343:ℚ)/6000) - ((29:ℚ)/250)) : ℚ) : ℝ))⁻¹ := by push_cast; norm_num
    rw [e, Real.log_inv]
    simp only [Rat.cast_neg] at ⊢
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by norm_num)]
      push_cast
      linarith [hx.2]
    have h2 : (0:ℝ) ≤ (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) := by
      apply div_nonneg _ (by norm_num)
      push_cast
      linarith [hx.1]
    have h3 := Real.log_nonpos h2 h1
    push_cast at h3 ⊢
    linarith [h3])
      (by norm_num)
      (by push_cast; norm_num)

private theorem B4_cert : ((112798419/250000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1343:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1343:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1343:ℚ)/6000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((1343:ℚ)/6000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((1343:ℚ)/6000) + 2/((6:ℚ) - 12*((1343:ℚ)/6000)) - ((1:ℚ)/6/((1343:ℚ)/6000) * ((((49:ℚ)/18000)/((1343:ℚ)/6000))^(4+1)/(1 - ((49:ℚ)/18000)/((1343:ℚ)/6000))) + 2/((6:ℚ) - 12*((1343:ℚ)/6000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1343:ℚ)/6000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1343:ℚ)/6000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((1343:ℚ)/6000)^(l+1) + (2/((6:ℚ)-12*((1343:ℚ)/6000))) * ((12:ℚ)/((6:ℚ)-12*((1343:ℚ)/6000)))^l) : ℚ) *
      (((((2039:ℚ)/9000) - ((1343:ℚ)/6000)) ^ (i + j + l + 1) - (((199:ℚ)/900) - ((1343:ℚ)/6000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma B4_certR : (((112798419/250000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((1343:ℚ)/6000))) - 1) / ((((5:ℚ) - 12*((1343:ℚ)/6000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((1343:ℚ)/6000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((1343:ℚ)/6000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((1343:ℚ)/6000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((1343:ℚ)/6000) + 2/((6:ℚ) - 12*((1343:ℚ)/6000)) - ((1:ℚ)/6/((1343:ℚ)/6000) * ((((49:ℚ)/18000)/((1343:ℚ)/6000))^(4+1)/(1 - ((49:ℚ)/18000)/((1343:ℚ)/6000))) + 2/((6:ℚ) - 12*((1343:ℚ)/6000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1343:ℚ)/6000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((1343:ℚ)/6000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((1343:ℚ)/6000)^(l+1) + (2/((6:ℚ)-12*((1343:ℚ)/6000))) * ((12:ℚ)/((6:ℚ)-12*((1343:ℚ)/6000)))^l) : ℚ) : ℝ) *
      ((((((2039/9000) : ℚ) : ℝ) - (((1343/6000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((199/900) : ℚ) : ℝ) - (((1343/6000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := B4_cert
  exact_mod_cast h

/-! #### panel B5 -/
private lemma B5_pan :
    (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((4127:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((4127:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((4127:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((4127:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((4127:ℚ)/18000) + 2/((6:ℚ) - 12*((4127:ℚ)/18000)) - ((1:ℚ)/6/((4127:ℚ)/18000) * ((((49:ℚ)/18000)/((4127:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((4127:ℚ)/18000))) + 2/((6:ℚ) - 12*((4127:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((4127:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((4127:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((4127:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((4127:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((4127:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((29/125) : ℚ) : ℝ) - (((4127/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((2039/9000) : ℚ) : ℝ) - (((4127/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1)))
      ≤ ∫ x in (((2039/9000) : ℚ) : ℝ)..(((29/125) : ℚ) : ℝ),
          Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  exact panel_low (p := ((2039:ℚ)/9000)) (q := ((29:ℚ)/125)) (c := ((4127:ℚ)/18000)) (d := ((49:ℚ)/18000))
    (a := ((29:ℚ)/250)) (r := ((29:ℚ)/250)) (eB := -1)
    (lA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((4127:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((4127:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (lB := -(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1)))) (mlA := (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((29:ℚ)/125))) - 1) / ((((5:ℚ) - 12*((29:ℚ)/125))) + 1)) ^ (2 * j + 1) / (2 * j + 1))))
    (na := 4) (nb := 4) (nc := 4)
    (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((4127:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((4127:ℚ)/18000)) : ℚ)
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((4127:ℚ)/18000)) : ℚ) : ℝ)) (by norm_num)).2
    rw [Wu04Integral.logUpper, Wu04Integral.logLower] at hb
    have hc1 := rat_logLower_cast' 40 ((((5:ℚ) - 12*((4127:ℚ)/18000)) : ℚ))
    have hz : (2:ℝ) * (((((((5:ℚ) - 12*((4127:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((4127:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ (2*40+1) / (1 - (((((((5:ℚ) - 12*((4127:ℚ)/18000)) : ℚ)) : ℝ) - 1) / ((((((5:ℚ) - 12*((4127:ℚ)/18000)) : ℚ)) : ℝ) + 1)) ^ 2) ≤ 1/1000000 := by
      push_cast
      norm_num
    push_cast at hb hc1 ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((5:ℚ) - 12*((29:ℚ)/125)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((5:ℚ) - 12*((29:ℚ)/125)) : ℚ)
    linarith)
      (by decide +kernel)
      (by
    have hq : (4 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((4127:ℚ)/18000)))^(4+1) + 1/1000000 : ℚ) ≤ (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((29:ℚ)/125))) - 1) / ((((5:ℚ) - 12*((29:ℚ)/125))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) := by decide +kernel
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast ⊢
    linarith)
      (by
    have hb := (Wu04Integral.log_bounds 40 (y := ((((29:ℚ)/250) / (((4127:ℚ)/18000) - ((29:ℚ)/250)) : ℚ) : ℝ)) (by norm_num)).1
    have hc1 := rat_logLower_cast' 40 (((29:ℚ)/250) / (((4127:ℚ)/18000) - ((29:ℚ)/250)) : ℚ)
    have e : (((((4127:ℚ)/18000) - ((29:ℚ)/250)) / ((29:ℚ)/250) : ℚ) : ℝ) = (((((29:ℚ)/250) / (((4127:ℚ)/18000) - ((29:ℚ)/250)) : ℚ) : ℝ))⁻¹ := by push_cast; norm_num
    rw [e, Real.log_inv]
    simp only [Rat.cast_neg] at ⊢
    linarith)
      (by norm_num)
      (by
    intro x hx
    rw [Set.mem_Icc] at hx
    have h1 : (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by norm_num)]
      push_cast
      linarith [hx.2]
    have h2 : (0:ℝ) ≤ (x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ) := by
      apply div_nonneg _ (by norm_num)
      push_cast
      linarith [hx.1]
    have h3 := Real.log_nonpos h2 h1
    push_cast at h3 ⊢
    linarith [h3])
      (by norm_num)
      (by push_cast; norm_num)

private theorem B5_cert : ((17770791/125000000000) : ℚ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      ((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((4127:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((4127:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((4127:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((4127:ℚ)/18000)))^i / (i:ℚ)) : ℚ) * ((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) * ((if l = 0 then (1:ℚ)/6/((4127:ℚ)/18000) + 2/((6:ℚ) - 12*((4127:ℚ)/18000)) - ((1:ℚ)/6/((4127:ℚ)/18000) * ((((49:ℚ)/18000)/((4127:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((4127:ℚ)/18000))) + 2/((6:ℚ) - 12*((4127:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((4127:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((4127:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((4127:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((4127:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((4127:ℚ)/18000)))^l) : ℚ) *
      (((((29:ℚ)/125) - ((4127:ℚ)/18000)) ^ (i + j + l + 1) - (((2039:ℚ)/9000) - ((4127:ℚ)/18000)) ^ (i + j + l + 1)) / ((i:ℚ) + (j:ℚ) + (l:ℚ) + 1))) := by
  decide +kernel

private lemma B5_certR : (((17770791/125000000000) : ℚ) : ℝ) ≤ (∑ l ∈ range 5, ∑ j ∈ range 5, ∑ i ∈ range 5,
      (((if i = 0 then (2 * (∑ j ∈ range 40, (((((5:ℚ) - 12*((4127:ℚ)/18000))) - 1) / ((((5:ℚ) - 12*((4127:ℚ)/18000))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((12:ℚ)*((49:ℚ)/18000))/((5:ℚ) - 12*((4127:ℚ)/18000)))^(4+1) else (-1 : ℚ)^(i-1) * (-(12:ℚ)/((5:ℚ) - 12*((4127:ℚ)/18000)))^i / (i:ℚ)) : ℚ) : ℝ) * (((if j = 0 then (-1:ℚ)*-(2 * (∑ j ∈ range 40, ((((((29:ℚ)/250)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))) - 1) / (((((29:ℚ)/250)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))) + 1)) ^ (2 * j + 1) / (2 * j + 1))) - 2 * (((49:ℚ)/18000)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))^(4+1) else -1 * (-1 : ℚ)^(j-1) * ((1:ℚ)/(((4127:ℚ)/18000) - ((29:ℚ)/250)))^j / (j:ℚ)) : ℚ) : ℝ) * (((if l = 0 then (1:ℚ)/6/((4127:ℚ)/18000) + 2/((6:ℚ) - 12*((4127:ℚ)/18000)) - ((1:ℚ)/6/((4127:ℚ)/18000) * ((((49:ℚ)/18000)/((4127:ℚ)/18000))^(4+1)/(1 - ((49:ℚ)/18000)/((4127:ℚ)/18000))) + 2/((6:ℚ) - 12*((4127:ℚ)/18000)) * (((12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((4127:ℚ)/18000)))^(4+1)/(1 - (12:ℚ)*((49:ℚ)/18000)/((6:ℚ) - 12*((4127:ℚ)/18000))))) else (1:ℚ)/6 * (-1 : ℚ)^l / ((4127:ℚ)/18000)^(l+1) + (2/((6:ℚ)-12*((4127:ℚ)/18000))) * ((12:ℚ)/((6:ℚ)-12*((4127:ℚ)/18000)))^l) : ℚ) : ℝ) *
      ((((((29/125) : ℚ) : ℝ) - (((4127/18000) : ℚ) : ℝ)) ^ (i + j + l + 1) - ((((2039/9000) : ℚ) : ℝ) - (((4127/18000) : ℚ) : ℝ)) ^ (i + j + l + 1)) / ((i:ℝ) + (j:ℝ) + (l:ℝ) + 1))) := by
  have h := B5_cert
  exact_mod_cast h


private lemma F4A_ii : IntervalIntegrable
    (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x))
    volume (((1/6) : ℚ) : ℝ) (((299/1500) : ℚ) : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by push_cast; norm_num)]
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · exact ContinuousOn.log (by fun_prop) (fun x hx => by
        have h := hx.2; push_cast at h; linarith)
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log (by fun_prop)
      intro x hx
      have h := hx.1; push_cast at h
      exact ne_of_gt (div_pos (by linarith) (by norm_num))
  · exact (by fun_prop : ContinuousOn (fun x : ℝ => (6 - 12*x)*x) (Set.Icc (((1/6) : ℚ) : ℝ) (((299/1500) : ℚ) : ℝ)))
  · intro x hx
    have h1 : (0:ℝ) < 6 - 12*x := by have h := hx.2; push_cast at h; linarith
    have h2 : (0:ℝ) < x := by have h := hx.1; push_cast at h; linarith
    exact ne_of_gt (mul_pos h1 h2)


private lemma F4A_ii0 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((1/6) : ℚ) : ℝ) (((1549/9000) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4A_ii1 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((1549/9000) : ℚ) : ℝ) (((799/4500) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4A_ii2 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((799/4500) : ℚ) : ℝ) (((183/1000) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4A_ii3 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((183/1000) : ℚ) : ℝ) (((212/1125) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4A_ii4 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((212/1125) : ℚ) : ℝ) (((349/1800) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4A_ii5 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((349/1800) : ℚ) : ℝ) (((299/1500) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4A_cum2 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((1/6) : ℚ) : ℝ) (((799/4500) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)

private lemma F4A_cum3 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((1/6) : ℚ) : ℝ) (((183/1000) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)

private lemma F4A_cum4 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((1/6) : ℚ) : ℝ) (((212/1125) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)

private lemma F4A_cum5 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((1/6) : ℚ) : ℝ) (((349/1800) : ℚ) : ℝ) :=
  ii_mono F4A_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)




private lemma F4A_form :
    (∫ s in (2 * kappa1)..(kappa1 + kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log ((s - kappa1) / kappa1) / s))
      = ∫ x in (((1/6) : ℚ) : ℝ)..(((299/1500) : ℚ) : ℝ), Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  have h1 : (2 * kappa1 : ℝ) = (((1/6) : ℚ) : ℝ) := by norm_num [kappa1]
  have h2 : (kappa1 + kappa2 : ℝ) = (((299/1500) : ℚ) : ℝ) := by norm_num [kappa1, kappa2]
  rw [h1, h2]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by push_cast; norm_num)] at hx
  have hx1 : (0:ℝ) < x := by have h := hx.1; push_cast at h; linarith
  have hx2 : (0:ℝ) < 6 - 12*x := by have h := hx.2; push_cast at h; linarith
  simp only [kappa1]
  push_cast
  field_simp
  try ring


private lemma F4A_split :
    (∫ x in (((1/6) : ℚ) : ℝ)..(((299/1500) : ℚ) : ℝ), Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x))
      = ((((((∫ x in (((1/6) : ℚ) : ℝ)..(((1549/9000) : ℚ) : ℝ), Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x)) + (∫ x in (((1549/9000) : ℚ) : ℝ)..(((799/4500) : ℚ) : ℝ), Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x))) + (∫ x in (((799/4500) : ℚ) : ℝ)..(((183/1000) : ℚ) : ℝ), Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x))) + (∫ x in (((183/1000) : ℚ) : ℝ)..(((212/1125) : ℚ) : ℝ), Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x))) + (∫ x in (((212/1125) : ℚ) : ℝ)..(((349/1800) : ℚ) : ℝ), Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x))) + (∫ x in (((349/1800) : ℚ) : ℝ)..(((299/1500) : ℚ) : ℝ), Real.log (5 - 12*x) * (((1 : ℚ) : ℝ) * Real.log ((x - (((1/12) : ℚ) : ℝ)) / (((1/12) : ℚ) : ℝ))) / ((6 - 12*x)*x))) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals F4A_cum5 F4A_ii5]
  rw [← intervalIntegral.integral_add_adjacent_intervals F4A_cum4 F4A_ii4]
  rw [← intervalIntegral.integral_add_adjacent_intervals F4A_cum3 F4A_ii3]
  rw [← intervalIntegral.integral_add_adjacent_intervals F4A_cum2 F4A_ii2]
  rw [← intervalIntegral.integral_add_adjacent_intervals F4A_ii0 F4A_ii1]


private lemma F4B_ii : IntervalIntegrable
    (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x))
    volume (((299/1500) : ℚ) : ℝ) (((29/125) : ℚ) : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by push_cast; norm_num)]
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · exact ContinuousOn.log (by fun_prop) (fun x hx => by
        have h := hx.2; push_cast at h; linarith)
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log (by fun_prop)
      intro x hx
      have h := hx.1; push_cast at h
      exact ne_of_gt (div_pos (by linarith) (by norm_num))
  · exact (by fun_prop : ContinuousOn (fun x : ℝ => (6 - 12*x)*x) (Set.Icc (((299/1500) : ℚ) : ℝ) (((29/125) : ℚ) : ℝ)))
  · intro x hx
    have h1 : (0:ℝ) < 6 - 12*x := by have h := hx.2; push_cast at h; linarith
    have h2 : (0:ℝ) < x := by have h := hx.1; push_cast at h; linarith
    exact ne_of_gt (mul_pos h1 h2)


private lemma F4B_ii0 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((299/1500) : ℚ) : ℝ) (((1843/9000) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4B_ii1 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((1843/9000) : ℚ) : ℝ) (((473/2250) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4B_ii2 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((473/2250) : ℚ) : ℝ) (((647/3000) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4B_ii3 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((647/3000) : ℚ) : ℝ) (((199/900) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4B_ii4 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((199/900) : ℚ) : ℝ) (((2039/9000) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4B_ii5 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((2039/9000) : ℚ) : ℝ) (((29/125) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)


private lemma F4B_cum2 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((299/1500) : ℚ) : ℝ) (((473/2250) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)

private lemma F4B_cum3 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((299/1500) : ℚ) : ℝ) (((647/3000) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)

private lemma F4B_cum4 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((299/1500) : ℚ) : ℝ) (((199/900) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)

private lemma F4B_cum5 : IntervalIntegrable (fun x : ℝ => Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) volume (((299/1500) : ℚ) : ℝ) (((2039/9000) : ℚ) : ℝ) :=
  ii_mono F4B_ii (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)




private lemma F4B_form :
    (∫ s in (kappa1 + kappa2)..(2 * kappa2), Real.log (5 - 12 * s) / (6 - 12 * s) * (Real.log (kappa2 / (s - kappa2)) / s))
      = ∫ x in (((299/1500) : ℚ) : ℝ)..(((29/125) : ℚ) : ℝ), Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x) := by
  have h1 : (kappa1 + kappa2 : ℝ) = (((299/1500) : ℚ) : ℝ) := by norm_num [kappa1, kappa2]
  have h2 : (2 * kappa2 : ℝ) = (((29/125) : ℚ) : ℝ) := by norm_num [kappa2]
  rw [h1, h2]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by push_cast; norm_num)] at hx
  have hxpos : (0:ℝ) < x - 29/250 := by have h := hx.1; push_cast at h; linarith
  have hx1 : (0:ℝ) < x := by have h := hx.1; push_cast at h; linarith
  have hx2 : (0:ℝ) < 6 - 12*x := by have h := hx.2; push_cast at h; linarith
  simp only [kappa2]
  push_cast
  rw [Real.log_div (by norm_num : ((29:ℝ)/250) ≠ 0) (ne_of_gt hxpos),
    Real.log_div (ne_of_gt hxpos) (by norm_num : ((29:ℝ)/250) ≠ 0)]
  field_simp
  try ring


private lemma F4B_split :
    (∫ x in (((299/1500) : ℚ) : ℝ)..(((29/125) : ℚ) : ℝ), Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x))
      = ((((((∫ x in (((299/1500) : ℚ) : ℝ)..(((1843/9000) : ℚ) : ℝ), Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x)) + (∫ x in (((1843/9000) : ℚ) : ℝ)..(((473/2250) : ℚ) : ℝ), Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x))) + (∫ x in (((473/2250) : ℚ) : ℝ)..(((647/3000) : ℚ) : ℝ), Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x))) + (∫ x in (((647/3000) : ℚ) : ℝ)..(((199/900) : ℚ) : ℝ), Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x))) + (∫ x in (((199/900) : ℚ) : ℝ)..(((2039/9000) : ℚ) : ℝ), Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x))) + (∫ x in (((2039/9000) : ℚ) : ℝ)..(((29/125) : ℚ) : ℝ), Real.log (5 - 12*x) * (((-1 : ℚ) : ℝ) * Real.log ((x - (((29/250) : ℚ) : ℝ)) / (((29/250) : ℚ) : ℝ))) / ((6 - 12*x)*x))) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals F4B_cum5 F4B_ii5]
  rw [← intervalIntegral.integral_add_adjacent_intervals F4B_cum4 F4B_ii4]
  rw [← intervalIntegral.integral_add_adjacent_intervals F4B_cum3 F4B_ii3]
  rw [← intervalIntegral.integral_add_adjacent_intervals F4B_cum2 F4B_ii2]
  rw [← intervalIntegral.integral_add_adjacent_intervals F4B_ii0 F4B_ii1]


private lemma F4_consts : ((697375 / 1000000 : ℚ) : ℝ) ≤ 48 * (((70032747/250000000000) : ℚ) + ((396107859/500000000000) : ℚ) + ((619640949/500000000000) : ℚ) + ((1629574479/1000000000000) : ℚ) + ((984933229/500000000000) : ℚ) + ((2265746597/1000000000000) : ℚ) + ((106569871/50000000000) : ℚ) + ((408609069/250000000000) : ℚ) + ((1192681691/1000000000000) : ℚ) + ((3999819/5000000000) : ℚ) + ((112798419/250000000000) : ℚ) + ((17770791/125000000000) : ℚ) : ℚ) := by
  push_cast
  norm_num

private lemma F4_leaf_aux (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    0.697375 ≤ integralTerms F f ω 4 := by
  have hred := F4_sigma F f ω h
  rw [hred, F4A_form, F4A_split, F4B_form, F4B_split]
  have b_A0 := A0_pan
  have c_A0 := A0_certR
  have b_A1 := A1_pan
  have c_A1 := A1_certR
  have b_A2 := A2_pan
  have c_A2 := A2_certR
  have b_A3 := A3_pan
  have c_A3 := A3_certR
  have b_A4 := A4_pan
  have c_A4 := A4_certR
  have b_A5 := A5_pan
  have c_A5 := A5_certR
  have b_B0 := B0_pan
  have c_B0 := B0_certR
  have b_B1 := B1_pan
  have c_B1 := B1_certR
  have b_B2 := B2_pan
  have c_B2 := B2_certR
  have b_B3 := B3_pan
  have c_B3 := B3_certR
  have b_B4 := B4_pan
  have c_B4 := B4_certR
  have b_B5 := B5_pan
  have c_B5 := B5_certR
  have hc := F4_consts
  linarith [b_A0, b_A1, b_A2, b_A3, b_A4, b_A5, b_B0, b_B1, b_B2, b_B3, b_B4, b_B5, c_A0, c_A1, c_A2, c_A3, c_A4, c_A5, c_B0, c_B1, c_B2, c_B3, c_B4, c_B5, hc]

end quadrature

/-- LEAF. Wu 2004 page 42 final numerical display, F1.
The single actual integral coefficient satisfies its printed upper bound. -/
theorem numerical_F1 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 1 ≤ 3.891854 := by
  exact numerical_F1_aux F f ω h hω



/-- LEAF. Wu 2004 page 42 final numerical display, F2.
The single actual integral coefficient satisfies its printed upper bound. -/
theorem numerical_F2 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 2 ≤ 20.432098 := by
  have hsub := F2_sub_F3 (F := F) (f := f) h ω
  have h3 := numerical_F3_priv F f ω h hω
  have hlog := log_step_F2
  linarith

/-- LEAF. Wu 2004 page 42 final numerical display, F3.
The single actual integral coefficient satisfies its printed upper bound. -/
theorem numerical_F3 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 3 ≤ 17.327241 := by
  exact numerical_F3_priv F f ω h hω

/-- LEAF. Wu 2004 page 42 final numerical display, F4.
The single actual integral coefficient satisfies its printed lower bound. -/
theorem numerical_F4 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    0.697375 ≤ integralTerms F f ω 4 := by
  exact F4_leaf_aux F f ω h hω

/-- LEAF. Wu 2004 page 42 final numerical display, F5.
The single actual integral coefficient satisfies its printed lower bound. -/
theorem numerical_F5 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    2.118119 ≤ integralTerms F f ω 5 := by
  sorry

end LeanLab.ChenDoubleSieve.Task315
