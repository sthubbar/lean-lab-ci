/-
P0021, Bordignon-Starichkova 2022, arXiv 2211.08844: the shared input of INPUTS.md,
`li(y) ≤ ∫₂^y dt / log t + 1.046` for the principal value logarithmic integral, PROVED.

`li 2 = ∫₀² g` with `g t = 1 / log t - 1 / (t - 1)`, LiPV.lean `liPV_two`. True value
`li 2 = 1.0451637801...`; this file proves `li 2 ≤ 1.04581 < 1.046`.

* Right half: `g t ≤ (t + 2) / (3 (t + 1))` on `(1, 2]`, LiTwoA.lean `gli_le_right`, so
  `∫₁² g ≤ 1/3 + log (3/2) / 3 ≤ 0.468490`; true `∫₁² g = 0.467948`.
* Left half: for `0 < t < 1` and `N = 63`,
  `g t = Σ_{k<N} t^k + (1 - t^N) / log t + t^N g t`, and `g t ≤ 1 - t/2`, LiTwoA.lean
  `gli_le_left`. The middle term integrates to `-log (N + 1)` by Fubini:
  `(1 - t^N) / log t = -∫₀^N t^s ds`, and `∫₀¹ t^s dt = 1 / (s + 1)`. So
  `∫₀¹ g ≤ H_63 - 6 log 2 + 1/64 - 1/130 ≤ 0.577316`; true `∫₀¹ g = γ = 0.577216`.

AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1154. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.LiTwoA

namespace LeanLab.BS2022GRH.LiTwo
open Real Set MeasureTheory intervalIntegral

/-! ### The right half `[1, 2]` -/

/-- `log (3/2) ≤ 0.40547`, true `0.4054651`, from the Taylor series of `log (1 - 1/3)`. -/
lemma log_three_halves_le : log (3 / 2) ≤ 0.40547 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 3) (by norm_num [abs_of_pos]) 14
  have e : log (1 - 1 / 3 : ℝ) = -log (3 / 2) := by
    rw [show (1 - 1 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  rw [e] at h
  have h2 := (abs_le.mp h).1
  norm_num [Finset.sum_range_succ, abs_of_pos] at h2
  linarith

lemma integral_right_majorant :
    ∫ t in (1 : ℝ)..2, (t + 2) / (3 * (t + 1)) = 1 / 3 + log (3 / 2) / 3 := by
  have hc : EqOn (fun t : ℝ => (t + 2) / (3 * (t + 1))) (fun t => 1 / 3 + (1 / 3) * (t + 1)⁻¹)
      (uIcc 1 2) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have : t + 1 ≠ 0 := by linarith [ht.1]
    simp only
    field_simp
    ring
  rw [intervalIntegral.integral_congr hc]
  have hi : IntervalIntegrable (fun t : ℝ => (t + 1)⁻¹) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  rw [intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right (fun x : ℝ => x⁻¹),
    integral_inv_of_pos (by norm_num) (by norm_num)]
  norm_num
  ring

/-- `∫₁² g ≤ 1/3 + log (3/2) / 3`. -/
lemma integral_right : ∫ t in (1 : ℝ)..2, gli t ≤ 1 / 3 + log (3 / 2) / 3 := by
  have hint : IntervalIntegrable (fun t : ℝ => (t + 2) / (3 * (t + 1))) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have : 0 < 3 * (x + 1) := by linarith [hx.1]
    exact this.ne'
  rw [← integral_right_majorant]
  refine intervalIntegral.integral_mono_on (by norm_num) (gli_ii zero_le_one (by norm_num)) hint ?_
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; norm_num [gli]
  · exact gli_le_right h

/-! ### The left half `[0, 1]` -/

/-- The middle term `(1 - t^63) / log t`. -/
noncomputable def mfun (t : ℝ) : ℝ := (1 - t ^ 63) / log t

lemma gli_le_decomp {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    gli t ≤ (∑ k ∈ Finset.range 63, t ^ k) + mfun t + t ^ 63 * (1 - t / 2) := by
  have hg := gli_le_left ht ht1
  have hgeom : (∑ k ∈ Finset.range 63, t ^ k) = (t ^ 63 - 1) / (t - 1) :=
    geom_sum_eq (by linarith : t ≠ 1) 63
  have hlog : log t ≠ 0 := (log_neg ht ht1).ne
  have hs : t - 1 ≠ 0 := by linarith
  have hid : gli t = (∑ k ∈ Finset.range 63, t ^ k) + mfun t + t ^ 63 * gli t := by
    rw [hgeom]; unfold mfun gli; field_simp; ring
  have hp : 0 ≤ t ^ 63 := by positivity
  have hm := mul_le_mul_of_nonneg_left hg hp
  linarith

/-- `∫₀^63 t^s ds = (t^63 - 1) / log t` for `0 < t < 1`. -/
lemma F_eq {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∫ s in (0 : ℝ)..63, t ^ s = (t ^ 63 - 1) / log t := by
  have hl : log t ≠ 0 := (log_neg ht ht1).ne
  have hd : ∀ s ∈ uIcc (0 : ℝ) 63, HasDerivAt (fun s => t ^ s / log t) (t ^ s) s := by
    intro s _
    have h := ((Real.hasStrictDerivAt_const_rpow ht s).hasDerivAt).div_const (log t)
    refine h.congr_deriv ?_
    field_simp
  have hc : IntervalIntegrable (fun s : ℝ => t ^ s) volume 0 63 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.rpow continuous_id (fun _ => Or.inl ht.ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc]
  rw [show (63 : ℝ) = ((63 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_zero]
  field_simp

lemma integrableOn_rpow_rect :
    IntegrableOn (fun p : ℝ × ℝ => p.1 ^ p.2) (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 63) := by
  rw [uIoc_of_le zero_le_one, uIoc_of_le (by norm_num)]
  refine Measure.integrableOn_of_bounded (M := 1) ?_ ?_ ?_
  · refine ne_of_lt (lt_of_le_of_lt (measure_mono
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)) ?_)
    exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  · exact (measurable_fst.pow measurable_snd).aestronglyMeasurable
  · rw [ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    obtain ⟨⟨h0, h1⟩, ⟨s0, _⟩⟩ := hp
    rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg h0.le _)]
    exact rpow_le_one h0.le h1 s0.le

lemma inner_rpow {s : ℝ} (hs : 0 ≤ s) : ∫ t in (0 : ℝ)..1, t ^ s = (s + 1)⁻¹ := by
  rw [integral_rpow (Or.inl (by linarith))]
  have h : (s + 1) ≠ 0 := by linarith
  rw [one_rpow, zero_rpow h, sub_zero, one_div]

/-- **Fubini**: `∫₀¹ ∫₀^63 t^s ds dt = log 64`. -/
lemma integral_F : ∫ t in (0 : ℝ)..1, (∫ s in (0 : ℝ)..63, t ^ s) = log 64 := by
  rw [intervalIntegral_intervalIntegral_swap integrableOn_rpow_rect]
  have hc : EqOn (fun s : ℝ => ∫ t in (0 : ℝ)..1, t ^ s) (fun s => (s + 1)⁻¹) (uIcc 0 63) := by
    intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    exact inner_rpow hs.1
  rw [intervalIntegral.integral_congr hc,
    intervalIntegral.integral_comp_add_right (fun x : ℝ => x⁻¹),
    integral_inv_of_pos (by norm_num) (by norm_num)]
  norm_num

lemma integral_mfun : ∫ t in (0 : ℝ)..1, mfun t = -log 64 := by
  have h1 : ∫ t in (0 : ℝ)..1, mfun t = ∫ t in (0 : ℝ)..1, -(∫ s in (0 : ℝ)..63, t ^ s) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    simp only [mfun]
    rw [F_eq ht.1 ht.2]
    ring
  rw [h1, intervalIntegral.integral_neg, integral_F]

lemma mfun_abs_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : |mfun t| ≤ 63 := by
  rcases eq_or_lt_of_le ht with h0 | h0
  · subst h0; norm_num [mfun]
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · subst h1; norm_num [mfun]
  have e : mfun t = -(∫ s in (0 : ℝ)..63, t ^ s) := by
    rw [F_eq h0 h1]; unfold mfun; ring
  rw [e, abs_neg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 63)
    (C := 1) (f := fun s : ℝ => t ^ s) (fun s hs => by
      rw [uIoc_of_le (by norm_num)] at hs
      rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg ht _)]
      exact rpow_le_one ht ht1 hs.1.le)
  norm_num at hb
  exact hb

lemma mfun_ii : IntervalIntegrable mfun volume 0 1 := by
  have hm : Measurable mfun := by
    unfold mfun
    exact (measurable_const.sub (measurable_id.pow_const 63)).div Real.measurable_log
  have h : IntegrableOn mfun (Icc 0 1) := by
    refine Measure.integrableOn_of_bounded (M := 63) measure_Icc_lt_top.ne
      hm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Real.norm_eq_abs]
    exact mfun_abs_le ht.1 ht.2
  rw [← uIcc_of_le zero_le_one] at h
  exact h.intervalIntegrable

lemma integral_geom : ∫ t in (0 : ℝ)..1, (∑ k ∈ Finset.range 63, t ^ k)
    = ∑ k ∈ Finset.range 63, (1 : ℝ) / (k + 1) := by
  rw [intervalIntegral.integral_finsetSum (fun k _ => (continuous_pow k).intervalIntegrable 0 1)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_pow]
  simp

lemma integral_tail : ∫ t in (0 : ℝ)..1, t ^ 63 * (1 - t / 2) = 1 / 64 - 1 / 130 := by
  have hc : EqOn (fun t : ℝ => t ^ 63 * (1 - t / 2)) (fun t => t ^ 63 - (1 / 2) * t ^ 64)
      (uIcc 0 1) := by
    intro t _; simp only; ring
  rw [intervalIntegral.integral_congr hc,
    intervalIntegral.integral_sub ((continuous_pow 63).intervalIntegrable 0 1)
      (((continuous_pow 64).intervalIntegrable 0 1).const_mul _),
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num

/-- `H_63 = Σ_{k<63} 1/(k+1) ≤ 4.728266`, true `4.7282659...`. -/
lemma harmonic63_le : ∑ k ∈ Finset.range 63, (1 : ℝ) / (k + 1) ≤ 4.728266 := by
  norm_num [Finset.sum_range_succ]

/-- `∫₀¹ g ≤ H_63 - log 64 + 1/64 - 1/130`. -/
lemma integral_left :
    ∫ t in (0 : ℝ)..1, gli t
      ≤ (∑ k ∈ Finset.range 63, (1 : ℝ) / (k + 1)) - log 64 + (1 / 64 - 1 / 130) := by
  have hP : IntervalIntegrable (fun t : ℝ => ∑ k ∈ Finset.range 63, t ^ k) volume 0 1 :=
    (continuous_finsetSum _ (fun k _ => continuous_pow k)).intervalIntegrable 0 1
  have hT : IntervalIntegrable (fun t : ℝ => t ^ 63 * (1 - t / 2)) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => t ^ 63 * (1 - t / 2))).intervalIntegrable 0 1
  have hR : IntervalIntegrable
      (fun t : ℝ => (∑ k ∈ Finset.range 63, t ^ k) + mfun t + t ^ 63 * (1 - t / 2))
      volume 0 1 := (hP.add mfun_ii).add hT
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
    (gli_ii le_rfl zero_le_one) hR (fun t ht => gli_le_decomp ht.1 ht.2)
  rw [intervalIntegral.integral_add (hP.add mfun_ii) hT,
    intervalIntegral.integral_add hP mfun_ii, integral_geom, integral_mfun, integral_tail]
    at hmono
  linarith

/-! ### The bound -/

/-- **`li 2 ≤ 1.046`** for the principal value logarithmic integral; in fact `≤ 1.04582`. -/
theorem liPV_two_le_1046 : liPV 2 ≤ 1.046 := by
  rw [liPV_two, ← intervalIntegral.integral_add_adjacent_intervals
    (gli_ii (a := 0) (b := 1) le_rfl zero_le_one) (gli_ii (a := 1) (b := 2) zero_le_one
    (by norm_num))]
  have hL := integral_left
  have hR := integral_right
  have h64 : log 64 = 6 * log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have h3 := log_three_halves_le
  have hH := harmonic63_le
  rw [h64] at hL
  linarith

/-- `li 2 ≥ 0` and `li 2 ≤ 1.046`, the sharp form of `liPV_two_le`. -/
theorem liPV_two_bounds : 0 ≤ liPV 2 ∧ liPV 2 ≤ 1.046 :=
  ⟨liPV_two_le.1, liPV_two_le_1046⟩

/-- **The shared input with the paper's constant, PROVED**:
`li y ≤ ∫₂^y dt / log t + 1.046` for every `y ≥ 2`, `li` the principal value logarithmic
integral. Bordignon-Starichkova 2022 use this with `1.046`; INPUTS.md item below the cut. -/
theorem liPV_le_1046 {y : ℝ} (hy : 2 ≤ y) :
    liPV y ≤ (∫ t in (2 : ℝ)..y, 1 / log t) + 1.046 := by
  rw [liPV_eq_add hy]; linarith [liPV_two_le_1046]

/-- Vacuity check: the hypothesis `2 ≤ y` holds at `y = 2`, where the bound reads
`li 2 ≤ 1.046`. -/
example : liPV 2 ≤ (∫ t in (2 : ℝ)..2, 1 / log t) + 1.046 := liPV_le_1046 le_rfl

#print axioms log_three_halves_le
#print axioms integral_right
#print axioms integral_F
#print axioms integral_mfun
#print axioms integral_left
#print axioms liPV_two_le_1046
#print axioms liPV_two_bounds
#print axioms liPV_le_1046

end LeanLab.BS2022GRH.LiTwo
