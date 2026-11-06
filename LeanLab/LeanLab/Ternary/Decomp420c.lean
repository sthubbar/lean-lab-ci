/-
MMS https://arxiv.org/abs/1610.02017v2, pages 11 and 12.
The supplementary BuchstabIntegrals.nb is in the v1 source archive.
Separate the prime number asymptotic from its explicit numerical envelope.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp379c
import LeanLab.Helfgott2013.SectionSeven

namespace LeanLab.Ternary.MMS.Task420
open MeasureTheory

/-- The notebook upper envelope B for Buchstab's function on u at least one.
MMS page 12 footnote 3 and BuchstabIntegrals.nb in the v1 source archive.
Below one we choose the same reciprocal branch as a harmless total extension.
Every argument used in the integral below is at least one. -/
noncomputable def buchstabEnvelope (u : ℝ) : ℝ :=
  if u ≤ 2 then 1 / u else
    if u ≤ 3 then (1 + Real.log (u - 1)) / u else (1 + Real.log 2) / 3

/-- The explicit triple integral evaluated by the accompanying notebook.
MMS page 11 bottom display, with omega replaced by its upper envelope.
The source order is a from one tenth to one quarter, b from a to one quarter,
and c from b to one quarter. This is real valued data. -/
noncomputable def buchstabEnvelopeIntegral : ℝ :=
  ∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ),
    ∫ b in a..(1 / 4 : ℝ),
      ∫ c in b..(1 / 4 : ℝ),
        buchstabEnvelope ((1 - a - b - c) / a) / (a ^ 2 * b * c)

/-- Every Buchstab argument in the paper integration region is at least one.
MMS page 11 bottom display and the first branch of BuchstabIntegrals.nb. -/
theorem buchstab_argument_ge_one {a b c : ℝ} (ha : 0 < a)
    (ha4 : a ≤ 1 / 4) (hb4 : b ≤ 1 / 4) (hc4 : c ≤ 1 / 4) :
    1 ≤ (1 - a - b - c) / a := by
  apply (le_div_iff₀ ha).mpr
  linarith

/-- The constant four B four is below 2.258.
MMS page 12 and the second computation in BuchstabIntegrals.nb.
The proof uses the certified Mathlib bound for log two. -/
theorem buchstab_constant_lt : 4 * buchstabEnvelope 4 < (2.258 : ℝ) := by
  norm_num [buchstabEnvelope]
  linarith [Real.log_two_lt_d9]

/-- The explicit notebook envelope is nonnegative on its stated domain.
MMS page 12 footnote 3, the three branches of BuchstabIntegrals.nb. -/
theorem buchstabEnvelope_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ buchstabEnvelope u := by
  unfold buchstabEnvelope
  split_ifs with htwo hthree
  · positivity
  · have hl : 0 ≤ Real.log (u - 1) := Real.log_nonneg (by linarith)
    positivity
  · have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity

/-- The notebook envelope is at most 0.57 from argument two onward.
Derived elementary enclosure of its logarithmic middle branch and constant tail.
MMS page 12 footnote 3, BuchstabIntegrals.nb. -/
theorem buchstabEnvelope_le_057 {u : ℝ} (hu : 2 ≤ u) :
    buchstabEnvelope u ≤ (0.57 : ℝ) := by
  have hlog : Real.log (7 / 4 : ℝ) < 0.56 := by
    rw [show (7 / 4 : ℝ) = 7 / 2 ^ (2 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    have hs := LeanLab.Helfgott2013.log_seven_lt_ratio
    have ht := Real.log_two_lt_d9
    norm_num
    linarith
  unfold buchstabEnvelope
  split_ifs with htwo hthree
  · have he : u = 2 := le_antisymm htwo hu
    subst u
    norm_num
  · have hz : 0 < u - 1 := by linarith
    have ht := Real.log_le_sub_one_of_pos (div_pos hz (by norm_num : (0 : ℝ) < 7 / 4))
    rw [Real.log_div hz.ne' (by norm_num)] at ht
    apply (div_le_iff₀ (by linarith : 0 < u)).mpr
    nlinarith
  · have ht := Real.log_two_lt_d9
    linarith

/-- The notebook envelope never exceeds one on arguments at least one.
Derived enclosure for the numerical integral in MMS page 12 footnote 3. -/
theorem buchstabEnvelope_le_one {u : ℝ} (hu : 1 ≤ u) : buchstabEnvelope u ≤ 1 := by
  by_cases htwo : u ≤ 2
  · simp only [buchstabEnvelope, ite_eq_left htwo]
    exact (div_le_one (by linarith : 0 < u)).mpr hu
  · exact (buchstabEnvelope_le_057 (by linarith)).trans (by norm_num)

/-- The explicit triple integral is nonnegative.
MMS page 11 bottom display, with the notebook nonnegative upper envelope. -/
theorem buchstabEnvelopeIntegral_nonneg : 0 ≤ buchstabEnvelopeIntegral := by
  unfold buchstabEnvelopeIntegral
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro a ha
  have ha0 : 0 < a := by linarith [ha.1]
  apply intervalIntegral.integral_nonneg ha.2
  intro b hb
  have hb0 : 0 < b := ha0.trans_le hb.1
  apply intervalIntegral.integral_nonneg hb.2
  intro c hc
  have hc0 : 0 < c := hb0.trans_le hc.1
  exact div_nonneg (buchstabEnvelope_nonneg
    (buchstab_argument_ge_one ha0 ha.2 hb.2 hc.2)) (by positivity)

/-- The logarithmic inner antiderivative for the notebook triangle.
Derived numerical integration step for MMS page 12 footnote 3. -/
theorem log_ratio_kernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (b / t) / t) = Real.log (b / a) ^ 2 / 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hpos (t : ℝ) (ht : t ∈ Set.Icc a b) : 0 < t := ha.trans_le ht.1
  have hcont : ContinuousOn (fun t : ℝ => (Real.log b - Real.log t) / t) (Set.Icc a b) :=
    (continuousOn_const.sub (Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne'))).div
      continuousOn_id (fun t ht => (hpos t ht).ne')
  have hd (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun t : ℝ => -(Real.log b - Real.log t) ^ 2 / 2)
        ((Real.log b - Real.log t) / t) t := by
    rw [Set.uIcc_of_le hab] at ht
    have h := ((((hasDerivAt_const t (Real.log b)).sub
      (Real.hasDerivAt_log (hpos t ht).ne')).pow 2).neg).div_const 2
    dsimp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply, Pi.div_apply, id_eq] at h
    convert h using 1 <;> field_simp [(hpos t ht).ne'] <;> ring
  have he : (∫ t in a..b, Real.log (b / t) / t) =
      ∫ t in a..b, (Real.log b - Real.log t) / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    dsimp only
    rw [Real.log_div hb.ne' (hpos t ht).ne']
  rw [he, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hcont.intervalIntegrable_of_Icc hab), Real.log_div hb.ne' ha.ne']
  ring

/-- The logarithmic outer antiderivative for the notebook triangle.
Derived numerical integration step for MMS page 12 footnote 3. -/
theorem log_ratio_sq_kernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (b / t) ^ 2 / (2 * t ^ 2)) =
      (Real.log (b / a) ^ 2 - 2 * Real.log (b / a) + 2) / (2 * a) - 1 / b := by
  have hb : 0 < b := ha.trans_le hab
  have hpos (t : ℝ) (ht : t ∈ Set.Icc a b) : 0 < t := ha.trans_le ht.1
  have hcont : ContinuousOn (fun t : ℝ => (Real.log b - Real.log t) ^ 2 / (2 * t ^ 2))
      (Set.Icc a b) :=
    ((continuousOn_const.sub (Real.continuousOn_log.mono
      (fun t ht => (hpos t ht).ne'))).pow 2).div
      (continuousOn_const.mul (continuousOn_id.pow 2))
      (fun t ht => by have := (hpos t ht).ne'; positivity)
  have hd (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt
        (fun t : ℝ => -((Real.log b - Real.log t) ^ 2 - 2 * (Real.log b - Real.log t) + 2) /
          (2 * t)) ((Real.log b - Real.log t) ^ 2 / (2 * t ^ 2)) t := by
    rw [Set.uIcc_of_le hab] at ht
    have hl := (hasDerivAt_const t (Real.log b)).sub (Real.hasDerivAt_log (hpos t ht).ne')
    have hp := (((hl.pow 2).sub (hl.const_mul 2)).add_const 2).neg
    have h := hp.div ((hasDerivAt_id t).const_mul 2) (mul_ne_zero (by norm_num) (hpos t ht).ne')
    dsimp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply, Pi.div_apply, id_eq] at h
    convert h using 1 <;> field_simp [(hpos t ht).ne'] <;> ring
  have he : (∫ t in a..b, Real.log (b / t) ^ 2 / (2 * t ^ 2)) =
      ∫ t in a..b, (Real.log b - Real.log t) ^ 2 / (2 * t ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    dsimp only
    rw [Real.log_div hb.ne' (hpos t ht).ne']
  rw [he, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hcont.intervalIntegrable_of_Icc hab), Real.log_div hb.ne' ha.ne']
  field_simp
  ring

/-- A nonnegative interval integral is bounded by an integrable pointwise majorant.
Mathlib setIntegral_mono_of_nonneg supplies this wrapper for the notebook enclosure. -/
theorem interval_integral_mono_nonneg {a b : ℝ} (hab : a ≤ b) (f g : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hfg : ∀ t ∈ Set.Icc a b, f t ≤ g t)
    (hg : IntervalIntegrable g volume a b) :
    (∫ t in a..b, f t) ≤ ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact setIntegral_mono_of_nonneg
    (fun t ht => hf t ⟨ht.1.le, ht.2⟩)
    (fun t ht => hfg t ⟨ht.1.le, ht.2⟩) hg.1

/-- Integrating the c coordinate replaces a uniform envelope bound by a logarithm.
Derived enclosure of the explicit notebook integral in MMS page 12 footnote 3. -/
theorem envelope_inner_bound {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 4) (hK : 0 ≤ K)
    (hB : ∀ c ∈ Set.Icc b (1 / 4 : ℝ),
      buchstabEnvelope ((1 - a - b - c) / a) ≤ K) :
    (∫ c in b..(1 / 4 : ℝ),
      buchstabEnvelope ((1 - a - b - c) / a) / (a ^ 2 * b * c)) ≤
      K / (a ^ 2 * b) * Real.log ((1 / 4 : ℝ) / b) := by
  have hb0 : 0 < b := ha.trans_le hab
  have hpos (t : ℝ) (ht : t ∈ Set.Icc b (1 / 4 : ℝ)) : 0 < t := hb0.trans_le ht.1
  have hg : IntervalIntegrable (fun c : ℝ => K / (a ^ 2 * b) * (1 / c)) volume b (1 / 4) :=
    (continuousOn_const.mul (continuousOn_const.div continuousOn_id
      (fun t ht => (hpos t ht).ne'))).intervalIntegrable_of_Icc hb
  have h := interval_integral_mono_nonneg hb
    (fun c => buchstabEnvelope ((1 - a - b - c) / a) / (a ^ 2 * b * c))
    (fun c => K / (a ^ 2 * b) * (1 / c)) ?_ ?_ hg
  · simpa only [intervalIntegral.integral_const_mul, integral_one_div_of_pos hb0
      (by norm_num : (0 : ℝ) < 1 / 4)] using h
  · intro c hc
    have hc0 := hpos c hc
    exact div_nonneg (buchstabEnvelope_nonneg
      (buchstab_argument_ge_one ha (hab.trans hb) hb hc.2)) (by positivity)
  · intro c hc
    have hc0 := hpos c hc
    have hh := div_le_div_of_nonneg_right (hB c hc)
      (show 0 ≤ a ^ 2 * b * c by positivity)
    convert hh using 1 <;> ring

/-- Integrating the b and c coordinates gives the squared logarithmic kernel.
Derived enclosure of the explicit notebook integral in MMS page 12 footnote 3. -/
theorem envelope_double_bound {a K : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (hK : 0 ≤ K)
    (hB : ∀ b ∈ Set.Icc a (1 / 4 : ℝ), ∀ c ∈ Set.Icc b (1 / 4 : ℝ),
      buchstabEnvelope ((1 - a - b - c) / a) ≤ K) :
    (∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ),
      buchstabEnvelope ((1 - a - b - c) / a) / (a ^ 2 * b * c)) ≤
      K * Real.log ((1 / 4 : ℝ) / a) ^ 2 / (2 * a ^ 2) := by
  have hpos (t : ℝ) (ht : t ∈ Set.Icc a (1 / 4 : ℝ)) : 0 < t := ha.trans_le ht.1
  have hcont : ContinuousOn (fun b : ℝ => (K / a ^ 2) *
      ((Real.log (1 / 4 : ℝ) - Real.log b) / b)) (Set.Icc a (1 / 4 : ℝ)) :=
    continuousOn_const.mul
      ((continuousOn_const.sub (Real.continuousOn_log.mono
        (fun t ht => (hpos t ht).ne'))).div continuousOn_id
        (fun t ht => (hpos t ht).ne'))
  have hg : IntervalIntegrable (fun b : ℝ => (K / a ^ 2) *
      (Real.log ((1 / 4 : ℝ) / b) / b)) volume a (1 / 4) := by
    apply (hcont.intervalIntegrable_of_Icc ha4).congr
    intro b hb
    rw [Set.uIoc_of_le ha4] at hb
    dsimp only
    rw [Real.log_div (by norm_num) (hpos b ⟨hb.1.le, hb.2⟩).ne']
  have h := interval_integral_mono_nonneg ha4
    (fun b => ∫ c in b..(1 / 4 : ℝ),
      buchstabEnvelope ((1 - a - b - c) / a) / (a ^ 2 * b * c))
    (fun b => (K / a ^ 2) * (Real.log ((1 / 4 : ℝ) / b) / b)) ?_ ?_ hg
  · rw [intervalIntegral.integral_const_mul, log_ratio_kernel ha ha4] at h
    convert h using 1 <;> ring
  · intro b hb
    apply intervalIntegral.integral_nonneg hb.2
    intro c hc
    exact div_nonneg (buchstabEnvelope_nonneg
      (buchstab_argument_ge_one ha ha4 hb.2 hc.2))
      (by have hb0 := hpos b hb; have hc0 := hb0.trans_le hc.1; positivity)
  · intro b hb
    have hh := envelope_inner_bound ha hb.1 hb.2 hK (hB b hb)
    convert hh using 1 <;> ring


/-- The full logarithmic kernel mass is at most 1.05.
Derived enclosure for MMS page 12 footnote 3, using certified log two and log five bounds. -/
theorem kernel_total_bound :
    (∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ),
      Real.log ((1 / 4 : ℝ) / a) ^ 2 / (2 * a ^ 2)) ≤ (1.05 : ℝ) := by
  rw [log_ratio_sq_kernel (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num)]
  norm_num
  have hl : (0.916 : ℝ) ≤ Real.log (5 / 2 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_five_gt_d9, Real.log_two_lt_d9]
  have hu : Real.log (5 / 2 : ℝ) ≤ (0.917 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_five_lt_d9, Real.log_two_gt_d9]
  have hsq : Real.log (5 / 2 : ℝ) ^ 2 ≤ (0.917 : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- The kernel mass above a equal to one sixth is at most 0.07.
Derived enclosure for MMS page 12 footnote 3, using certified log two and log three bounds. -/
theorem kernel_tail_bound :
    (∫ a in (1 / 6 : ℝ)..(1 / 4 : ℝ),
      Real.log ((1 / 4 : ℝ) / a) ^ 2 / (2 * a ^ 2)) ≤ (0.07 : ℝ) := by
  rw [log_ratio_sq_kernel (by norm_num : (0 : ℝ) < 1 / 6) (by norm_num)]
  norm_num
  have hl : (0.405 : ℝ) ≤ Real.log (3 / 2 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_gt_d9, Real.log_two_lt_d9]
  have hu : Real.log (3 / 2 : ℝ) ≤ (0.406 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have hsq : Real.log (3 / 2 : ℝ) ^ 2 ≤ (0.406 : ℝ) ^ 2 := by nlinarith
  nlinarith


/-- LEAF. The explicit notebook triple integral is at most 0.64.
MMS page 12 footnote 3, BuchstabIntegrals.nb in the v1 source archive.
The notebook output is 0.5837866229322005. This leaf asks only for the
weaker rigorous upper enclosure 0.64 and contains no prime number asymptotic. -/
theorem buchstab_envelope_integral_upper : buchstabEnvelopeIntegral ≤ (0.64 : ℝ) := by
  let H := fun a : ℝ => ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ),
    buchstabEnvelope ((1 - a - b - c) / a) / (a ^ 2 * b * c)
  let F := fun a : ℝ => Real.log ((1 / 4 : ℝ) / a) ^ 2 / (2 * a ^ 2)
  have hpos (t : ℝ) (ht : t ∈ Set.Icc (1 / 10 : ℝ) (1 / 4 : ℝ)) : 0 < t := by
    linarith [ht.1]
  have hHnonneg (a : ℝ) (ha : a ∈ Set.Icc (1 / 10 : ℝ) (1 / 4 : ℝ)) : 0 ≤ H a := by
    dsimp [H]
    apply intervalIntegral.integral_nonneg ha.2
    intro b hb
    have hb0 := (hpos a ha).trans_le hb.1
    apply intervalIntegral.integral_nonneg hb.2
    intro c hc
    have hc0 := hb0.trans_le hc.1
    exact div_nonneg (buchstabEnvelope_nonneg
      (buchstab_argument_ge_one (hpos a ha) ha.2 hb.2 hc.2)) (by positivity)
  have hF : IntervalIntegrable F volume (1 / 10) (1 / 4) := by
    have hc : ContinuousOn (fun a : ℝ =>
        (Real.log (1 / 4 : ℝ) - Real.log a) ^ 2 / (2 * a ^ 2))
        (Set.Icc (1 / 10 : ℝ) (1 / 4 : ℝ)) :=
      ((continuousOn_const.sub (Real.continuousOn_log.mono
        (fun t ht => (hpos t ht).ne'))).pow 2).div
        (continuousOn_const.mul (continuousOn_id.pow 2))
        (fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero _ (hpos t ht).ne'))
    apply (hc.intervalIntegrable_of_Icc (by norm_num)).congr
    intro a ha
    rw [Set.uIoc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 4)] at ha
    dsimp [F]
    rw [Real.log_div (by norm_num) (hpos a ⟨ha.1.le, ha.2⟩).ne']
  obtain ⟨hF₁, hF₂⟩ := (IntervalIntegrable.trans_iff
    (by norm_num : (1 / 6 : ℝ) ∈ Set.uIcc (1 / 10 : ℝ) (1 / 4 : ℝ))).mp hF
  have hl : (∫ a in (1 / 10 : ℝ)..(1 / 6 : ℝ), H a) ≤
      0.57 * (∫ a in (1 / 10 : ℝ)..(1 / 6 : ℝ), F a) := by
    rw [← intervalIntegral.integral_const_mul]
    apply interval_integral_mono_nonneg (by norm_num) H (fun a => 0.57 * F a) ?_ ?_
      (hF₁.const_mul _)
    · intro a ha
      exact hHnonneg a ⟨ha.1, ha.2.trans (by norm_num)⟩
    · intro a ha
      have ha0 : 0 < a := by linarith [ha.1]
      have ha4 : a ≤ (1 / 4 : ℝ) := ha.2.trans (by norm_num)
      have h := envelope_double_bound ha0 ha4 (by norm_num : (0 : ℝ) ≤ 0.57) ?_
      · dsimp [H, F]
        convert h using 1 <;> ring
      · intro b hb c hc
        apply buchstabEnvelope_le_057
        apply (le_div_iff₀ ha0).mpr
        linarith [ha.2, hb.2, hc.2]
  have hh : (∫ a in (1 / 6 : ℝ)..(1 / 4 : ℝ), H a) ≤
      ∫ a in (1 / 6 : ℝ)..(1 / 4 : ℝ), F a := by
    apply interval_integral_mono_nonneg (by norm_num) H F ?_ ?_ hF₂
    · intro a ha
      exact hHnonneg a ⟨(by norm_num : (1 / 10 : ℝ) ≤ 1 / 6).trans ha.1, ha.2⟩
    · intro a ha
      have ha0 : 0 < a := by linarith [ha.1]
      have h := envelope_double_bound ha0 ha.2 (by norm_num : (0 : ℝ) ≤ 1) ?_
      · simpa [H, F] using h
      · intro b hb c hc
        exact buchstabEnvelope_le_one (buchstab_argument_ge_one ha0 ha.2 hb.2 hc.2)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hF₁ hF₂
  have ht := kernel_total_bound
  have htail := kernel_tail_bound
  change (∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ), H a) ≤ 0.64
  by_cases hi : IntervalIntegrable H volume (1 / 10) (1 / 4)
  · obtain ⟨hi₁, hi₂⟩ := (IntervalIntegrable.trans_iff
      (by norm_num : (1 / 6 : ℝ) ∈ Set.uIcc (1 / 10 : ℝ) (1 / 4 : ℝ))).mp hi
    have hs := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
    change (∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ), F a) ≤ 1.05 at ht
    change (∫ a in (1 / 6 : ℝ)..(1 / 4 : ℝ), F a) ≤ 0.07 at htail
    linarith
  · rw [intervalIntegral.integral_undef hi]
    norm_num

/-- LEAF. The reference mean converges to a positive coefficient below the explicit envelope.
MMS page 11 bottom Buchstab display, page 12 first paragraph and footnote 3.
The prime number theorem supplies the limiting coefficient. The initial Buchstab
formulas and the bound omega u at most omega three for u at least three
supply comparison with B. No numerical integration bound is used in this leaf. -/
theorem harman_reference_mean_enveloped :
    ∃ αp : ℝ, 0 < αp ∧ αp ≤ 4 * buchstabEnvelope 4 + buchstabEnvelopeIntegral ∧
      ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        |Task379.referenceMean x - αp| ≤ δ := by
  sorry

/-- The explicit envelope is strictly below the required density ceiling.
MMS page 12 first paragraph, using the proved integral enclosure. -/
theorem buchstab_envelope_lt :
    4 * buchstabEnvelope 4 + buchstabEnvelopeIntegral < (2.9 : ℝ) := by
  have hc := buchstab_constant_lt
  have hi := buchstab_envelope_integral_upper
  linarith

/-- The exact existing reference mean statement from its analytic and numerical parts.
MMS pages 11 and 12. CONDITIONAL ON harman_reference_mean_enveloped alone. -/
theorem harman_reference_mean_decomposed :
    ∃ αp : ℝ, 0 < αp ∧ αp < 2.9 ∧
      ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        |Task379.referenceMean x - αp| ≤ δ := by
  obtain ⟨αp, hp, hb, hmean⟩ := harman_reference_mean_enveloped
  exact ⟨αp, hp, hb.trans_lt buchstab_envelope_lt, hmean⟩

end LeanLab.Ternary.MMS.Task420
