/- AI wrote this Lean code for CODEX task543. Goldbach is open.
Abel summation for journal Lemma 14, pp. 1238 and 1239.
https://doi.org/10.1007/s11139-024-00866-x -/
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.NumberTheory.Bertrand
import LeanLab.BS2022GRH.SlicePartial236
import LeanLab.BS2022GRH.Lemma11C164

namespace LeanLab.BS2022GRH.Decomp543a
open Real Finset Classical MeasureTheory intervalIntegral
noncomputable section

/-- LEAF. CITED Rosser and Schoenfeld 1962, p. 70, Theorem 5,
displays 3.17 and 3.18. The constant B is common to both inequalities.
The lower bound holds for x greater than one. The upper bound starts at 286.
https://doi.org/10.1215/ijm/1255631807 -/
theorem rosser_schoenfeld_theorem5 : ∃ B : ℝ,
    (∀ x : ℝ, 1 < x → log (log x) + B - 1 / (2 * log x ^ 2) <
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) ∧
    (∀ x : ℝ, 286 ≤ x → (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) <
      log (log x) + B + 1 / (2 * log x ^ 2)) := by
  sorry

/-- The contribution of one atom to Abel summation, journal p. 1238.
The strict cumulative convention uses p less than t. -/
theorem abel_atom (H H' : ℝ → ℝ) (a b p c : ℝ) (hab : a ≤ b) (hp : p < b)
    (hd : ∀ t ∈ Set.uIcc a b, HasDerivAt H (H' t) t)
    (hi : IntervalIntegrable H' volume a b) :
    (∫ t in a..b, if p < t then H' t * c else 0) =
      (H b - H (max a p)) * c := by
  have hprod := hi.mul_const c
  by_cases hpa : p ≤ a
  · have he : (∫ t in a..b, if p < t then H' t * c else 0) =
        ∫ t in a..b, H' t * c := by
      apply integral_congr_ae_restrict
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Set.uIoc_of_le hab] at ht
      simp [lt_of_le_of_lt hpa ht.1]
    rw [he, intervalIntegral.integral_mul_const, integral_eq_sub_of_hasDerivAt hd hi, max_eq_left hpa]
  · have hap : a ≤ p := (lt_of_not_ge hpa).le
    have hpb : p ≤ b := hp.le
    have hleft : (∫ t in a..p, if p < t then H' t * c else 0) = 0 := by
      rw [← integral_zero (a := a) (b := p) (μ := volume)]
      apply integral_congr_ae_restrict
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Set.uIoc_of_le hap] at ht
      simp [not_lt.mpr ht.2]
    have hright : (∫ t in p..b, if p < t then H' t * c else 0) =
        ∫ t in p..b, H' t * c := by
      apply integral_congr_ae_restrict
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Set.uIoc_of_le hpb] at ht
      simp [ht.1]
    have hif : IntervalIntegrable (fun t => if p < t then H' t * c else 0) volume a b := by
      rw [intervalIntegrable_iff]
      apply MeasureTheory.Integrable.congr
        (MeasureTheory.Integrable.indicator (s := Set.Ioi p) hprod.def' measurableSet_Ioi)
      filter_upwards with t
      rfl
    have hpab : p ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact ⟨hap, hpb⟩
    rw [← integral_add_adjacent_intervals (hif.mono_set (Set.uIcc_subset_uIcc_left hpab))
      (hif.mono_set (Set.uIcc_subset_uIcc_right hpab)), hleft, zero_add, hright,
      intervalIntegral.integral_mul_const, integral_eq_sub_of_hasDerivAt _ (hi.mono_set _), max_eq_right hap]
    · intro t ht
      exact hd t (Set.uIcc_subset_uIcc_right hpab ht)
    · exact Set.uIcc_subset_uIcc_right hpab

/-- Integrability of one cumulative atom, journal p. 1238 Abel formula. -/
theorem abel_atom_integrable (H' : ℝ → ℝ) (a b p c : ℝ)
    (hi : IntervalIntegrable H' volume a b) :
    IntervalIntegrable (fun t => if p < t then H' t * c else 0) volume a b := by
  rw [intervalIntegrable_iff]
  apply MeasureTheory.Integrable.congr
    (MeasureTheory.Integrable.indicator (s := Set.Ioi p) (hi.mul_const c).def' measurableSet_Ioi)
  filter_upwards with t
  rfl

/-- Exact Abel summation with a strict cumulative sum and both endpoints.
This is the finite identity underlying Greaves Lemma 1 part ii, p. 1238. -/
theorem finite_abel_strict (s : Finset ℕ) (c : ℕ → ℝ) (H H' : ℝ → ℝ)
    (a b : ℝ) (hab : a ≤ b) (hs : ∀ p ∈ s, (p : ℝ) < b)
    (hd : ∀ t ∈ Set.uIcc a b, HasDerivAt H (H' t) t)
    (hi : IntervalIntegrable H' volume a b) :
    (∑ p ∈ s.filter (fun p : ℕ => a ≤ (p : ℝ)), H p * c p) =
      H b * (∑ p ∈ s, c p) -
      H a * (∑ p ∈ s, if (p : ℝ) < a then c p else 0) -
      ∫ t in a..b, H' t * ∑ p ∈ s, if (p : ℝ) < t then c p else 0 := by
  have hsum : (∫ t in a..b, H' t * ∑ p ∈ s, if (p : ℝ) < t then c p else 0) =
      ∑ p ∈ s, (H b - H (max a p)) * c p := by
    simp_rw [mul_sum, mul_ite, mul_zero]
    rw [intervalIntegral.integral_finsetSum (s := s) (fun (p : ℕ) hp => abel_atom_integrable H' a b p (c p) hi)]
    exact sum_congr rfl (fun p hp => abel_atom H H' a b p (c p) hab (hs p hp) hd hi)
  rw [hsum, sum_filter, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  by_cases hpa : a ≤ (p : ℝ)
  · simp only [hpa, ite_true, not_lt.mpr hpa, ite_false, mul_zero, sub_zero,
      max_eq_right hpa]
    ring
  · have hlt : (p : ℝ) < a := lt_of_not_ge hpa
    simp only [hpa, ite_false, hlt, ite_true, max_eq_left hlt.le]
    ring

/-- Greaves Lemma 1 part ii in Abel form, used on journal pp. 1238 and 1239.
A uniform cumulative error E costs the endpoint terms and the variation of H.
The exact Abel identity is an explicit premise, with no endpoint suppressed. -/
theorem greaves_variation (H H' A A' S : ℝ → ℝ) (a b E W : ℝ)
    (hab : a ≤ b)
    (hdH : ∀ t ∈ Set.uIcc a b, HasDerivAt H (H' t) t)
    (hdA : ∀ t ∈ Set.uIcc a b, HasDerivAt A (A' t) t)
    (hiH : IntervalIntegrable H' volume a b)
    (hiA : IntervalIntegrable A' volume a b)
    (hiS : IntervalIntegrable (fun t => H' t * S t) volume a b)
    (herr : ∀ t ∈ Set.Icc a b, |S t - A t| ≤ E)
    (habel : W = H b * S b - H a * S a - ∫ t in a..b, H' t * S t) :
    |W - ∫ t in a..b, H t * A' t| ≤
      E * (|H b| + |H a| + ∫ t in a..b, |H' t|) := by
  have hAc : ContinuousOn A (Set.uIcc a b) :=
    continuousOn_of_forall_continuousAt (fun t ht => (hdA t ht).continuousAt)
  have hiHA := hiH.mul_continuousOn hAc
  have hip := integral_mul_deriv_eq_deriv_mul hdH hdA hiH hiA
  have heq : W - (∫ t in a..b, H t * A' t) =
      H b * (S b - A b) - H a * (S a - A a) -
      ∫ t in a..b, H' t * (S t - A t) := by
    simp_rw [mul_sub]
    rw [integral_sub hiS hiHA, habel, hip]
    ring
  have hint : |∫ t in a..b, H' t * (S t - A t)| ≤
      E * ∫ t in a..b, |H' t| := by
    have h := norm_integral_le_of_norm_le (μ := volume)
      (f := fun t : ℝ => H' t * (S t - A t)) hab
      (Filter.Eventually.of_forall (fun t ht => ?_)) (hiH.abs.const_mul E)
    · simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using h
    · rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (herr t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)).trans_eq
        (mul_comm _ _)
  rw [heq]
  calc
    _ ≤ |H b * (S b - A b)| + |H a * (S a - A a)| +
        |∫ t in a..b, H' t * (S t - A t)| :=
      by
        simpa only [Real.norm_eq_abs] using
          (norm_sub_le (H b * (S b - A b) - H a * (S a - A a))
            (∫ t in a..b, H' t * (S t - A t))).trans
            (add_le_add (norm_sub_le (H b * (S b - A b)) (H a * (S a - A a))) le_rfl)
    _ ≤ |H b| * E + |H a| * E + E * ∫ t in a..b, |H' t| := by
      simp only [abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (herr b ⟨hab, le_rfl⟩) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (herr a ⟨le_rfl, hab⟩) (abs_nonneg _))) hint
    _ = _ := by ring

/-- The source Mertens bounds pass to the strict prime endpoint by a left limit.
CONDITIONAL ON the two inequalities of Rosser and Schoenfeld Theorem 5. -/
theorem mertens_strict_error (B x : ℝ) (hx : 286 ≤ x)
    (hlo : ∀ y : ℝ, 1 < y → log (log y) + B - 1 / (2 * log y ^ 2) <
      ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p)
    (hup : ∀ y : ℝ, 286 ≤ y → (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) <
      log (log y) + B + 1 / (2 * log y ^ 2)) :
    |(∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p) - log (log x) - B| ≤
      1 / (2 * log x ^ 2) := by
  have hx1 : 1 < x := by linarith
  have hcont : ContinuousAt (fun y : ℝ => log (log y) + B - 1 / (2 * log y ^ 2)) x := by
    have hx0 : x ≠ 0 := by linarith
    have hl : log x ≠ 0 := (log_pos hx1).ne'
    have hden : 2 * log x ^ 2 ≠ 0 := by positivity
    fun_prop
  have hlow : log (log x) + B - 1 / (2 * log x ^ 2) ≤
      ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
    apply le_of_tendsto (hcont.tendsto.mono_left
      (show nhdsWithin x (Set.Iio x) ≤ nhds x from nhdsWithin_le_nhds))
    have he : ∀ᶠ y in nhdsWithin x (Set.Iio x), 1 < y :=
      (lt_mem_nhds hx1).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, he] with y hy hy1
    apply (hlo y hy1).le.trans
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpy, hprime⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesBelow.mpr ⟨Nat.lt_ceil.mpr
        (((Nat.cast_le.mpr hpy).trans (Nat.floor_le (by linarith))).trans_lt hy), hprime⟩
    · intro p hp hnot
      positivity
  have hsum : (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p) ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpx, hprime⟩ := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (Nat.lt_ceil.mp hpx).le, hprime⟩
    · intro p hp hnot
      positivity
  exact abs_le.mpr ⟨by linarith, by linarith [hup x hx]⟩

/-- Restrict a finite strict prime cumulative sum, journal p. 1238. -/
theorem prime_cumulative_restrict (t b : ℝ) (ht : t ≤ b) :
    (∑ p ∈ Nat.primesBelow ⌈b⌉₊, if (p : ℝ) < t then (1 : ℝ) / p else 0) =
      ∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p := by
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hpb, hp⟩, hpt⟩
    exact ⟨Nat.lt_ceil.mpr hpt, hp⟩
  · rintro ⟨hpt, hp⟩
    exact ⟨⟨Nat.lt_ceil.mpr ((Nat.lt_ceil.mp hpt).trans_le ht), hp⟩, Nat.lt_ceil.mp hpt⟩

/-- Exact strict-endpoint prime Abel identity, journal pp. 1238 and 1239. -/
theorem prime_abel_strict (H H' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ t ∈ Set.uIcc a b, HasDerivAt H (H' t) t)
    (hi : IntervalIntegrable H' volume a b) :
    (∑ p ∈ (Nat.primesBelow ⌈b⌉₊).filter (fun p : ℕ => a ≤ (p : ℝ)), H p / p) =
      H b * (∑ p ∈ Nat.primesBelow ⌈b⌉₊, (1 : ℝ) / p) -
      H a * (∑ p ∈ Nat.primesBelow ⌈a⌉₊, (1 : ℝ) / p) -
      ∫ t in a..b, H' t * (∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) := by
  have hs (p : ℕ) (hp : p ∈ Nat.primesBelow ⌈b⌉₊) : (p : ℝ) < b :=
    Nat.lt_ceil.mp (Nat.mem_primesBelow.mp hp).1
  have he := finite_abel_strict (Nat.primesBelow ⌈b⌉₊) (fun p => (1 : ℝ) / p)
    H H' a b hab hs hd hi
  simp only [prime_cumulative_restrict a b hab, mul_one_div] at he
  rw [he]
  congr 1
  apply integral_congr_ae_restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Set.uIoc_of_le hab] at ht
  rw [prime_cumulative_restrict t b ht.2]

/-- Weighted prime summation with the explicit Mertens error and variation.
CONDITIONAL ON the source inequalities of Rosser and Schoenfeld Theorem 5. -/
theorem greaves_prime_variation (H H' : ℝ → ℝ) (a b B : ℝ)
    (ha : 286 ≤ a) (hab : a ≤ b)
    (hd : ∀ t ∈ Set.uIcc a b, HasDerivAt H (H' t) t)
    (hi : IntervalIntegrable H' volume a b)
    (hlo : ∀ y : ℝ, 1 < y → log (log y) + B - 1 / (2 * log y ^ 2) <
      ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p)
    (hup : ∀ y : ℝ, 286 ≤ y → (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) <
      log (log y) + B + 1 / (2 * log y ^ 2)) :
    |(∑ p ∈ (Nat.primesBelow ⌈b⌉₊).filter (fun p : ℕ => a ≤ (p : ℝ)), H p / p) -
      ∫ t in a..b, H t / (t * log t)| ≤
      (|H b| + |H a| + ∫ t in a..b, |H' t|) / (2 * log a ^ 2) := by
  have ha1 : 1 < a := by linarith
  have ht1 (t : ℝ) (ht : t ∈ Set.uIcc a b) : 1 < t := by
    rw [Set.uIcc_of_le hab] at ht
    exact ha1.trans_le ht.1
  have hdA : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t => log (log t) + B) (1 / (t * log t)) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht1 t ht]
    convert (hasDerivAt_log_log ht0.ne' (by linarith [ht1 t ht])
      (by linarith [ht1 t ht])).add_const B using 1
    simp only [div_eq_mul_inv, mul_inv, one_mul]
  have hiA : IntervalIntegrable (fun t => 1 / (t * log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one (ht1 t ht))
    have hlt : log t ≠ 0 := (log_pos (ht1 t ht)).ne'
    have hden : t * log t ≠ 0 := mul_ne_zero ht0 hlt
    fun_prop
  have hiS : IntervalIntegrable
      (fun t => H' t * ∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) volume a b := by
    have hs := IntervalIntegrable.sum (Nat.primesBelow ⌈b⌉₊)
      (fun p _ => abel_atom_integrable H' a b p (1 / p) hi)
    apply hs.congr
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    simp only [Finset.sum_apply]
    rw [← prime_cumulative_restrict t b ht.2, mul_sum]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> simp
  have herr : ∀ t ∈ Set.Icc a b,
      |(∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)| ≤
        1 / (2 * log a ^ 2) := by
    intro t ht
    have hfirst := mertens_strict_error B t (ha.trans ht.1) hlo hup
    have hlog : log a ≤ log t := log_le_log (by linarith) ht.1
    have hloga : 0 < log a := log_pos ha1
    have hden : 2 * log a ^ 2 ≤ 2 * log t ^ 2 := by nlinarith
    have hsecond := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
      (show 0 < 2 * log a ^ 2 by positivity) hden
    convert hfirst.trans hsecond using 1 <;> congr 1 <;> ring
  have hv := greaves_variation H H' (fun t => log (log t) + B)
    (fun t => 1 / (t * log t))
    (fun t => ∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p)
    a b (1 / (2 * log a ^ 2))
    (∑ p ∈ (Nat.primesBelow ⌈b⌉₊).filter (fun p : ℕ => a ≤ (p : ℝ)), H p / p)
    hab hd hdA hi hiA hiS herr (prime_abel_strict H H' a b hab hd hi)
  simpa only [mul_one_div, one_div_mul_eq_div] using hv

/-- Decreasing nonnegative weights cost H at the lower endpoint over log squared.
This is the outer application on journal p. 1239.
CONDITIONAL ON Rosser and Schoenfeld Theorem 5. -/
theorem greaves_prime_antitone (H H' : ℝ → ℝ) (a b B : ℝ)
    (ha : 286 ≤ a) (hab : a ≤ b)
    (hd : ∀ t ∈ Set.uIcc a b, HasDerivAt H (H' t) t)
    (hi : IntervalIntegrable H' volume a b)
    (hHa : 0 ≤ H a) (hHb : 0 ≤ H b)
    (hD : ∀ t ∈ Set.Icc a b, H' t ≤ 0)
    (hlo : ∀ y : ℝ, 1 < y → log (log y) + B - 1 / (2 * log y ^ 2) <
      ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p)
    (hup : ∀ y : ℝ, 286 ≤ y → (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) <
      log (log y) + B + 1 / (2 * log y ^ 2)) :
    (∑ p ∈ (Nat.primesBelow ⌈b⌉₊).filter (fun p : ℕ => a ≤ (p : ℝ)), H p / p) ≤
      (∫ t in a..b, H t / (t * log t)) + H a / log a ^ 2 := by
  have hv := greaves_prime_variation H H' a b B ha hab hd hi hlo hup
  have hvariation : (∫ t in a..b, |H' t|) = H a - H b := by
    calc
      _ = ∫ t in a..b, -H' t := by
        apply integral_congr
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        exact abs_of_nonpos (hD t ht)
      _ = H a - H b := by
        rw [intervalIntegral.integral_neg, integral_eq_sub_of_hasDerivAt hd hi]
        ring
  rw [abs_of_nonneg hHb,
    abs_of_nonneg hHa, hvariation] at hv
  have heq : (H b + H a + (H a - H b)) / (2 * log a ^ 2) = H a / log a ^ 2 := by
    have hlog : log a ≠ 0 := (log_pos (show 1 < a by linarith)).ne'
    field_simp
    <;> ring
  rw [heq] at hv
  linarith [(le_abs_self _).trans hv]

/-- The outer H weight is nonnegative and has nonpositive derivative.
The domain is the full interval z to y in journal p. 1238. -/
theorem H_signs (N u : ℝ) (hN : 1 < N)
    (hu : u ∈ Set.Icc (N ^ (1 / 8 : ℝ)) (N ^ (1 / 3 : ℝ))) :
    0 ≤ SliceMass236.H N u ∧ SliceMass236.Hderiv N u ≤ 0 := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < log N := log_pos hN
  have hu0 : 0 < u := (rpow_pos_of_pos hN0 _).trans_le hu.1
  have hlu : log N / 8 ≤ log u ∧ log u ≤ log N / 3 := by
    have hl := log_le_log (rpow_pos_of_pos hN0 (1 / 8 : ℝ)) hu.1
    have hr := log_le_log hu0 hu.2
    rw [log_rpow hN0] at hl hr
    constructor <;> linarith
  have hy : log (N ^ (1 / 3 : ℝ)) = log N / 3 := by rw [log_rpow hN0]; ring
  let A := log N - log u
  let Y := log N / 3
  let B := A - Y
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hB : 0 < B := by dsimp [B, A, Y]; linarith [hlu.2]
  have hA : 0 < A := by dsimp [A]; linarith [hlu.2]
  have hYB : Y ≤ B := by dsimp [Y, B, A]; linarith [hlu.2]
  have hC0 : 0 ≤ log B - log Y := sub_nonneg.mpr (log_le_log hY hYB)
  have hratio : B / Y ≤ 13 / 8 := by
    rw [div_le_iff₀ hY]
    dsimp [B, A, Y]
    linarith [hlu.1]
  have hC1 : log B - log Y ≤ 5 / 8 := by
    rw [← log_div hB.ne' hY.ne']
    have h := log_le_sub_one_of_pos (div_pos hB hY)
    linarith
  have hAB : 1 ≤ A / B := by
    rw [le_div_iff₀ hB]
    dsimp [B]
    linarith
  constructor
  · unfold SliceMass236.H
    rw [hy]
    exact div_nonneg hC0 hA.le
  · unfold SliceMass236.Hderiv
    rw [hy]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- The outer H endpoint obeys the printed 0.56 over log N bound. -/
theorem H_at_z_bound (N : ℝ) (hN : 1 < N) :
    SliceMass236.H N (N ^ (1 / 8 : ℝ)) ≤ 0.56 / log N := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < log N := log_pos hN
  rw [SliceMass236.H_rpow N (1 / 8 : ℝ) hN (by norm_num)]
  norm_num
  have hh := LeanLab.BS2022GRH.Hz_const
  have heq : log (13 / 8 : ℝ) / ((7 / 8) * log N) =
      (8 / 7 * log (13 / 8 : ℝ)) / log N := by field_simp [hL.ne'] <;> ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ hL.le
  linarith

/-- Smoothness and integrability for the outer H weight, journal pp. 1238 and 1239. -/
theorem H_regular (N : ℝ) (hN : 1 < N) :
    (∀ u ∈ Set.uIcc (N ^ (1 / 8 : ℝ)) (N ^ (1 / 3 : ℝ)),
      HasDerivAt (SliceMass236.H N) (SliceMass236.Hderiv N u) u) ∧
    IntervalIntegrable (SliceMass236.Hderiv N) volume
      (N ^ (1 / 8 : ℝ)) (N ^ (1 / 3 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < log N := log_pos hN
  have hab : N ^ (1 / 8 : ℝ) ≤ N ^ (1 / 3 : ℝ) :=
    rpow_le_rpow_of_exponent_le hN.le (by norm_num)
  have hguards (u : ℝ) (hu : u ∈ Set.uIcc (N ^ (1 / 8 : ℝ)) (N ^ (1 / 3 : ℝ))) :
      0 < u ∧ 0 < log N - log u - log (N ^ (1 / 3 : ℝ)) := by
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 < u := (rpow_pos_of_pos hN0 _).trans_le hu.1
    have hlu := log_le_log hu0 hu.2
    rw [log_rpow hN0] at hlu ⊢
    exact ⟨hu0, by linarith⟩
  constructor
  · intro u hu
    exact SliceMass236.H_hasDeriv N u hN (hguards u hu).1 (hguards u hu).2
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro u hu
    obtain ⟨hu0, hgap⟩ := hguards u hu
    have hY : 0 < log (N ^ (1 / 3 : ℝ)) := by rw [log_rpow hN0]; positivity
    have hA : log N - log u ≠ 0 := by linarith
    unfold SliceMass236.Hderiv
    fun_prop (disch := first | assumption | positivity)

/-- The paper threshold puts z in the unconditional Mertens range. -/
theorem z_mertens_range (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) :
    286 ≤ U7153.zz n := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hL := Lemma11C164.log_lower n hn
  have hz : exp 100 ≤ U7153.zz n := by
    apply (le_log_iff_exp_le (rpow_pos_of_pos hn0 (1 / 8 : ℝ))).mp
    rw [log_rpow hn0]
    linarith
  have he := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 100) 3
  norm_num [sum_range_succ] at he
  linarith

/-- The exact prime set for the outer strict Abel identity, journal p. 1238. -/
theorem Qset_eq_strict_interval (n : ℕ) (hn : 1 < (n : ℝ)) :
    U7153.Qset n = (Nat.primesBelow ⌈U7153.yy n⌉₊).filter
      (fun p : ℕ => U7153.zz n ≤ (p : ℝ)) := by
  have hyN : U7153.yy n ≤ (n : ℝ) := by
    unfold U7153.yy
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hn.le (by norm_num : (1 / 3 : ℝ) ≤ 1)
  ext p
  simp only [U7153.Qset, mem_filter, mem_range, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hpn, hp, hz, hy⟩
    exact ⟨⟨Nat.lt_ceil.mpr hy, hp⟩, hz⟩
  · rintro ⟨⟨hpy, hp⟩, hz⟩
    have hy := Nat.lt_ceil.mp hpy
    exact ⟨Nat.lt_succ_of_le (Nat.cast_le.mp (hy.le.trans hyN)), hp, hz, hy⟩

/-- The outer prime sum follows from the source Mertens inequalities.
CONDITIONAL ON Rosser and Schoenfeld Theorem 5, journal p. 1239. -/
theorem outer_prime_sum_of_mertens (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) (B : ℝ)
    (hlo : ∀ y : ℝ, 1 < y → log (log y) + B - 1 / (2 * log y ^ 2) <
      ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p)
    (hup : ∀ y : ℝ, 286 ≤ y → (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) <
      log (log y) + B + 1 / (2 * log y ^ 2)) :
    (∑ p ∈ U7153.Qset n, SliceMass236.H n p / p) ≤
      (∫ u in U7153.zz n..U7153.yy n, SliceMass236.H n u / (u * log u)) +
        36 / log n ^ 3 := by
  have hn1 : 1 < (n : ℝ) := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < log (n : ℝ) := log_pos hn1
  have hab : U7153.zz n ≤ U7153.yy n :=
    rpow_le_rpow_of_exponent_le hn1.le (by norm_num)
  obtain ⟨hd, hi⟩ := H_regular n hn1
  have hs := greaves_prime_antitone (SliceMass236.H n) (SliceMass236.Hderiv n)
    (U7153.zz n) (U7153.yy n) B (z_mertens_range n hn) hab hd hi
    (H_signs n (U7153.zz n) hn1 ⟨le_rfl, hab⟩).1
    (by rw [U7153.yy, SliceMass236.H_at_y n hn1])
    (fun u hu => (H_signs n u hn1 hu).2) hlo hup
  rw [← Qset_eq_strict_interval n hn1] at hs
  have herr : SliceMass236.H n (U7153.zz n) / log (U7153.zz n) ^ 2 ≤ 36 / log n ^ 3 := by
    calc
      _ ≤ (0.56 / log n) / log (U7153.zz n) ^ 2 :=
        div_le_div_of_nonneg_right (H_at_z_bound n hn1) (sq_nonneg _)
      _ ≤ _ := by
        rw [U7153.zz, log_rpow hn0]
        have he : (0.56 / log n) / ((1 / 8 : ℝ) * log n) ^ 2 =
            35.84 / log n ^ 3 := by
          field_simp [hL.ne']
          <;> ring
        rw [he]
        exact div_le_div_of_nonneg_right (by norm_num : (35.84 : ℝ) ≤ 36)
          (pow_nonneg hL.le 3)
  exact hs.trans (add_le_add le_rfl herr)

/-- Scalar normalization of the inner endpoint, journal p. 1238.
Here L is log N, r is log p and s is log of one plus epsilon one. -/
theorem inner_endpoint_denominator (L r s : ℝ) :
    L - r - (L + s - r) / 2 = (L - r - s) / 2 := by
  ring

/-- A diagnostic for the printed inner endpoint bound, journal p. 1238.
If log p is sufficiently close to log N over three, that bound is reversed.
This statement does not assert that the sealed prime sum is false. -/
theorem inner_endpoint_three_gap (L r s : ℝ) (hL : 0 < L)
    (hden : 0 < L - r - s) (hnear : L / 3 - s < r) :
    3 / L < 1 / (L - r - (L + s - r) / 2) := by
  rw [inner_endpoint_denominator]
  apply (div_lt_div_iff₀ hL (by linarith : 0 < (L - r - s) / 2)).mpr
  nlinarith

/-- A concrete scalar instance of the endpoint diagnostic, journal p. 1238.
The epsilon value is one half and s is log of three halves. -/
theorem inner_endpoint_three_instance :
    3 / (30000 : ℝ) <
      1 / (30000 - 9999.9 - (30000 + log (3 / 2) - 9999.9) / 2) := by
  have hlo := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have hup := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  norm_num at hlo hup
  apply inner_endpoint_three_gap <;> linarith

/-- The short endpoint integral after the logarithmic substitution on p. 1238.
Here A is half of log N minus log p and Y is log y. -/
theorem short_log_integral_bound (A Y s : ℝ) (hY : 0 < Y)
    (hAY : Y ≤ A) (hs : 0 ≤ s) (hsY : s < Y) :
    (∫ v in 0..s, 1 / (A ^ 2 - v ^ 2)) ≤ s / (Y ^ 2 - s ^ 2) := by
  have hAY2 : Y ^ 2 ≤ A ^ 2 := by nlinarith [mul_self_le_mul_self hY.le hAY]
  have hs2 : s ^ 2 < Y ^ 2 := by nlinarith [mul_self_lt_mul_self hs hsY]
  have hden : 0 < Y ^ 2 - s ^ 2 := by linarith
  have hcont : ContinuousOn (fun v : ℝ => 1 / (A ^ 2 - v ^ 2)) (Set.uIcc 0 s) := by
    apply continuousOn_of_forall_continuousAt
    intro v hv
    rw [Set.uIcc_of_le hs] at hv
    have hd : 0 < A ^ 2 - v ^ 2 := by nlinarith [mul_self_le_mul_self hv.1 hv.2]
    fun_prop (disch := positivity)
  have hbound := integral_mono_on hs hcont.intervalIntegrable
    (intervalIntegrable_const (μ := volume) (c := 1 / (Y ^ 2 - s ^ 2))) (fun v hv => ?_)
  · simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one_div] using hbound
  · have hd : Y ^ 2 - s ^ 2 ≤ A ^ 2 - v ^ 2 := by
      nlinarith [mul_self_le_mul_self hv.1 hv.2]
    exact div_le_div_of_nonneg_left (by norm_num) hden hd

/-- Exact substitution into the inner logarithm, journal p. 1238 definitions.
The epsilon logarithm has a minus sign. -/
theorem inner_endpoint_log (N p ε : ℝ) (hN : 0 < N) (hp : 0 < p) (hε : 0 < 1 + ε) :
    log (N / (p * √((1 + ε) * N / p))) =
      (log N - log p - log (1 + ε)) / 2 := by
  have hx : 0 < (1 + ε) * N / p := div_pos (mul_pos hε hN) hp
  have hs : √((1 + ε) * N / p) ≠ 0 := (sqrt_pos.mpr hx).ne'
  rw [log_div hN.ne' (mul_ne_zero hp.ne' hs), log_mul hp.ne' hs,
    sqrt_eq_rpow, log_rpow hx,
    log_div (mul_ne_zero hε.ne' hN.ne') hp.ne', log_mul hε.ne' hN.ne']
  ring

/-- The scalar endpoint gap also occurs with the exact real logarithms and square root.
The real p lies between z and y. No prime or natural number assertion is made. -/
theorem inner_real_endpoint_instance :
    (exp (30000 : ℝ)) ^ (1 / 8 : ℝ) ≤ exp (9999.9 : ℝ) ∧
    exp (9999.9 : ℝ) < (exp (30000 : ℝ)) ^ (1 / 3 : ℝ) ∧
    3 / log (exp (30000 : ℝ)) <
      1 / log (exp (30000 : ℝ) /
        (exp (9999.9 : ℝ) * √((1 + (1 / 2 : ℝ)) * exp (30000 : ℝ) / exp (9999.9 : ℝ)))) := by
  constructor
  · rw [rpow_def_of_pos (exp_pos _), log_exp]
    apply exp_le_exp.mpr
    norm_num
  constructor
  · rw [rpow_def_of_pos (exp_pos _), log_exp]
    apply exp_lt_exp.mpr
    norm_num
  · rw [inner_endpoint_log _ _ _ (exp_pos _) (exp_pos _) (by norm_num), log_exp, log_exp]
    have h := inner_endpoint_three_instance
    rw [inner_endpoint_denominator] at h
    norm_num at h ⊢
    exact h

/-- The unweighted outer prime reciprocal bound needs no parity hypothesis.
CONDITIONAL ON Rosser and Schoenfeld Theorem 5, journal p. 1238. -/
theorem reciprocal_prime_interval_of_mertens (n : ℕ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (B : ℝ)
    (hlo : ∀ y : ℝ, 1 < y → log (log y) + B - 1 / (2 * log y ^ 2) <
      ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p)
    (hup : ∀ y : ℝ, 286 ≤ y → (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) <
      log (log y) + B + 1 / (2 * log y ^ 2)) :
    (∑ p ∈ U7153.Qset n, (1 : ℝ) / p) ≤ log (8 / 3) + 64 / log n ^ 2 := by
  have hn1 : 1 < (n : ℝ) := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < log (n : ℝ) := log_pos hn1
  have hab : U7153.zz n ≤ U7153.yy n :=
    rpow_le_rpow_of_exponent_le hn1.le (by norm_num)
  have hz := z_mertens_range n hn
  have ht1 (t : ℝ) (ht : t ∈ Set.uIcc (U7153.zz n) (U7153.yy n)) : 1 < t := by
    rw [Set.uIcc_of_le hab] at ht
    linarith [ht.1]
  have hd : ∀ t ∈ Set.uIcc (U7153.zz n) (U7153.yy n),
      HasDerivAt (fun t => log (log t)) (1 / (t * log t)) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht1 t ht]
    convert hasDerivAt_log_log ht0.ne' (by linarith [ht1 t ht])
      (by linarith [ht1 t ht]) using 1
    simp only [div_eq_mul_inv, mul_inv, one_mul]
  have hi : IntervalIntegrable (fun t => 1 / (t * log t)) volume
      (U7153.zz n) (U7153.yy n) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    have ht0 : 0 < t := by linarith [ht1 t ht]
    have hlt : 0 < log t := log_pos (ht1 t ht)
    fun_prop (disch := positivity)
  have hs := greaves_prime_antitone (fun _ => 1) (fun _ => 0)
    (U7153.zz n) (U7153.yy n) B hz hab (fun t _ => hasDerivAt_const t 1)
    (intervalIntegrable_const (c := 0)) (by norm_num) (by norm_num)
    (fun _ _ => by norm_num) hlo hup
  rw [← Qset_eq_strict_interval n hn1] at hs
  have hmain : (∫ t in U7153.zz n..U7153.yy n, 1 / (t * log t)) = log (8 / 3) := by
    rw [integral_eq_sub_of_hasDerivAt hd hi, U7153.yy, U7153.zz,
      log_rpow hn0, log_rpow hn0,
      ← log_div (show (1 / 3 : ℝ) * log n ≠ 0 by positivity)
        (show (1 / 8 : ℝ) * log n ≠ 0 by positivity)]
    congr 1
    field_simp [hL.ne']
    <;> ring
  have herr : 1 / log (U7153.zz n) ^ 2 = 64 / log n ^ 2 := by
    rw [U7153.zz, log_rpow hn0]
    field_simp [hL.ne']
    <;> ring
  simpa only [hmain, herr] using hs

/-- The uniform Abel endpoint estimate exceeds the requested 27 error in this regime.
This diagnoses a proof bound, not the actual prime sum, journal p. 1238. -/
theorem inner_uniform_error_gap (L r s : ℝ) (hL : 0 < L)
    (hden : 0 < L - r - s) (hnear : L / 3 - s < r) :
    27 / L ^ 3 < (1 / (L - r - (L + s - r) / 2)) / (L / 3) ^ 2 := by
  have h := div_lt_div_of_pos_right (inner_endpoint_three_gap L r s hL hden hnear)
    (show 0 < (L / 3) ^ 2 by positivity)
  have he : (3 / L) / (L / 3) ^ 2 = 27 / L ^ 3 := by
    field_simp [hL.ne']
    <;> ring
  rwa [he] at h

/-- A concrete natural domain witness for the outer summation, journal p. 1239.
The natural number is the ceiling of the stated threshold. -/
theorem outer_domain_instance : ∃ n : ℕ,
    exp (exp 10) ≤ (n : ℝ) ∧ 286 ≤ U7153.zz n ∧ U7153.zz n ≤ U7153.yy n ∧
    SliceMass236.H n (U7153.yy n) = 0 := by
  let n : ℕ := ⌈exp (exp 10)⌉₊
  have hn : exp (exp 10) ≤ (n : ℝ) := Nat.le_ceil _
  have hn1 : 1 < (n : ℝ) := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hn
  refine ⟨n, hn, z_mertens_range n hn,
    rpow_le_rpow_of_exponent_le hn1.le (by norm_num), ?_⟩
  simpa only [U7153.yy] using SliceMass236.H_at_y n hn1

/-- The task236 inner integral is exactly the H used by the prime summations.
This retains the square root endpoint and every logarithmic guard on p. 1238. -/
theorem H_integral_identity (N p : ℝ) (hN : 1 < N) (hp : 0 < p)
    (hyR : N ^ (1 / 3 : ℝ) ≤ √(N / p)) :
    SliceMass236.H N p =
      ∫ t in N ^ (1 / 3 : ℝ)..√(N / p),
        1 / (t * log t * (log N - log p - log t)) := by
  have hN0 : 0 < N := by linarith
  have hy1 : 1 < N ^ (1 / 3 : ℝ) := by
    rw [rpow_def_of_pos hN0]
    exact one_lt_exp_iff.mpr (mul_pos (log_pos hN) (by norm_num))
  exact (SliceMass236.inner_integral_eq N p (N ^ (1 / 3 : ℝ)) hN0 hp hy1 hyR).symm

/-- The outer interval contains a prime at the paper threshold, journal p. 1238.
Bertrand supplies a prime between ceiling z and twice that ceiling.
This certifies a nonempty prime summation domain without a numerical prime search. -/
theorem Qset_nonempty (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) :
    (U7153.Qset n).Nonempty := by
  have hn1 : 1 < (n : ℝ) := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hz := z_mertens_range n hn
  have hz0 : 0 < U7153.zz n := by linarith
  have hz2 : U7153.zz n ^ 2 = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [U7153.zz, ← rpow_natCast, ← rpow_mul hn0.le]
    norm_num
  have hz2y : U7153.zz n ^ 2 ≤ U7153.yy n := by
    rw [hz2]
    exact rpow_le_rpow_of_exponent_le hn1.le (by norm_num)
  let m : ℕ := ⌈U7153.zz n⌉₊
  have hm : 0 < (m : ℝ) := hz0.trans_le (Nat.le_ceil _)
  have hm0 : m ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨p, hprime, hmp, hpm⟩ := Nat.exists_prime_lt_and_le_two_mul m hm0
  have hzp : U7153.zz n ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hmp.le)
  have hfour : 4 * U7153.zz n ≤ U7153.zz n ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (show (4 : ℝ) ≤ U7153.zz n by linarith) hz0.le
    nlinarith
  have hpy : (p : ℝ) < U7153.yy n := by
    have hpmR : (p : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hpm
    have hmR : (m : ℝ) < U7153.zz n + 1 := Nat.ceil_lt_add_one hz0.le
    nlinarith
  refine ⟨p, ?_⟩
  rw [Qset_eq_strict_interval n hn1]
  exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨Nat.lt_ceil.mpr hpy, hprime⟩, hzp⟩

end
end LeanLab.BS2022GRH.Decomp543a

#print axioms LeanLab.BS2022GRH.Decomp543a.rosser_schoenfeld_theorem5
#print axioms LeanLab.BS2022GRH.Decomp543a.abel_atom
#print axioms LeanLab.BS2022GRH.Decomp543a.abel_atom_integrable
#print axioms LeanLab.BS2022GRH.Decomp543a.finite_abel_strict
#print axioms LeanLab.BS2022GRH.Decomp543a.greaves_variation
#print axioms LeanLab.BS2022GRH.Decomp543a.mertens_strict_error
#print axioms LeanLab.BS2022GRH.Decomp543a.prime_cumulative_restrict
#print axioms LeanLab.BS2022GRH.Decomp543a.prime_abel_strict
#print axioms LeanLab.BS2022GRH.Decomp543a.greaves_prime_variation
#print axioms LeanLab.BS2022GRH.Decomp543a.greaves_prime_antitone
#print axioms LeanLab.BS2022GRH.Decomp543a.H_signs
#print axioms LeanLab.BS2022GRH.Decomp543a.H_at_z_bound
#print axioms LeanLab.BS2022GRH.Decomp543a.H_regular
#print axioms LeanLab.BS2022GRH.Decomp543a.z_mertens_range
#print axioms LeanLab.BS2022GRH.Decomp543a.Qset_eq_strict_interval
#print axioms LeanLab.BS2022GRH.Decomp543a.outer_prime_sum_of_mertens
#print axioms LeanLab.BS2022GRH.Decomp543a.inner_endpoint_denominator
#print axioms LeanLab.BS2022GRH.Decomp543a.inner_endpoint_three_gap
#print axioms LeanLab.BS2022GRH.Decomp543a.inner_endpoint_three_instance

#print axioms LeanLab.BS2022GRH.Decomp543a.short_log_integral_bound

#print axioms LeanLab.BS2022GRH.Decomp543a.inner_endpoint_log
#print axioms LeanLab.BS2022GRH.Decomp543a.inner_real_endpoint_instance

#print axioms LeanLab.BS2022GRH.Decomp543a.reciprocal_prime_interval_of_mertens

#print axioms LeanLab.BS2022GRH.Decomp543a.inner_uniform_error_gap

#print axioms LeanLab.BS2022GRH.Decomp543a.outer_domain_instance

#print axioms LeanLab.BS2022GRH.Decomp543a.H_integral_identity

#print axioms LeanLab.BS2022GRH.Decomp543a.Qset_nonempty
