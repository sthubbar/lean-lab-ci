import LeanLab.ChenDoubleSieve.Decomp349f
import LeanLab.ChenDoubleSieve.Decomp366b
import LeanLab.ChenDoubleSieve.Decomp366f

/-!
Weighted prime sum preparation for Wu 2004 page 39.
Source: https://arxiv.org/pdf/0705.1652, equation 10.3.
The existing prime triangle limit supplies a quadratic moment.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory intervalIntegral
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- The separable triangular integral is half the square of the full integral.
This is a calculus helper for identifying the quadratic prime sum limit. -/
theorem tail_integral_square {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.uIcc a b)) :
    (∫ x in a..b, f x * (∫ y in x..b, f y)) = (∫ x in a..b, f x) ^ 2 / 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  let A : ℝ → ℝ := fun x => ∫ y in a..x, f y
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable
  have hAc : ContinuousOn A (Set.uIcc a b) :=
    continuousOn_primitive_interval' hfi Set.left_mem_uIcc
  have hleft : ∀ x ∈ Set.uIcc a b, IntervalIntegrable f volume a x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    apply hfi.mono_set
    rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc_right hx.2
  have hright : ∀ x ∈ Set.uIcc a b, IntervalIntegrable f volume x b := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    apply hfi.mono_set
    rw [Set.uIcc_of_le hx.2, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc_left hx.1
  have hfo : ContinuousOn f (Set.Ioo a b) := hf.mono (by
    intro x hx
    rw [Set.uIcc_of_le hab]
    exact ⟨hx.1.le, hx.2.le⟩)
  have hDeriv : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt A (f x) x := by
    intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    have hxAB : x ∈ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]
      exact ⟨hx.1.le, hx.2.le⟩
    have hsm : StronglyMeasurableAtFilter f (𝓝 x) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hfo x hx
    exact intervalIntegral.integral_hasDerivAt_right (hleft x hxAB) hsm
      (hfo.continuousAt (isOpen_Ioo.mem_nhds hx))
  have hp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hAc hAc hDeriv hDeriv hfi hfi
  have hFA : IntervalIntegrable (fun x => f x * A x) volume a b :=
    hfi.mul_continuousOn hAc
  have htwice : (∫ x in a..b, f x * A x + A x * f x) =
      2 * ∫ x in a..b, f x * A x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [htwice] at hp
  have htwo : 2 * (∫ x in a..b, f x * A x) = (∫ x in a..b, f x) ^ 2 := by
    simpa only [A, intervalIntegral.integral_same, mul_zero, sub_zero, pow_two] using hp
  have htail : ∀ x ∈ Set.uIcc a b,
      (∫ y in x..b, f y) = (∫ y in a..b, f y) - A x := by
    intro x hx
    have hs := intervalIntegral.integral_add_adjacent_intervals (hleft x hx) (hright x hx)
    change A x + (∫ y in x..b, f y) = (∫ y in a..b, f y) at hs
    linarith
  have htarget : (∫ x in a..b, f x * (∫ y in x..b, f y)) =
      (∫ x in a..b, f x) ^ 2 - ∫ x in a..b, f x * A x := by
    calc
      _ = ∫ x in a..b, f x * (∫ y in a..b, f y) - f x * A x := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [htail x hx]
        ring
      _ = (∫ x in a..b, f x) * (∫ x in a..b, f x) - ∫ x in a..b, f x * A x := by
        rw [intervalIntegral.integral_sub (hfi.mul_const _) hFA, intervalIntegral.integral_mul_const]
      _ = _ := by ring
  rw [htarget]
  nlinarith

/-- Reciprocal prime averaging in the exact ordinary upper prime band. -/
def weightedPrimeSum (φ : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ Task366.primeBand4 N, φ (log (p : ℝ) / log N) / p

/-- A bounded continuous prime weight has a vanishing reciprocal square diagonal. -/
theorem weightedPrimeSum_diagonal_tendsto (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc kappa1 kappa2)) :
    Tendsto (fun N : ℕ => ∑ p ∈ Task366.primeBand4 N,
      φ (log (p : ℝ) / log N) ^ 2 / ((p : ℝ) * p)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  let K : ℝ := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  have hbound : ∀ t ∈ Set.Icc kappa1 kappa2, |φ t| ≤ K := by
    intro t ht
    have h := hC t ht
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hzero : Tendsto (fun N : ℕ => K ^ 2 *
      ∑ p ∈ Task366.primeBand4 N, 1 / ((p : ℝ) * p)) atTop (𝓝 0) := by
    simpa using Task366.primeBand4_diagonal_tendsto.const_mul (K ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun N => Finset.sum_nonneg (by intros; positivity))) _ hzero
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hmem := hp
  simp only [Task366.primeBand4, lowerPrimeBand, Finset.mem_filter, Finset.mem_range] at hmem
  have hprime := hmem.1.2.1
  have ht : log (p : ℝ) / log N ∈ Set.Icc kappa1 kappa2 := by
    exact ⟨(Task367.power_cutoff_le_iff hN hprime.pos kappa1).mp hmem.1.2.2,
      ((Task367.lt_power_cutoff_iff hN hprime.pos kappa2).mp hmem.2).le⟩
  have hsquare : φ (log (p : ℝ) / log N) ^ 2 ≤ K ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (φ (log (p : ℝ) / log N))) hK).mpr (hbound _ ht)
    simpa only [sq_abs] using h
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hsquare
    (by positivity : 0 ≤ (p : ℝ) * p)

/-- The prime triangle coefficient is half the square of the weighted integral. -/
theorem weighted_triangle_integral_square (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc kappa1 kappa2)) :
    (∫ t in kappa1..kappa2,
      (∫ u in t..kappa2, φ t * φ u / u) / t) =
      (∫ t in kappa1..kappa2, φ t / t) ^ 2 / 2 := by
  have hab : kappa1 ≤ kappa2 := by norm_num [kappa1, kappa2]
  have hc : ContinuousOn (fun t => φ t / t) (Set.uIcc kappa1 kappa2) := by
    rw [Set.uIcc_of_le hab]
    refine hφ.div continuousOn_id ?_
    intro t ht
    have hk : 0 < kappa1 := by norm_num [kappa1]
    linarith [ht.1]
  have hform : (∫ t in kappa1..kappa2,
      (∫ u in t..kappa2, φ t * φ u / u) / t) =
      ∫ t in kappa1..kappa2, (φ t / t) * (∫ u in t..kappa2, φ u / u) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have hi : (∫ u in t..kappa2, φ t * φ u / u) =
        φ t * ∫ u in t..kappa2, φ u / u := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      ring
    rw [hi]
    ring
  rw [hform]
  exact tail_integral_square hab hc

/-- The quadratic weighted prime moment follows from the existing triangle limit. -/
theorem weightedPrimeSum_square_tendsto (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc kappa1 kappa2)) :
    Tendsto (fun N => weightedPrimeSum φ N ^ 2) atTop
      (𝓝 ((∫ t in kappa1..kappa2, φ t / t) ^ 2)) := by
  have hgc : ContinuousOn (fun z : ℝ × ℝ => φ z.1 * φ z.2)
      (Set.Icc kappa1 kappa2 ×ˢ Set.Icc kappa1 kappa2) := by
    exact (hφ.comp continuousOn_fst (fun z hz => hz.1)).mul
      (hφ.comp continuousOn_snd (fun z hz => hz.2))
  have htri := Task366.continuous_prime_triangle (fun z : ℝ × ℝ => φ z.1 * φ z.2) hgc
  have hdiag := weightedPrimeSum_diagonal_tendsto φ hφ
  have hlim := (htri.const_mul 2).add hdiag
  have hlim' : Tendsto (fun N : ℕ =>
      2 * (∑ q ∈ fullPairs4 N,
        (φ (log (q.1 : ℝ) / log N) * φ (log (q.2 : ℝ) / log N)) /
          ((q.1 : ℝ) * q.2)) +
      ∑ p ∈ Task366.primeBand4 N,
        φ (log (p : ℝ) / log N) ^ 2 / ((p : ℝ) * p)) atTop
      (𝓝 ((∫ t in kappa1..kappa2, φ t / t) ^ 2)) := by
    convert hlim using 1
    congr 1
    rw [weighted_triangle_integral_square φ hφ]
    ring
  apply hlim'.congr'
  apply Eventually.of_forall
  intro N
  let S : Finset ℕ := Task366.primeBand4 N
  let ψ : ℕ → ℝ := fun p => φ (log (p : ℝ) / log N)
  let k : ℕ × ℕ → ℝ := fun q => ψ q.1 * ψ q.2 / ((q.1 : ℝ) * q.2)
  have hs := Task366.symmetric_pair_sum S k (fun p q => by dsimp [k]; ring)
  have hrect : weightedPrimeSum φ N ^ 2 = ∑ q ∈ S ×ˢ S, k q := by
    unfold weightedPrimeSum
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    dsimp [k, ψ]
    ring
  dsimp only
  rw [hrect, hs]
  change _ = _
  rw [Task366.fullPairs4_as_triangle]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  dsimp [k, ψ]
  ring

/-- Continuous reciprocal prime weights converge to their logarithmic integral.
Polarization recovers the signed average from the quadratic moments. -/
theorem weightedPrimeSum_tendsto (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc kappa1 kappa2)) :
    Tendsto (weightedPrimeSum φ) atTop
      (𝓝 (∫ t in kappa1..kappa2, φ t / t)) := by
  let I : ℝ := ∫ t in kappa1..kappa2, φ t / t
  let M : ℝ := log (kappa2 / kappa1)
  let mass : ℕ → ℝ := fun N => ∑ p ∈ Task366.primeBand4 N, 1 / (p : ℝ)
  have hM : 0 < M := by
    dsimp [M]
    apply log_pos
    norm_num [kappa1, kappa2]
  have hab : kappa1 ≤ kappa2 := by norm_num [kappa1, kappa2]
  have hk1 : 0 < kappa1 := by norm_num [kappa1]
  have hk2 : 0 < kappa2 := by norm_num [kappa2]
  have hPhiI : IntervalIntegrable (fun t => φ t / t) volume kappa1 kappa2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hφ.div continuousOn_id (fun t ht => ne_of_gt (hk1.trans_le ht.1))
  have hOneI : IntervalIntegrable (fun t : ℝ => 1 / t) volume kappa1 kappa2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (hk1.trans_le ht.1))
  have hIntPlus : (∫ t in kappa1..kappa2, (φ t + 1) / t) = I + M := by
    calc
      _ = ∫ t in kappa1..kappa2, φ t / t + 1 / t := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        ring
      _ = I + M := by
        rw [intervalIntegral.integral_add hPhiI hOneI,
          _root_.integral_one_div_of_pos hk1 hk2]
  have hSumPlus : ∀ N : ℕ,
      weightedPrimeSum (fun t => φ t + 1) N = weightedPrimeSum φ N + mass N := by
    intro N
    unfold weightedPrimeSum
    dsimp only [mass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hmass : Tendsto mass atTop (𝓝 M) := Task366.primeBand4_mass_tendsto
  have hsquare := weightedPrimeSum_square_tendsto φ hφ
  have hplus := weightedPrimeSum_square_tendsto (fun t => φ t + 1)
    (hφ.add continuousOn_const)
  have hplus' : Tendsto (fun N => (weightedPrimeSum φ N + mass N) ^ 2)
      atTop (𝓝 ((I + M) ^ 2)) := by
    simpa only [hSumPlus, hIntPlus] using hplus
  have hdiff := ((hplus'.sub hsquare).sub (hmass.pow 2)).div_const 2
  have hprod : Tendsto (fun N => weightedPrimeSum φ N * mass N) atTop (𝓝 (I * M)) := by
    convert hdiff using 1
    · funext N
      try dsimp only [I]
      ring
    · congr 1
      try dsimp only [I]
      ring
  have hquot := hprod.div hmass hM.ne'
  have hquot' : Tendsto (fun N => (weightedPrimeSum φ N * mass N) / mass N)
      atTop (𝓝 I) := by
    simpa only [Pi.div_def, mul_div_cancel_right₀ _ hM.ne'] using hquot
  apply hquot'.congr'
  filter_upwards [hmass.eventually (eventually_gt_nhds hM)] with N hN
  exact mul_div_cancel_right₀ _ hN.ne'

end LeanLab.ChenDoubleSieve.Task349
