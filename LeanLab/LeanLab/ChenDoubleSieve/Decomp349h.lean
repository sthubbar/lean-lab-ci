import LeanLab.ChenDoubleSieve.Decomp349g

/-!
Actual prime band weights for Wu 2004 equation 10.3.
Source: https://arxiv.org/pdf/0705.1652, page 39.
The reciprocal totient shift and coprimality errors are treated separately.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- Exact logarithmic coordinates of the full ordinary upper prime band. -/
theorem primeBand4_coordinates {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ Task366.primeBand4 N) :
    log (p : ℝ) / log N ∈ Set.Ico kappa1 kappa2 := by
  have hmem := hp
  simp only [Task366.primeBand4, lowerPrimeBand, Finset.mem_filter, Finset.mem_range] at hmem
  have hprime := hmem.1.2.1
  exact ⟨(Task367.power_cutoff_le_iff hN hprime.pos kappa1).mp hmem.1.2.2,
    (Task367.lt_power_cutoff_iff hN hprime.pos kappa2).mp hmem.2⟩

/-- A continuous weight is uniformly bounded on all actual band coordinates. -/
theorem primeBand4_weight_bounded (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc kappa1 kappa2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ p ∈ Task366.primeBand4 N,
      |φ (log (p : ℝ) / log N)| ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro N hN p hp
  have ht := primeBand4_coordinates hN hp
  have hc := hC _ ⟨ht.1, ht.2.le⟩
  rw [Real.norm_eq_abs] at hc
  exact hc.trans (le_max_left _ _)

/-- The actual coprime band is the full band filtered by coprimality with N. -/
theorem upperBand_eq_filter {N : ℕ} (hN : 2 ≤ N) :
    Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2) =
      (Task366.primeBand4 N).filter (fun p => p.Coprime N) := by
  have hpow : (N : ℝ) ^ kappa2 ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N)
      (by norm_num [kappa2] : kappa2 ≤ 1)
  ext p
  simp only [Wu41.mem_PS, Task366.primeBand4, lowerPrimeBand,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hlo, hup, hcop⟩
    have hpN : p < N := by exact_mod_cast hup.trans_le hpow
    exact ⟨⟨⟨hpN, hp, hlo⟩, hup⟩, hcop⟩
  · rintro ⟨⟨⟨hpN, hp, hlo⟩, hup⟩, hcop⟩
    exact ⟨hp, hlo, hup, hcop⟩

/-- The full band average with the exact reciprocal prime totient weight. -/
def weightedTotientPrimeSum (φ : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ Task366.primeBand4 N, φ (log (p : ℝ) / log N) / ((p : ℝ) - 1)

/-- The actual coprime band average with reciprocal prime totient weights. -/
def weightedCoprimeTotientPrimeSum (φ : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
    φ (log (p : ℝ) / log N) / ((p : ℝ) - 1)

/-- The reciprocal totient replacement error is bounded by the prime diagonal. -/
theorem weightedTotientPrimeSum_error (φ : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    {N : ℕ} (hN : 2 ≤ N)
    (hφ : ∀ p ∈ Task366.primeBand4 N, |φ (log (p : ℝ) / log N)| ≤ K) :
    |weightedTotientPrimeSum φ N - weightedPrimeSum φ N| ≤
      (2 * K) * ∑ p ∈ Task366.primeBand4 N, 1 / ((p : ℝ) * p) := by
  have heq : weightedTotientPrimeSum φ N - weightedPrimeSum φ N =
      ∑ p ∈ Task366.primeBand4 N,
        φ (log (p : ℝ) / log N) * (1 / ((p : ℝ) - 1) - 1 / p) := by
    unfold weightedTotientPrimeSum weightedPrimeSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [heq, Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ Task366.primeBand4 N,
        |φ (log (p : ℝ) / log N) * (1 / ((p : ℝ) - 1) - 1 / p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem := hp
      simp only [Task366.primeBand4, lowerPrimeBand, Finset.mem_filter] at hmem
      have hprime := hmem.1.2.1
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hs := reciprocal_shift_error hp2 hp0 (le_refl (p : ℝ))
      rw [abs_mul, abs_of_nonneg hs.1]
      calc
        _ ≤ K * ((2 / (p : ℝ)) * (1 / p)) :=
          mul_le_mul (hφ p hp) hs.2.1 hs.1 hK
        _ = _ := by ring

/-- Reciprocal totient weights have the same continuous prime averaging limit. -/
theorem weightedTotientPrimeSum_tendsto (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc kappa1 kappa2)) :
    Tendsto (weightedTotientPrimeSum φ) atTop
      (𝓝 (∫ t in kappa1..kappa2, φ t / t)) := by
  obtain ⟨K, hK, hbound⟩ := primeBand4_weight_bounded φ hφ
  have hzero : Tendsto (fun N => (2 * K) *
      ∑ p ∈ Task366.primeBand4 N, 1 / ((p : ℝ) * p)) atTop (𝓝 0) := by
    simpa using Task366.primeBand4_diagonal_tendsto.const_mul (2 * K)
  have herr : Tendsto (fun N => weightedTotientPrimeSum φ N - weightedPrimeSum φ N)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) _ hzero
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact weightedTotientPrimeSum_error φ hK hN (hbound N hN)
  have ht := herr.add (weightedPrimeSum_tendsto φ hφ)
  simpa only [Pi.add_def, sub_add_cancel, zero_add] using ht

/-- Removing primes dividing N costs one inverse power cutoff in the band average. -/
theorem weightedCoprimeTotientPrimeSum_error (φ : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    {N : ℕ} (hN : 2 ≤ N)
    (hφ : ∀ p ∈ Task366.primeBand4 N, |φ (log (p : ℝ) / log N)| ≤ K) :
    |weightedTotientPrimeSum φ N - weightedCoprimeTotientPrimeSum φ N| ≤
      (2 * K) / (kappa1 * (N : ℝ) ^ kappa1) := by
  have hsplit : weightedCoprimeTotientPrimeSum φ N +
      (∑ p ∈ (Task366.primeBand4 N).filter (fun p => ¬ p.Coprime N),
        φ (log (p : ℝ) / log N) / ((p : ℝ) - 1)) = weightedTotientPrimeSum φ N := by
    unfold weightedCoprimeTotientPrimeSum weightedTotientPrimeSum
    rw [upperBand_eq_filter hN]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have heq : weightedTotientPrimeSum φ N - weightedCoprimeTotientPrimeSum φ N =
      ∑ p ∈ (Task366.primeBand4 N).filter (fun p => ¬ p.Coprime N),
        φ (log (p : ℝ) / log N) / ((p : ℝ) - 1) := by linarith
  have hrec := exceptional_reciprocal_sum_sharp (Task366.primeBand4 N) hN
    (by norm_num [kappa1] : 0 < kappa1) (fun p hp => by
      have hmem := hp
      simp only [Task366.primeBand4, lowerPrimeBand, Finset.mem_filter] at hmem
      exact ⟨hmem.1.2.1, hmem.1.2.2⟩)
  rw [heq]
  calc
    _ ≤ ∑ p ∈ (Task366.primeBand4 N).filter (fun p => ¬ p.Coprime N),
        |φ (log (p : ℝ) / log N) / ((p : ℝ) - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (Task366.primeBand4 N).filter (fun p => ¬ p.Coprime N),
        (2 * K) * (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpband : p ∈ Task366.primeBand4 N := (Finset.mem_filter.mp hp).1
      have hmem := hpband
      simp only [Task366.primeBand4, lowerPrimeBand, Finset.mem_filter] at hmem
      have hprime := hmem.1.2.1
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hs := reciprocal_shift_error hp2 hp0 (le_refl (p : ℝ))
      rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ (p : ℝ) - 1)]
      calc
        _ ≤ K / ((p : ℝ) - 1) := div_le_div_of_nonneg_right (hφ p hpband) (by linarith)
        _ = K * (1 / ((p : ℝ) - 1)) := by ring
        _ ≤ K * (2 * (1 / (p : ℝ))) := mul_le_mul_of_nonneg_left hs.2.2 hK
        _ = _ := by ring
    _ = (2 * K) * ∑ p ∈ (Task366.primeBand4 N).filter (fun p => ¬ p.Coprime N),
        1 / (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (2 * K) * (1 / (kappa1 * (N : ℝ) ^ kappa1)) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = _ := by ring

/-- The actual coprime reciprocal totient prime sum has the exact weighted limit. -/
theorem weightedCoprimeTotientPrimeSum_tendsto (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc kappa1 kappa2)) :
    Tendsto (weightedCoprimeTotientPrimeSum φ) atTop
      (𝓝 (∫ t in kappa1..kappa2, φ t / t)) := by
  obtain ⟨K, hK, hbound⟩ := primeBand4_weight_bounded φ hφ
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun N : ℕ => (2 * K) / (kappa1 * (N : ℝ) ^ kappa1))
      atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div] using hz.const_div_atTop (2 * K / kappa1)
  have herr : Tendsto (fun N => weightedTotientPrimeSum φ N - weightedCoprimeTotientPrimeSum φ N)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) _ hzero
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact weightedCoprimeTotientPrimeSum_error φ hK hN (hbound N hN)
  have ht := (weightedTotientPrimeSum_tendsto φ hφ).sub herr
  simpa only [Pi.sub_def, sub_sub_cancel, sub_zero] using ht

end LeanLab.ChenDoubleSieve.Task349
