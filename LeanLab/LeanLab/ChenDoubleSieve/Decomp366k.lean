import LeanLab.ChenDoubleSieve.Decomp366j

/-!
The actual F4 sum limit for constant numerators.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
The coprimality and totient errors require no sieve function hypothesis here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348

/-- The actual constant numerator sum and unrestricted reciprocal sum have
vanishing difference for every fixed B, with no linear sieve hypothesis. -/
theorem lowerSum4_const_error (B c : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      |lowerSum4 (fun _ => c) B N - reciprocalFullSum4 (fun _ => c) B N| ≤ ε := by
  obtain ⟨J, hJ⟩ := totient_sum_error_small (κ := kappa1)
    (by norm_num [kappa1]) (abs_nonneg c) (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := weighted_coprimality_error_small (κ := kappa1)
    (by norm_num [kappa1]) (abs_nonneg c) (ε / 2) (by positivity)
  refine ⟨max J K, ?_⟩
  intro N hN
  have ht := hJ N (by omega) (lowerPrimeBand N) (lowerPrimeBand N)
    (lowerPrimeBand_range N) (lowerPrimeBand_range N) (fullPairs4 N)
    (fullPairs4_subset N) (fun _ hp => fullPairs4_primes hp)
    (fun _ => c) (by intros; exact le_refl _)
  have hc := hK N (by omega) (lowerPrimeBand N) (lowerPrimeBand N)
    (lowerPrimeBand_range N) (lowerPrimeBand_range N) (fullPairs4 N)
    (fullPairs4_subset N) (fun _ hp => fullPairs4_primes hp)
    (fun _ => c) (by intros; exact le_refl _)
  have ht' : |fullSum4 (fun _ => c) B N - reciprocalFullSum4 (fun _ => c) B N| ≤ ε / 2 := ht
  have hc' : |fullSum4 (fun _ => c) B N - lowerSum4 (fun _ => c) B N| ≤ ε / 2 := by
    unfold fullSum4 lowerSum4
    rw [lowerPairs4_eq_filter]
    exact hc
  have htri := abs_sub_le (lowerSum4 (fun _ => c) B N)
    (fullSum4 (fun _ => c) B N) (reciprocalFullSum4 (fun _ => c) B N)
  rw [abs_sub_comm (lowerSum4 (fun _ => c) B N) (fullSum4 (fun _ => c) B N)] at htri
  linarith

/-- Constant numerators have the exact unrestricted reciprocal product limit
for every finite logarithmic parameter. -/
theorem reciprocalFullSum4_const_tendsto (B c : ℝ) :
    Tendsto (reciprocalFullSum4 (fun _ => c) B) atTop
      (𝓝 (c * (log (kappa2 / kappa1) ^ 2 / 2))) := by
  apply (fullPairs4_mass_tendsto.const_mul c).congr'
  apply Eventually.of_forall
  intro N
  unfold reciprocalFullSum4 pairMass
  dsimp only
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  ring

/-- The actual coprime reciprocal totient F4 sum has the exact constant kernel
integral limit. This is unconditional and holds along all naturals. -/
theorem lowerSum4_const_tendsto (B c : ℝ) :
    Tendsto (lowerSum4 (fun _ => c) B) atTop (𝓝 (lowerIntegral4 (fun _ => c))) := by
  have ht : Tendsto (reciprocalFullSum4 (fun _ => c) B) atTop
      (𝓝 (lowerIntegral4 (fun _ => c))) := by
    rw [lowerIntegral4_const]
    exact reciprocalFullSum4_const_tendsto B c
  have hd : Tendsto (fun N => dist (reciprocalFullSum4 (fun _ => c) B N)
      (lowerSum4 (fun _ => c) B N)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨J, hJ⟩ := lowerSum4_const_error B c (ε / 2) (by positivity)
    refine ⟨J, ?_⟩
    intro N hN
    simpa only [Real.dist_eq, sub_zero, abs_abs, abs_sub_comm] using
      (hJ N hN).trans_lt (by linarith : ε / 2 < ε)
  exact ht.congr_dist hd

/-- The actual coprime ordered pair domain is nonempty for every sufficiently
large N. The positive limiting mass gives a nonvacuous tail instance. -/
theorem lowerPairs4_eventually_nonempty : ∀ᶠ N : ℕ in atTop, (lowerPairs4 N).Nonempty := by
  have hlog : 0 < log (kappa2 / kappa1) := log_pos (by norm_num [kappa1, kappa2])
  have hpos : 0 < lowerIntegral4 (fun _ => (1 : ℝ)) := by
    rw [lowerIntegral4_const]
    positivity
  have he := (lowerSum4_const_tendsto 0 1).eventually (eventually_gt_nhds hpos)
  filter_upwards [he] with N hN
  by_contra hn
  have hempty : lowerPairs4 N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simpa only [lowerSum4, hempty, sum_empty, lt_self_iff_false] using hN

end LeanLab.ChenDoubleSieve.Task366
