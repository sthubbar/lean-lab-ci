import LeanLab.ChenDoubleSieve.Decomp348k

/-!
Apply the reciprocal totient error to the finite lower sieve sums in equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve)

/-- Reciprocal totient replacement is uniform over bounded prime pair sums. -/
theorem totient_sum_error_small {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ P Q : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ κ ≤ p ∧ p ≤ N) →
      (∀ q ∈ Q, q.Prime ∧ (N : ℝ) ^ κ ≤ q ∧ q ≤ N) →
      ∀ R : Finset (ℕ × ℕ), R ⊆ P ×ˢ Q →
      (∀ q ∈ R, q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2) →
      ∀ g : ℕ × ℕ → ℝ, (∀ q ∈ R, |g q| ≤ M) →
      |(∑ q ∈ R, g q / (Nat.totient (q.1 * q.2) : ℝ)) -
        ∑ q ∈ R, g q / ((q.1 : ℝ) * q.2)| ≤ ε := by
  have he : ∀ᶠ N : ℕ in atTop, (6 * M / (N : ℝ) ^ κ) * (1 + log N) ^ 2 < ε :=
    ((totient_bound_tendsto hκ M).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_lt_nhds hε)
  obtain ⟨K, hK⟩ := eventually_atTop.1 he
  refine ⟨max 2 K, ?_⟩
  intro N hN P Q hP hQ R hsub hR g hg
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 0 < (N : ℝ) ^ κ := rpow_pos_of_pos hpos _
  calc
    _ ≤ (6 * M / (N : ℝ) ^ κ) * pairMass R :=
      totient_sum_error R g hM hz (by
        intro q hq
        obtain ⟨hp, hq', hpq⟩ := hR q hq
        obtain ⟨hpP, hqQ⟩ := mem_product.mp (hsub hq)
        exact ⟨hp, hq', hpq, (hP _ hpP).2.1, (hQ _ hqQ).2.1⟩) hg
    _ ≤ (6 * M / (N : ℝ) ^ κ) * (1 + log N) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact pairMass_le_log_square P Q R (by omega) hsub
          (fun p hp => ⟨(hP p hp).1.one_le, (hP p hp).2.2⟩)
          (fun q hq => ⟨(hQ q hq).1.one_le, (hQ q hq).2.2⟩)
      · positivity
    _ ≤ ε := (hK N (by omega)).le

/-- The unrestricted F4 sum with reciprocal product weights. -/
def reciprocalFullSum4 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ fullPairs4 N, f (lowerLevel B N (q.1 * q.2)) / ((q.1 : ℝ) * q.2)

/-- Totient replacement is negligible for the actual unrestricted F4 sum.
CONDITIONAL ON IsLinearSieve only. -/
theorem fullSum4_totient_error (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → |fullSum4 f B N - reciprocalFullSum4 f B N| ≤ ε := by
  obtain ⟨M, hM, K, hK⟩ := lower_values_bounded F f h B hB
  intro ε hε
  obtain ⟨J, hJ⟩ := totient_sum_error_small (κ := kappa1)
    (by norm_num [kappa1]) hM ε hε
  refine ⟨max 2 (max K J), ?_⟩
  intro N hN
  exact hJ N (by omega) (lowerPrimeBand N) (lowerPrimeBand N)
    (lowerPrimeBand_range N) (lowerPrimeBand_range N) (fullPairs4 N)
    (fullPairs4_subset N) (fun _ hq => fullPairs4_primes hq)
    (fun q => f (lowerLevel B N (q.1 * q.2))) (by
      intro q hq
      obtain ⟨hd, hb⟩ := fullPairs4_product (by omega) hq
      exact hK N (by omega) _ hd hb)

/-- Both elementary replacements leave the actual F4 prime sum unchanged in the limit.
CONDITIONAL ON IsLinearSieve only. -/
theorem lowerSum4_reciprocal_error (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → |lowerSum4 f B N - reciprocalFullSum4 f B N| ≤ ε := by
  intro ε hε
  obtain ⟨K, hK⟩ := lowerSum4_coprimality F f h B hB (ε / 2) (by positivity)
  obtain ⟨J, hJ⟩ := fullSum4_totient_error F f h B hB (ε / 2) (by positivity)
  refine ⟨max K J, ?_⟩
  intro N hN
  have hfirst := hK N (by omega)
  have hsecond := hJ N (by omega)
  have htri := abs_sub_le (lowerSum4 f B N) (fullSum4 f B N) (reciprocalFullSum4 f B N)
  rw [abs_sub_comm (lowerSum4 f B N) (fullSum4 f B N)] at htri
  linarith

/-- The unrestricted F5 sum with reciprocal product weights. -/
def reciprocalFullSum5 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ fullPairs5 N, f (lowerLevel B N (q.1 * q.2)) / ((q.1 : ℝ) * q.2)

/-- Totient replacement is negligible for the actual unrestricted F5 sum.
CONDITIONAL ON IsLinearSieve only. -/
theorem fullSum5_totient_error (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → |fullSum5 f B N - reciprocalFullSum5 f B N| ≤ ε := by
  obtain ⟨M, hM, K, hK⟩ := lower_values_bounded F f h B hB
  intro ε hε
  obtain ⟨J, hJ⟩ := totient_sum_error_small (κ := kappa1)
    (by norm_num [kappa1]) hM ε hε
  refine ⟨max 2 (max K J), ?_⟩
  intro N hN
  exact hJ N (by omega) (lowerPrimeBand N) (lowerPrimeBand N)
    (lowerPrimeBand_range N) (lowerPrimeBand_range N) (fullPairs5 N)
    (fullPairs5_subset (by omega)) (fun _ hq => fullPairs5_primes hq)
    (fun q => f (lowerLevel B N (q.1 * q.2))) (by
      intro q hq
      obtain ⟨hd, hb⟩ := fullPairs5_product hq
      exact hK N (by omega) _ hd hb)

/-- Both elementary replacements leave the actual F5 prime sum unchanged in the limit.
CONDITIONAL ON IsLinearSieve only. -/
theorem lowerSum5_reciprocal_error (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → |lowerSum5 f B N - reciprocalFullSum5 f B N| ≤ ε := by
  intro ε hε
  obtain ⟨K, hK⟩ := lowerSum5_coprimality F f h B hB (ε / 2) (by positivity)
  obtain ⟨J, hJ⟩ := fullSum5_totient_error F f h B hB (ε / 2) (by positivity)
  refine ⟨max K J, ?_⟩
  intro N hN
  have hfirst := hK N (by omega)
  have hsecond := hJ N (by omega)
  have htri := abs_sub_le (lowerSum5 f B N) (fullSum5 f B N) (reciprocalFullSum5 f B N)
  rw [abs_sub_comm (lowerSum5 f B N) (fullSum5 f B N)] at htri
  linarith

/-- A reciprocal full sum limit supplies the actual F4 prime sum limit.
CONDITIONAL ON IsLinearSieve and the explicit reciprocal full sum limit. -/
theorem lowerSum4_of_reciprocal (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B)
    (hfull : Tendsto (reciprocalFullSum4 f B) evenAtTop (𝓝 (lowerIntegral4 f))) :
    Tendsto (lowerSum4 f B) evenAtTop (𝓝 (lowerIntegral4 f)) := by
  have hd : Tendsto (fun N => dist (reciprocalFullSum4 f B N) (lowerSum4 f B N))
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨K, hK⟩ := lowerSum4_reciprocal_error F f h B hB (ε / 2) (by positivity)
    refine ⟨K, ?_⟩
    intro N hN
    simpa only [Real.dist_eq, sub_zero, abs_abs, abs_sub_comm] using
      (hK N hN).trans_lt (by linarith : ε / 2 < ε)
  exact hfull.congr_dist (tendsto_inf_left hd)

/-- A reciprocal full sum limit supplies the actual F5 prime sum limit.
CONDITIONAL ON IsLinearSieve and the explicit reciprocal full sum limit. -/
theorem lowerSum5_of_reciprocal (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B)
    (hfull : Tendsto (reciprocalFullSum5 f B) evenAtTop (𝓝 (lowerIntegral5 f))) :
    Tendsto (lowerSum5 f B) evenAtTop (𝓝 (lowerIntegral5 f)) := by
  have hd : Tendsto (fun N => dist (reciprocalFullSum5 f B N) (lowerSum5 f B N))
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨K, hK⟩ := lowerSum5_reciprocal_error F f h B hB (ε / 2) (by positivity)
    refine ⟨K, ?_⟩
    intro N hN
    simpa only [Real.dist_eq, sub_zero, abs_abs, abs_sub_comm] using
      (hK N hN).trans_lt (by linarith : ε / 2 < ε)
  exact hfull.congr_dist (tendsto_inf_left hd)

end LeanLab.ChenDoubleSieve.Task348
