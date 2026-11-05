import LeanLab.ChenDoubleSieve.Decomp348g

/-!
Remove the coprimality condition from the actual finite sums in equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39.
The remaining unrestricted prime sum limits are not asserted here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve)

/-- The prime band containing both coordinates of the lower pair domains. -/
def lowerPrimeBand (N : ℕ) : Finset ℕ :=
  (range N).filter (fun p => p.Prime ∧ (N : ℝ) ^ kappa1 ≤ p)

/-- Upsilon four's ordered pair domain before imposing coprimality to N. -/
def fullPairs4 (N : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter (fun q => q.1.Prime ∧ q.2.Prime ∧
    (N : ℝ) ^ kappa1 ≤ q.1 ∧ q.1 < q.2 ∧ (q.2 : ℝ) < (N : ℝ) ^ kappa2)

/-- Upsilon five's crossing pair domain before imposing coprimality to N. -/
def fullPairs5 (N : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter (fun q => q.1.Prime ∧ q.2.Prime ∧
    (N : ℝ) ^ kappa1 ≤ q.1 ∧ (q.1 : ℝ) < (N : ℝ) ^ kappa2 ∧
    (N : ℝ) ^ kappa2 ≤ q.2 ∧
    (q.2 : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / q.1)

/-- The unrestricted finite prime sum for F4. -/
def fullSum4 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ fullPairs4 N, f (lowerLevel B N (q.1 * q.2)) /
    (Nat.totient (q.1 * q.2) : ℝ)

/-- The unrestricted finite prime sum for F5. -/
def fullSum5 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ fullPairs5 N, f (lowerLevel B N (q.1 * q.2)) /
    (Nat.totient (q.1 * q.2) : ℝ)

/-- The prime band satisfies the marginal range hypotheses. -/
theorem lowerPrimeBand_range (N : ℕ) : ∀ p ∈ lowerPrimeBand N,
    p.Prime ∧ (N : ℝ) ^ kappa1 ≤ p ∧ p ≤ N := by
  intro p hp
  obtain ⟨hpN, hp, hcut⟩ := mem_filter.mp hp
  exact ⟨hp, hcut, (mem_range.mp hpN).le⟩

/-- The sealed F4 domain is exactly the coprime restriction of its full domain. -/
theorem lowerPairs4_eq_filter (N : ℕ) : lowerPairs4 N =
    (fullPairs4 N).filter (fun q => q.1.Coprime N ∧ q.2.Coprime N) := by
  ext q
  simp only [lowerPairs4, fullPairs4, Wu08Sum.P2, mem_filter]
  tauto

/-- The sealed F5 domain is exactly the coprime restriction of its full domain. -/
theorem lowerPairs5_eq_filter (N : ℕ) : lowerPairs5 N =
    (fullPairs5 N).filter (fun q => q.1.Coprime N ∧ q.2.Coprime N) := by
  ext q
  simp only [lowerPairs5, fullPairs5, Wu08Sum.P2, mem_filter]
  tauto

/-- Every full F4 pair has distinct prime coordinates. -/
theorem fullPairs4_primes {N : ℕ} {q : ℕ × ℕ} (hq : q ∈ fullPairs4 N) :
    q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 := by
  obtain ⟨_, hp, hq, _, hlt, _⟩ := mem_filter.mp hq
  exact ⟨hp, hq, hlt.ne⟩

/-- Every full F5 pair has distinct prime coordinates. -/
theorem fullPairs5_primes {N : ℕ} {q : ℕ × ℕ} (hq : q ∈ fullPairs5 N) :
    q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 := by
  obtain ⟨_, hp, hq, _, hpup, hqlow, _⟩ := mem_filter.mp hq
  have hlt : (q.1 : ℝ) < q.2 := hpup.trans_le hqlow
  exact ⟨hp, hq, by exact_mod_cast hlt.ne⟩

/-- The full F4 domain lies in the product of the two prime bands. -/
theorem fullPairs4_subset (N : ℕ) : fullPairs4 N ⊆ lowerPrimeBand N ×ˢ lowerPrimeBand N := by
  intro q hq
  obtain ⟨hqN, hp, hq, hlow, hlt, _⟩ := mem_filter.mp hq
  obtain ⟨hpN, hqN⟩ := mem_product.mp hqN
  have hpq : (q.1 : ℝ) ≤ q.2 := by exact_mod_cast hlt.le
  apply mem_product.mpr
  exact ⟨mem_filter.mpr ⟨hpN, hp, hlow⟩, mem_filter.mpr ⟨hqN, hq, hlow.trans hpq⟩⟩

/-- The full F5 domain lies in the same prime band product for positive N. -/
theorem fullPairs5_subset {N : ℕ} (hN : 1 ≤ N) :
    fullPairs5 N ⊆ lowerPrimeBand N ×ˢ lowerPrimeBand N := by
  intro q hq
  obtain ⟨hqN, hp, hq, hlow, _, hqlow, _⟩ := mem_filter.mp hq
  obtain ⟨hpN, hqN⟩ := mem_product.mp hqN
  have hcut : (N : ℝ) ^ kappa1 ≤ (N : ℝ) ^ kappa2 :=
    rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num [kappa1, kappa2])
  apply mem_product.mpr
  exact ⟨mem_filter.mpr ⟨hpN, hp, hlow⟩, mem_filter.mpr ⟨hqN, hq, hcut.trans hqlow⟩⟩

/-- Full F4 divisors lie below N to one third. -/
theorem fullPairs4_product {N : ℕ} (hN : 2 ≤ N) {q : ℕ × ℕ}
    (hq : q ∈ fullPairs4 N) : 1 ≤ q.1 * q.2 ∧
      ((q.1 * q.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨_, hp, hq, _, hlt, hqbound⟩ := mem_filter.mp hq
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpq : (q.1 : ℝ) ≤ q.2 := by exact_mod_cast hlt.le
  have hpbound : (q.1 : ℝ) ≤ (N : ℝ) ^ kappa2 := hpq.trans hqbound.le
  refine ⟨Nat.mul_pos hp.pos hq.pos, ?_⟩
  push_cast
  calc
    (q.1 : ℝ) * q.2 ≤ (N : ℝ) ^ kappa2 * (N : ℝ) ^ kappa2 :=
      mul_le_mul hpbound hqbound.le (by positivity) (by positivity)
    _ = (N : ℝ) ^ (kappa2 + kappa2) := (rpow_add hpos _ _).symm
    _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
        (by norm_num [kappa2])

/-- Full F5 divisors have the same power bound by their moving boundary. -/
theorem fullPairs5_product {N : ℕ} {q : ℕ × ℕ} (hq : q ∈ fullPairs5 N) :
    1 ≤ q.1 * q.2 ∧ ((q.1 * q.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨_, hp, hq, _, _, _, hbound⟩ := mem_filter.mp hq
  have hp0 : (0 : ℝ) < q.1 := by exact_mod_cast hp.pos
  have he := (lt_div_iff₀ hp0).mp hbound
  norm_num [kappa1] at he
  refine ⟨Nat.mul_pos hp.pos hq.pos, ?_⟩
  push_cast
  nlinarith

/-- Coprimality removal is negligible for the actual finite F4 sum.
CONDITIONAL ON IsLinearSieve only. No prime sum limit is used. -/
theorem lowerSum4_coprimality (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → |fullSum4 f B N - lowerSum4 f B N| ≤ ε := by
  obtain ⟨M, hM, K, hK⟩ := lower_values_bounded F f h B hB
  intro ε hε
  obtain ⟨J, hJ⟩ := weighted_coprimality_error_small (κ := kappa1)
    (by norm_num [kappa1]) hM ε hε
  refine ⟨max 2 (max K J), ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have he := hJ N (by omega) (lowerPrimeBand N) (lowerPrimeBand N)
    (lowerPrimeBand_range N) (lowerPrimeBand_range N) (fullPairs4 N)
    (fullPairs4_subset N) (fun _ hq => fullPairs4_primes hq)
    (fun q => f (lowerLevel B N (q.1 * q.2))) (by
      intro q hq
      obtain ⟨hd, hb⟩ := fullPairs4_product hN2 hq
      exact hK N (by omega) _ hd hb)
  unfold fullSum4 lowerSum4
  rw [lowerPairs4_eq_filter]
  exact he

/-- Coprimality removal is negligible for the actual finite F5 sum.
CONDITIONAL ON IsLinearSieve only. No prime sum limit is used. -/
theorem lowerSum5_coprimality (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → |fullSum5 f B N - lowerSum5 f B N| ≤ ε := by
  obtain ⟨M, hM, K, hK⟩ := lower_values_bounded F f h B hB
  intro ε hε
  obtain ⟨J, hJ⟩ := weighted_coprimality_error_small (κ := kappa1)
    (by norm_num [kappa1]) hM ε hε
  refine ⟨max 2 (max K J), ?_⟩
  intro N hN
  have he := hJ N (by omega) (lowerPrimeBand N) (lowerPrimeBand N)
    (lowerPrimeBand_range N) (lowerPrimeBand_range N) (fullPairs5 N)
    (fullPairs5_subset (by omega)) (fun _ hq => fullPairs5_primes hq)
    (fun q => f (lowerLevel B N (q.1 * q.2))) (by
      intro q hq
      obtain ⟨hd, hb⟩ := fullPairs5_product hq
      exact hK N (by omega) _ hd hb)
  unfold fullSum5 lowerSum5
  rw [lowerPairs5_eq_filter]
  exact he

end LeanLab.ChenDoubleSieve.Task348
