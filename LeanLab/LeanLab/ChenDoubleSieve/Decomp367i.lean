import LeanLab.ChenDoubleSieve.Decomp367f

/-!
Finite modulus bookkeeping for the pair mean value estimate.
Source: https://arxiv.org/pdf/0705.1652, page 39 error display and equation 10.5.
The analytic mean value estimate remains OPEN.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348

/-- Candidate actual F5 pairs whose two prime coordinates divide one fixed modulus. -/
def candidatePairs5 (N d : ℕ) : Finset (ℕ × ℕ) :=
  (lowerPairs5 N).filter (fun p => p.1 ∣ d ∧ p.2 ∣ d)

/-- At most 144 actual F5 pairs can contribute to a fixed positive modulus at most N. -/
theorem candidatePairs5_card {N d : ℕ} (hN : 2 ≤ N) (hd : 0 < d) (hdN : d ≤ N) :
    (candidatePairs5 N d).card ≤ 144 := by
  have hfull : ∀ p ∈ lowerPairs5 N, p ∈ fullPairs5 N := by
    intro p hp
    rw [lowerPairs5_eq_filter] at hp
    exact (mem_filter.mp hp).1
  by_cases hd2 : 2 ≤ d
  · let P : Finset ℕ := d.primeFactors.filter (fun p : ℕ => (N : ℝ) ^ kappa1 ≤ (p : ℝ))
    have hc : (P.card : ℝ) ≤ 12 := by
      have he := large_prime_divisor_card hd2 P (filter_subset _ _)
        (show 0 < kappa1 by norm_num [kappa1]) (by
          intro p hp
          have hlo := (mem_filter.mp hp).2
          exact (rpow_le_rpow (Nat.cast_nonneg d) (by exact_mod_cast hdN)
            (by norm_num [kappa1])).trans hlo)
      norm_num [kappa1] at he
      exact_mod_cast he
    have hcN : P.card ≤ 12 := by exact_mod_cast hc
    have hsub : candidatePairs5 N d ⊆ P ×ˢ P := by
      intro p hp
      obtain ⟨hp, hpd, hqd⟩ := mem_filter.mp hp
      have hpfull := hfull p hp
      obtain ⟨hp1, hp2, _⟩ := fullPairs5_primes hpfull
      obtain ⟨hpband, hqband⟩ := mem_product.mp (fullPairs5_subset (by omega) hpfull)
      exact mem_product.mpr
        ⟨mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp1, hpd, hd.ne'⟩,
          (lowerPrimeBand_range N _ hpband).2.1⟩,
         mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp2, hqd, hd.ne'⟩,
          (lowerPrimeBand_range N _ hqband).2.1⟩⟩
    have he := Finset.card_le_card hsub
    rw [card_product] at he
    nlinarith
  · have hd1 : d = 1 := by omega
    subst d
    have he : candidatePairs5 N 1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro p hp
      obtain ⟨hp, hpd, _⟩ := mem_filter.mp hp
      have hprime := (fullPairs5_primes (hfull p hp)).1
      exact hprime.ne_one (Nat.dvd_one.mp hpd)
    rw [he]
    norm_num

/-- Each residual pair modulus gives a squarefree coprime full progression modulus
at the original finite sieve level. -/
theorem pairModuli5_product_mem {B : ℝ} {N : ℕ} {p : ℕ × ℕ} {q : ℕ}
    (hN : 2 ≤ N) (hp : p ∈ lowerPairs5 N) (hq : q ∈ pairModuli5 B N p) :
    p.1 * p.2 * q ∈ Task363.remainderModuli B N := by
  rw [lowerPairs5_eq_filter] at hp
  obtain ⟨hpfull, hpN, hp2N⟩ := mem_filter.mp hp
  obtain ⟨hp1, hp2, hne⟩ := fullPairs5_primes hpfull
  obtain ⟨hqI, hsq, hcop⟩ := mem_filter.mp hq
  obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hqI
  have hprod : 0 < p.1 * p.2 := Nat.mul_pos hp1.pos hp2.pos
  have hprodR : (0 : ℝ) < (p.1 * p.2 : ℕ) := by exact_mod_cast hprod
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hQpos : 0 < Task363.sieveLevel B N := by unfold Task363.sieveLevel; positivity
  have hqR : (q : ℝ) ≤ Task363.sieveLevel B N / (p.1 * p.2 : ℕ) :=
    (Nat.le_floor_iff (div_pos hQpos hprodR).le).1 hqQ
  have hbound : ((p.1 * p.2 * q : ℕ) : ℝ) ≤ Task363.sieveLevel B N := by
    have he := (le_div_iff₀ hprodR).1 hqR
    push_cast at he ⊢
    nlinarith
  have hq12 : q.Coprime (p.1 * p.2) := hcop.coprime_dvd_right (dvd_mul_left _ _)
  have hqN : q.Coprime N := hcop.coprime_dvd_right (dvd_mul_right _ _)
  apply mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hprod hq1, Nat.le_floor hbound⟩, ?_, ?_⟩
  · exact (Nat.squarefree_mul hq12.symm).2
      ⟨(Nat.squarefree_mul ((Nat.coprime_primes hp1 hp2).2 hne)).2
        ⟨hp1.squarefree, hp2.squarefree⟩, hsq⟩
  · exact Nat.coprime_mul_iff_left.2 ⟨Nat.coprime_mul_iff_left.2 ⟨hpN, hp2N⟩, hqN⟩

/-- Every actual summand pair is a candidate for its full progression modulus. -/
theorem pair_mem_candidatePairs5 {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ lowerPairs5 N) (q : ℕ) :
    p ∈ candidatePairs5 N (p.1 * p.2 * q) := by
  apply mem_filter.mpr
  refine ⟨hp, ?_, ?_⟩
  · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

/-- The actual nonempty F5 pair also has a nonempty residual modulus domain. -/
theorem pairModuli5_actual_instance : 1 ∈ pairModuli5 1 262144 (3, 11) := by
  apply one_mem_pairModuli5
  have hlog : 0 < log (262144 : ℝ) := log_pos (by norm_num)
  have he : log (262144 : ℝ) = 18 * log 2 := by
    have h := log_pow (2 : ℝ) 18
    norm_num at h
    exact h
  have hb : log (262144 : ℝ) < 13 := by
    rw [he]
    linarith [log_two_lt_d9]
  unfold Task363.sieveLevel
  norm_num
  rw [one_le_div (by positivity), le_div_iff₀ hlog]
  linarith

end LeanLab.ChenDoubleSieve.Task367
