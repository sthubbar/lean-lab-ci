import LeanLab.ChenDoubleSieve.Decomp366e
import LeanLab.ChenDoubleSieve.Decomp363b
import LeanLab.ChenDoubleSieve.Decomp367k

/-!
Regroup the F4 pair discrepancy into the existing single modulus input.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
The finite comparison is elementary. The single mean value theorem remains OPEN.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348

/-- The residual squarefree discrepancy moduli after fixing a prime pair.
The full progression modulus is the product of the pair and this modulus. -/
def pairModuli4 (B : ℝ) (N : ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Task363.sieveLevel B N / (p.1 * p.2 : ℕ)⌋₊).filter
    (fun q => Squarefree q ∧ q.Coprime (N * (p.1 * p.2)))

/-- The absolute progression discrepancy summed over the actual F4 domain.
This contains neither a sieve function nor a sifted count. -/
def rawRemainder4 (B : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ lowerPairs4 N, ∑ q ∈ pairModuli4 B N p,
    |(#((primeSequence N).filter (fun a => p.1 * p.2 * q ∣ a)) : ℝ) -
      Wu04.li N / (Nat.totient (p.1 * p.2 * q) : ℝ)|

/-- Candidate actual F4 pairs whose two prime coordinates divide one fixed modulus. -/
def candidatePairs4 (N d : ℕ) : Finset (ℕ × ℕ) :=
  (lowerPairs4 N).filter (fun p => p.1 ∣ d ∧ p.2 ∣ d)

/-- At most 144 actual F4 pairs can contribute to a fixed positive modulus at most N. -/
theorem candidatePairs4_card {N d : ℕ} (hN : 2 ≤ N) (hd : 0 < d) (hdN : d ≤ N) :
    (candidatePairs4 N d).card ≤ 144 := by
  have hfull : ∀ p ∈ lowerPairs4 N, p ∈ fullPairs4 N := by
    intro p hp
    rw [lowerPairs4_eq_filter] at hp
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
    have hsub : candidatePairs4 N d ⊆ P ×ˢ P := by
      intro p hp
      obtain ⟨hp, hpd, hqd⟩ := mem_filter.mp hp
      have hpfull := hfull p hp
      obtain ⟨hp1, hp2, _⟩ := fullPairs4_primes hpfull
      obtain ⟨hpband, hqband⟩ := mem_product.mp (fullPairs4_subset N hpfull)
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
    have he : candidatePairs4 N 1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro p hp
      obtain ⟨hp, hpd, _⟩ := mem_filter.mp hp
      have hprime := (fullPairs4_primes (hfull p hp)).1
      exact hprime.ne_one (Nat.dvd_one.mp hpd)
    rw [he]
    norm_num

/-- Each residual pair modulus gives a squarefree coprime full progression modulus
at the original finite sieve level. -/
theorem pairModuli4_product_mem {B : ℝ} {N : ℕ} {p : ℕ × ℕ} {q : ℕ}
    (hN : 2 ≤ N) (hp : p ∈ lowerPairs4 N) (hq : q ∈ pairModuli4 B N p) :
    p.1 * p.2 * q ∈ Task363.remainderModuli B N := by
  rw [lowerPairs4_eq_filter] at hp
  obtain ⟨hpfull, hpN, hp2N⟩ := mem_filter.mp hp
  obtain ⟨hp1, hp2, hne⟩ := fullPairs4_primes hpfull
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
theorem pair_mem_candidatePairs4 {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ lowerPairs4 N) (q : ℕ) :
    p ∈ candidatePairs4 N (p.1 * p.2 * q) := by
  apply mem_filter.mpr
  refine ⟨hp, ?_, ?_⟩
  · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

/-- Actual pairs together with their residual discrepancy moduli. -/
def pairTriples4 (B : ℝ) (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  (lowerPairs4 N).sigma (pairModuli4 B N)

/-- The full progression modulus attached to an actual pair and residual modulus. -/
def tripleModulus4 (t : Σ _ : ℕ × ℕ, ℕ) : ℕ := t.1.1 * t.1.2 * t.2

/-- Each triple maps into the original single modulus discrepancy domain. -/
theorem tripleModulus4_mem {B : ℝ} {N : ℕ} (hN : 2 ≤ N)
    {t : Σ _ : ℕ × ℕ, ℕ} (ht : t ∈ pairTriples4 B N) :
    tripleModulus4 t ∈ Task363.remainderModuli B N := by
  obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp ht
  exact pairModuli4_product_mem hN hp hq

/-- A full modulus has at most 144 preimages among the actual discrepancy triples. -/
theorem tripleModulus4_fiber_card {B : ℝ} {N d : ℕ} (hN : 2 ≤ N)
    (hd : 0 < d) (hdN : d ≤ N) :
    ((pairTriples4 B N).filter (fun t => tripleModulus4 t = d)).card ≤ 144 := by
  apply le_trans _ (candidatePairs4_card hN hd hdN)
  apply card_le_card_of_injOn (fun t : Σ _ : ℕ × ℕ, ℕ => t.1)
  · intro t ht
    obtain ⟨htT, htd⟩ := mem_filter.mp ht
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp htT
    rw [← htd]
    exact pair_mem_candidatePairs4 hp t.2
  · intro t ht u hu heq
    obtain ⟨htT, htd⟩ := mem_filter.mp ht
    obtain ⟨huT, hud⟩ := mem_filter.mp hu
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp htT
    rcases t with ⟨p, q⟩
    rcases u with ⟨r, s⟩
    dsimp only at heq
    subst r
    have hpfull : p ∈ fullPairs4 N := by
      rw [lowerPairs4_eq_filter] at hp
      exact (mem_filter.mp hp).1
    have hpos : 0 < p.1 * p.2 := (fullPairs4_product hN hpfull).1
    have he : p.1 * p.2 * q = p.1 * p.2 * s := htd.trans hud.symm
    have hqs : q = s := Nat.eq_of_mul_eq_mul_left hpos he
    subst s
    rfl

/-- The absolute pair discrepancy is bounded by 144 times the single modulus discrepancy.
Only the explicit finite level bound is needed beyond N at least two. -/
theorem rawRemainder4_le_single {B : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hQ : Task363.sieveLevel B N ≤ N) :
    rawRemainder4 B N ≤ 144 * Task363.rawRemainder B N := by
  let T := pairTriples4 B N
  let S := Task363.remainderModuli B N
  let g : ℕ → ℝ := fun d =>
    |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) - Wu04.li N / (d.totient : ℝ)|
  have hmap : ∀ t ∈ T, tripleModulus4 t ∈ S := fun _ ht => tripleModulus4_mem hN ht
  have he : rawRemainder4 B N = ∑ t ∈ T, g (tripleModulus4 t) := by
    simp only [T, pairTriples4, Finset.sum_sigma, g, tripleModulus4, rawRemainder4]
  rw [he]
  have hgroup := Finset.sum_fiberwise_of_maps_to hmap (fun t => g (tripleModulus4 t))
  rw [← hgroup]
  calc
    _ ≤ ∑ d ∈ S, (144 : ℝ) * g d := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hdI, _⟩ := mem_filter.mp hd
      obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.mp hdI
      have hdN : d ≤ N := by
        have he := (Nat.le_floor_iff' (by omega : d ≠ 0)).1 hdQ
        exact_mod_cast he.trans hQ
      have hc := tripleModulus4_fiber_card (B := B) hN hd1 hdN
      have hcR : (((T.filter (fun t => tripleModulus4 t = d)).card : ℕ) : ℝ) ≤ 144 := by
        exact_mod_cast hc
      calc
        _ = ∑ _t ∈ T.filter (fun t => tripleModulus4 t = d), g d := by
          apply sum_congr rfl
          intro t ht
          rw [(mem_filter.mp ht).2]
        _ = ((T.filter (fun t => tripleModulus4 t = d)).card : ℝ) * g d := by simp
        _ ≤ 144 * g d := mul_le_mul_of_nonneg_right hcR (abs_nonneg _)
    _ = 144 * Task363.rawRemainder B N := by
      simp only [S, Task363.rawRemainder, g, mul_sum]

/-- The existing single modulus mean value estimate implies the pair estimate.
CONDITIONAL ON the explicitly displayed single modulus analytic input. -/
theorem pair_remainder_of_single
    (hsingle : ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        Task363.rawRemainder B N ≤ D * (N : ℝ) / log N ^ 3) :
    ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        rawRemainder4 B N ≤ D * (N : ℝ) / log N ^ 3 := by
  obtain ⟨B, hB, D, hD, M, hM⟩ := hsingle
  have hl : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hl.eventually_ge_atTop 1)
  refine ⟨B, hB, 144 * D, by positivity, max 2 (max M J), ?_⟩
  intro N hEven hN
  calc
    _ ≤ 144 * Task363.rawRemainder B N :=
      rawRemainder4_le_single (by omega) (Task367.sieveLevel_le_self (by omega) (hJ N (by omega)) hB.le)
    _ ≤ 144 * (D * (N : ℝ) / log N ^ 3) := by gcongr; exact hM N hEven (by omega)
    _ = (144 * D) * (N : ℝ) / log N ^ 3 := by ring

end LeanLab.ChenDoubleSieve.Task366
