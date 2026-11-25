import LeanLab.ChenDoubleSieve.Decomp349aSplitBasic

/-!
Remainder terms of Wu 2004 pages 38 to 41, arXiv 0705.1652.
`leaf_remainder_bv_proved` is `leaf_remainder_bv` of `Decomp349aSplitBasic`, proved from
the grouping m = p d of the double sum over p and d into one sum over the modulus q = p d,
each q met at most tau q times, and a cited divisor weighted Bombieri and Vinogradov LEAF.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF: Wu 2004 page 38 and display before 10.3, the remainder R of D estimated by
Wu Lemma 2.3, the mean value theorem of Pan and Ding in the form of Pan and Pan,
Corollary 8.12, with f 1 equal 1 and f m equal 0 for m at least 2. Wu weights q by
mu q squared times 3 to the nu q; here the weight is tau q over all q coprime to N, which
follows from plain Bombieri and Vinogradov by Cauchy Schwarz, the trivial bound N over q
and the bound on the sum of tau q squared over q. Wu's main term is li N over phi q; here
it is pi N over phi q, which costs the prime number theorem with error term. The lab form
`bvPrimeSequence` of Decomp363b is the unweighted li version, proved from `bvPi`.
Class MEDIUM. -/
theorem leaf_bv_weighted_pi :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ q ∈ (Finset.range ⌈(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌉₊).filter
          (fun q => q.Coprime N),
        (q.divisors.card : ℝ) *
          |(((primeSequence N).filter (fun a => q ∣ a)).card : ℝ) -
            (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)| ≤
        K * N / (log N) ^ 3 := by
  sorry

/-- The weighted remainder is at most eta times Theta N for large N, from
`leaf_bv_weighted_pi` and C_N at least the twin prime constant, Wu 2004 page 39. -/
theorem leaf_bv_divisor_weighted :
    ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∑ q ∈ (Finset.range ⌈(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌉₊).filter
          (fun q => q.Coprime N),
        (q.divisors.card : ℝ) *
          |(((primeSequence N).filter (fun a => q ∣ a)).card : ℝ) -
            (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)| ≤
        η * Θ N := by
  obtain ⟨B, hB, K, hK, N0, h⟩ := leaf_bv_weighted_pi
  refine ⟨B, hB, fun η hη => ?_⟩
  have hc : 0 < LeanLab.ChenExplicit.twinC := LeanLab.ChenExplicit.twinC_pos
  set M : ℝ := K / (η * LeanLab.ChenExplicit.twinC)
  refine ⟨max N0 (max 3 ⌈Real.exp M⌉₊), fun N _ hN => le_trans (h N (le_of_max_le_left hN)) ?_⟩
  have hN3 : (3 : ℝ) ≤ N := by
    have : 3 ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
    exact_mod_cast this
  have hNe : Real.exp M ≤ N := by
    have : ⌈Real.exp M⌉₊ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogM : M ≤ log N := by
    rw [← Real.log_exp M]
    exact Real.log_le_log (Real.exp_pos M) hNe
  have hlog1 : 1 < log N := by
    rw [← Real.log_exp 1]
    apply Real.log_lt_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  have hlogpos : 0 < log N := by linarith
  have hCN : LeanLab.ChenExplicit.twinC ≤ CN N := by
    unfold CN
    have := oddFactor_one_le N
    nlinarith
  have hKle : K ≤ η * LeanLab.ChenExplicit.twinC * log N := by
    have hpos : 0 < η * LeanLab.ChenExplicit.twinC := by positivity
    have : K = η * LeanLab.ChenExplicit.twinC * M := by
      simp only [M]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hlogM hpos.le
  unfold Θ
  rw [div_le_iff₀ (by positivity)]
  have e2 : η * (CN N * N / log N ^ 2) * log N ^ 3 = η * CN N * log N * N := by
    field_simp
  rw [e2]
  have : η * LeanLab.ChenExplicit.twinC * log N ≤ η * CN N * log N := by
    have := mul_le_mul_of_nonneg_left hCN hη.le
    exact mul_le_mul_of_nonneg_right this hlogpos.le
  nlinarith

/-- Grouping of Wu 2004 page 39: the double sum over primes p and squarefree d below
D over p with prime factors coprime to N is at most the sum over moduli q below D
coprime to N of tau q times the summand at q. -/
theorem remainder_group_le (N : ℕ) (D : ℝ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p ∧ p.Coprime N) (z : ℕ → ℝ) (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q) :
    ∑ p ∈ P, ∑ d ∈ (Finset.range ⌈D / p⌉₊).filter
        (fun d : ℕ => Squarefree d ∧ ∀ q ∈ d.primeFactors, ((q : ℕ) : ℝ) < z p ∧ Nat.Coprime q N),
      g (p * d) ≤
    ∑ q ∈ (Finset.range ⌈D⌉₊).filter (fun q => q.Coprime N), (q.divisors.card : ℝ) * g q := by
  set Q := (Finset.range ⌈D⌉₊).filter (fun q => q.Coprime N)
  set S : ℕ → Finset ℕ := fun p => (Finset.range ⌈D / p⌉₊).filter
        (fun d : ℕ => Squarefree d ∧ ∀ q ∈ d.primeFactors, ((q : ℕ) : ℝ) < z p ∧ Nat.Coprime q N)
  -- maps to
  have hmaps : ∀ p ∈ P, ∀ d ∈ S p, p * d ∈ Q := by
    intro p hp d hd
    obtain ⟨hp0, hpN⟩ := hP p hp
    simp only [S, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨hdD, hsq, hfac⟩ := hd
    have hd0 : d ≠ 0 := hsq.ne_zero
    have hdlt : (d : ℝ) < D / p := Nat.lt_ceil.mp hdD
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    have hpd : ((p * d : ℕ) : ℝ) < D := by
      push_cast
      have := (lt_div_iff₀ hpR).mp hdlt
      linarith
    simp only [Q, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_ceil.mpr hpd, Nat.coprime_mul_iff_left.mpr ⟨hpN, ?_⟩⟩
    apply Nat.coprime_of_dvd
    intro k hk hkd hkN
    have hkmem : k ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hk, hkd, hd0⟩
    have hc := (hfac k hkmem).2
    have : k ∣ Nat.gcd k N := Nat.dvd_gcd (dvd_refl k) hkN
    rw [hc] at this
    exact hk.one_lt.ne' (Nat.dvd_one.mp this)
  have hinner : ∀ p ∈ P, ∑ d ∈ S p, g (p * d) =
      ∑ q ∈ Q, ((((S p).filter (fun d => p * d = q)).card : ℕ) : ℝ) * g q := by
    intro p hp
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun d => p * d) (hmaps p hp)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => g q)]
    · rw [Finset.sum_const, nsmul_eq_mul]
    · intro d hd
      rw [(Finset.mem_filter.mp hd).2]
  have hcard : ∀ p ∈ P, ∀ q : ℕ,
      ((((S p).filter (fun d => p * d = q)).card : ℕ) : ℝ) ≤ if p ∈ q.divisors then 1 else 0 := by
    intro p hp q
    obtain ⟨hp0, -⟩ := hP p hp
    have hsub : (S p).filter (fun d => p * d = q) ⊆ {q / p} := by
      intro d hd
      rw [Finset.mem_singleton]
      have h := (Finset.mem_filter.mp hd).2
      rw [← h, Nat.mul_div_cancel_left d hp0]
    split_ifs with hdiv
    · have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      exact_mod_cast this
    · have hempty : (S p).filter (fun d => p * d = q) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro d hd
        apply hdiv
        obtain ⟨hd1, h⟩ := Finset.mem_filter.mp hd
        simp only [S, Finset.mem_filter] at hd1
        have hd0 : d ≠ 0 := hd1.2.1.ne_zero
        rw [Nat.mem_divisors]
        refine ⟨⟨d, h.symm⟩, ?_⟩
        rw [← h]
        exact Nat.mul_ne_zero hp0.ne' hd0
      rw [hempty]
      simp
  calc ∑ p ∈ P, ∑ d ∈ S p, g (p * d)
      = ∑ p ∈ P, ∑ q ∈ Q, ((((S p).filter (fun d => p * d = q)).card : ℕ) : ℝ) * g q :=
        Finset.sum_congr rfl hinner
    _ = ∑ q ∈ Q, ∑ p ∈ P, ((((S p).filter (fun d => p * d = q)).card : ℕ) : ℝ) * g q :=
        Finset.sum_comm
    _ ≤ ∑ q ∈ Q, (q.divisors.card : ℝ) * g q := by
      refine Finset.sum_le_sum (fun q _ => ?_)
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (hg q)
      calc ∑ p ∈ P, ((((S p).filter (fun d => p * d = q)).card : ℕ) : ℝ)
          ≤ ∑ p ∈ P, (if p ∈ q.divisors then (1 : ℝ) else 0) :=
            Finset.sum_le_sum (fun p hp => hcard p hp q)
        _ = ((P.filter (fun p => p ∈ q.divisors)).card : ℝ) := by
            rw [Finset.sum_boole]
        _ ≤ (q.divisors.card : ℝ) := by
            exact_mod_cast Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)

/-- `leaf_remainder_bv` of `Decomp349aSplitBasic`, statement identical, proved from the
grouping `remainder_group_le` and the cited LEAF `leaf_bv_divisor_weighted`.
CONDITIONAL ON that LEAF. -/
theorem leaf_remainder_bv_proved :
    ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
          sieveRemainder N p (basicSifting N p i)
            (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) ≤ η * Θ N := by
  obtain ⟨B, hB, h⟩ := leaf_bv_divisor_weighted
  refine ⟨B, hB, fun η hη => ?_⟩
  obtain ⟨N0, hN0⟩ := h η hη
  refine ⟨N0, fun N hE hN i _ => le_trans ?_ (hN0 N hE hN)⟩
  unfold sieveRemainder
  refine remainder_group_le N ((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) _ ?_
    (fun p => basicSifting N p i)
    (fun q => |(((primeSequence N).filter (fun a => q ∣ a)).card : ℝ) -
      (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|)
    (fun q => abs_nonneg _)
  intro p hp
  simp only [Wu41.PS, Finset.mem_filter] at hp
  exact ⟨hp.2.1.pos, hp.2.2.2.2⟩


end LeanLab.ChenDoubleSieve.Task349
