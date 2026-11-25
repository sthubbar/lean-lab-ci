import LeanLab.ChenDoubleSieve.Decomp349bSplitFinite

/-!
Split of the LEAF `leaf_switching` of Decomp349bSplitFinite, Wu 2004 page 40, Chen's
switching principle before 10.6. Source: https://arxiv.org/pdf/0705.1652.
For each switched pair an element N minus p' of A_{pq} sifted at z is p q m with m prime,
because m is below z squared, unless it is one of three exceptional kinds; the
exceptional count over all pairs is one new LEAF.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- Wu 2004 page 40, Chen's switching for one pair: an element a of A_{pq} sifted at z
by the primes not dividing N p is p q m with m prime, unless a equals p q, p squared q
divides a, or a has a factor in common with N; here N is below p q z squared. -/
theorem sw_pair_le (N p q : ℕ) (z : ℝ) (hp : p.Prime) (hq : q.Prime)
    (hz : (N : ℝ) < p * q * z ^ 2) (hz0 : 0 ≤ z) :
    (Wu41.S (primeSequence N) (p * q) (N * p) z : ℝ) ≤
      (((Finset.range (N + 1)).filter
        (fun m => m.Prime ∧ p * q * m ≤ N ∧ (N - p * q * m).Prime)).card : ℝ) +
      (((primeSequence N).filter (fun a => p * q ∣ a ∧
        (a = p * q ∨ p * (p * q) ∣ a ∨ ¬ Nat.Coprime a N))).card : ℝ) := by
  set A := primeSequence N
  set E := A.filter (fun a => p * q ∣ a ∧ (a = p * q ∨ p * (p * q) ∣ a ∨ ¬ Nat.Coprime a N))
  set G := A.filter (fun a => p * q ∣ a ∧ Wu41.Sifted (N * p) z a)
  set M := (Finset.range (N + 1)).filter
    (fun m => m.Prime ∧ p * q * m ≤ N ∧ (N - p * q * m).Prime)
  have hpq0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hS : Wu41.S A (p * q) (N * p) z = G.card := rfl
  have hsplit : G ⊆ G.filter (fun a => a ∉ E) ∪ E := by
    intro a ha
    by_cases h : a ∈ E
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, h⟩)
  have hmaps : ∀ a ∈ G.filter (fun a => a ∉ E), a / (p * q) ∈ M := by
    intro a ha
    obtain ⟨hG, hnE⟩ := Finset.mem_filter.mp ha
    obtain ⟨hA, hdvd, hsift⟩ := Finset.mem_filter.mp hG
    obtain ⟨p', hp'mem, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hp'r, hp'⟩ := Finset.mem_filter.mp hp'mem
    have hp'N : p' ≤ N := by have := Finset.mem_range.mp hp'r; omega
    have hnot : ¬ (N - p' = p * q ∨ p * (p * q) ∣ N - p' ∨ ¬ Nat.Coprime (N - p') N) := by
      intro h; exact hnE (Finset.mem_filter.mpr ⟨hA, hdvd, h⟩)
    push Not at hnot
    obtain ⟨hne, hnp, hcop⟩ := hnot
    obtain ⟨m, hm⟩ := hdvd
    have hmdiv : (N - p') / (p * q) = m := by rw [hm]; exact Nat.mul_div_cancel_left m hpq0
    rw [hmdiv]
    have hm0 : m ≠ 0 := by
      rintro rfl
      have h0 : N - p' = 0 := by simpa using hm
      rw [h0, Nat.coprime_zero_left] at hcop
      have := hp'.two_le
      omega
    have hm1 : m ≠ 1 := by rintro rfl; exact hne (by rw [hm, mul_one])
    have hmprime : m.Prime := by
      by_contra hmp
      have hm2 : 2 ≤ m := by omega
      set r := m.minFac
      have hr : r.Prime := Nat.minFac_prime (by omega)
      have hrm : r ∣ m := Nat.minFac_dvd m
      have hra : r ∣ N - p' := hm ▸ dvd_mul_of_dvd_right hrm _
      by_cases hrz : (r : ℝ) < z
      · by_cases hrD : r ∣ N * p
        · rcases (Nat.Prime.dvd_mul hr).mp hrD with hrN | hrp
          · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨r, hr, hra, hrN⟩ hcop
          · have hrp' : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
            apply hnp
            rw [hrp'] at hrm
            obtain ⟨k, hk⟩ := hrm
            rw [hm, hk]
            exact ⟨k, by ring⟩
        · exact hsift r hr hrz hrD hra
      · push Not at hrz
        have hsq : r ^ 2 ≤ m := by
          have := Nat.minFac_sq_le_self (by omega : 0 < m) hmp
          simpa [pow_two] using this
        have hle : p * q * m ≤ N := by rw [← hm]; omega
        have hmR : (r : ℝ) ^ 2 ≤ m := by exact_mod_cast hsq
        have hzr : z ^ 2 ≤ (r : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hrz 2
        have hleR : (p : ℝ) * q * m ≤ N := by exact_mod_cast hle
        have hpqR : (0 : ℝ) < p * q := by exact_mod_cast hpq0
        nlinarith
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hmprime, ?_, ?_⟩
    · have : m ≤ p * q * m := Nat.le_mul_of_pos_left m hpq0
      omega
    · rw [← hm]; omega
    · rw [← hm]
      have : N - (N - p') = p' := by omega
      rw [this]; exact hp'
  have hinj : Set.InjOn (fun a => a / (p * q)) (G.filter (fun a => a ∉ E) : Set ℕ) := by
    intro a ha b hb hab
    have hda := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2.1
    have hdb := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.1
    simp only at hab
    rw [← Nat.div_mul_cancel hda, ← Nat.div_mul_cancel hdb, hab]
  have hcard1 : (G.filter (fun a => a ∉ E)).card ≤ M.card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hcard := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  rw [hS]
  exact_mod_cast (by omega : G.card ≤ M.card + E.card)

/-- LEAF: Wu 2004 page 40, the exceptions in Chen's switching principle before 10.6:
over the switched pairs, the elements N minus p' of A_{pq} equal to p q, divisible by
p squared q, or sharing a prime with N number o of Theta N. The first and last kinds
are at most a few per pair and there are at most N to 5/6 pairs; the middle kind is
at most N over p squared q per pair. Class MEDIUM. -/
theorem leaf_switch_exceptions :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        ∑ q ∈ switchedPairs N i, (((primeSequence N).filter (fun a => q.1 * q.2 ∣ a ∧
          (a = q.1 * q.2 ∨ q.1 * (q.1 * q.2) ∣ a ∨ ¬ Nat.Coprime a N))).card : ℝ) ≤
          η * Θ N := by
  sorry

/-- Wu 2004 page 40: membership in the switched pairs gives prime coordinates and the
defining bounds. -/
theorem sw_mem {N : ℕ} {i : Fin 12} {q : ℕ × ℕ} (hq : q ∈ switchedPairs N i) :
    q.1.Prime ∧ q.2.Prime ∧
      (if i = 6 then (N : ℝ) ^ sigma1 ≤ q.1 else
        if i = 7 then (N : ℝ) ^ sigma2 ≤ q.1 else
          (N : ℝ) ^ kappa2 ≤ q.1 ∧ (q.1 : ℝ) < (N : ℝ) ^ sigma2 ∧
            (N : ℝ) ^ sigma2 ≤ q.2) ∧ q.1 < q.2 := by
  simp only [switchedPairs, Wu08Sum.P2, Finset.mem_filter] at hq
  exact ⟨hq.2.1, hq.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2.1⟩

/-- Wu 2004 page 40, the size condition of the switching: N is below p q z squared, with
z equal q for coordinates six and seven, from p q cubed above N. -/
theorem sw_size_q {N p q : ℕ} {σ : ℝ} (hN : 1 ≤ N) (hσ : 1 / 4 ≤ σ)
    (hp : (N : ℝ) ^ σ ≤ p) (hpq : p < q) : (N : ℝ) < p * q * (q : ℝ) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : (N : ℝ) ≤ ((N : ℝ) ^ σ) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (σ * ((4 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hp0 : (0 : ℝ) ≤ (N : ℝ) ^ σ := by positivity
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  have hp4 : ((N : ℝ) ^ σ) ^ 4 ≤ (p : ℝ) ^ 4 := pow_le_pow_left₀ hp0 hp 4
  have hpp : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp
  have : (p : ℝ) ^ 4 < p * q * q ^ 2 := by
    have h1 : (p : ℝ) ^ 3 < (q : ℝ) ^ 3 := pow_lt_pow_left₀ hpq' hpp.le (by norm_num)
    nlinarith
  linarith

/-- Wu 2004 page 40, the size condition for coordinate nine: p q times N to two sigma one
is above N since kappa2 plus sigma2 plus 2 sigma1 exceeds 1. -/
theorem sw_size_nine {N p q : ℕ} (hN : 2 ≤ N) (hp : (N : ℝ) ^ kappa2 ≤ p)
    (hq : (N : ℝ) ^ sigma2 ≤ q) : (N : ℝ) < p * q * ((N : ℝ) ^ sigma1) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hprod : (N : ℝ) ^ kappa2 * (N : ℝ) ^ sigma2 * ((N : ℝ) ^ sigma1) ^ 2 =
      (N : ℝ) ^ (kappa2 + sigma2 + 2 * sigma1) := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    push_cast; ring_nf
  have hlt : (N : ℝ) < (N : ℝ) ^ (kappa2 + sigma2 + 2 * sigma1) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num [kappa2, sigma2, sigma1])
  have h1 : (N : ℝ) ^ kappa2 * (N : ℝ) ^ sigma2 ≤ p * q :=
    mul_le_mul hp hq (by positivity) (le_trans (by positivity) hp)
  have h2 : (N : ℝ) ^ kappa2 * (N : ℝ) ^ sigma2 * ((N : ℝ) ^ sigma1) ^ 2 ≤
      p * q * ((N : ℝ) ^ sigma1) ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith

/-- `leaf_switching`, exactly as stated in Decomp349bSplitFinite, Wu 2004 page 40:
Chen's switching principle, proved from `sw_pair_le` for each pair and the
exceptional count LEAF `leaf_switch_exceptions`. CONDITIONAL ON that LEAF. -/
theorem leaf_switching_proved :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        sieveTerms N i ≤ switchedCount N i + η * Θ N := by
  intro η hη
  obtain ⟨N0, hN0⟩ := leaf_switch_exceptions η hη
  refine ⟨max N0 2, fun N hEven hN i hi => ?_⟩
  have hE := hN0 N hEven (le_of_max_le_left hN) i hi
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  refine le_trans ?_ (add_le_add (le_refl (switchedCount N i)) hE)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · show ((∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ sigma1 ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
        Wu41.S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℕ) : ℝ) ≤ _
    have hset : Wu08Sum.P2 N (fun p q => (N : ℝ) ^ sigma1 ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)) = switchedPairs N 6 := by
      simp [switchedPairs]
    push_cast
    rw [hset, switchedCount, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hp, hq', hc, hpq⟩ := sw_mem hq
    simp only [↓reduceIte] at hc
    exact sw_pair_le N q.1 q.2 q.2 hp hq'
      (sw_size_q (by omega) (by norm_num [sigma1]) hc hpq) (by positivity)
  · show ((∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ sigma2 ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
        Wu41.S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 : ℕ) : ℝ) ≤ _
    have hset : Wu08Sum.P2 N (fun p q => (N : ℝ) ^ sigma2 ≤ p ∧ p < q ∧
        (q : ℝ) < Real.sqrt ((N : ℝ) / p)) = switchedPairs N 7 := by
      simp [switchedPairs]
    push_cast
    rw [hset, switchedCount, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hp, hq', hc, hpq⟩ := sw_mem hq
    simp only [show (7 : Fin 12) ≠ 6 by decide, ↓reduceIte] at hc
    exact sw_pair_le N q.1 q.2 q.2 hp hq'
      (sw_size_q (by omega) (by norm_num [sigma2]) hc hpq) (by positivity)
  · show ((∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
        (N : ℝ) ^ sigma2 ≤ q ∧ (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
        Wu41.S (primeSequence N) (q.1 * q.2) (N * q.1) ((N : ℝ) ^ sigma1) : ℕ) : ℝ) ≤ _
    have hset : Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
        (N : ℝ) ^ sigma2 ≤ q ∧ (q : ℝ) < Real.sqrt ((N : ℝ) / p)) = switchedPairs N 9 := by
      simp only [switchedPairs, Wu08Sum.P2, show (9 : Fin 12) ≠ 6 by decide,
        show (9 : Fin 12) ≠ 7 by decide, ↓reduceIte]
      apply Finset.filter_congr
      intro x _
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
        refine ⟨h1, h2, h3, h4, ⟨h5, h6, h7⟩, ?_, h8⟩
        exact_mod_cast h6.trans_le h7
      · rintro ⟨h1, h2, h3, h4, ⟨h5, h6, h7⟩, _, h8⟩
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    push_cast
    rw [hset, switchedCount, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hp, hq', hc, hpq⟩ := sw_mem hq
    simp only [show (9 : Fin 12) ≠ 6 by decide, show (9 : Fin 12) ≠ 7 by decide,
      ↓reduceIte] at hc
    exact sw_pair_le N q.1 q.2 _ hp hq' (sw_size_nine hN2 hc.1 hc.2.2) (by positivity)

end LeanLab.ChenDoubleSieve.Task349

