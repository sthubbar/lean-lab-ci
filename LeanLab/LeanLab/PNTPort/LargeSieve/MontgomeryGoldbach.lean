import LeanLab.PNTPort.LargeSieve.MontgomeryTau

/-!
# An explicit upper bound for the Goldbach count from Montgomery's sieve

Lab proof, unit U-5554, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics, the
upper bound sieve for `r(N) = #{p ≤ N : p, N - p prime}`; the order `N/log² N` is Brun 1920.
No cited input. Binary Goldbach is OPEN; this is an upper bound for the number of
representations, not a lower bound.

* `goldbach_upper_montgomery`: for even `N ≥ 4` and `Q ≥ 3`,
  `r(N) ≤ 2Q + (N + 2Q²) (N/φ(N))² / (log²(Q + 1)/2 - 3/4)`.
  With `Q` near `√N / log N` this is `r(N) ≤ (8 + o(1)) (N/φ(N))² N / log² N`.

The sieve: modulo a prime `ℓ ≤ Q`, a prime `p > Q` with `N - p > Q` prime misses the classes
`0` and `N mod ℓ`. The sieve sum is bounded below through the weight
`c(ℓ) = (2ℓ - 1)/(ℓ - 1)² ≤ 2/(ℓ - 2)` and `∑_{n ≤ Q} τ(n)/n`, after removing the primes of `N`
at the cost `(N/φ(N))²`.
-/

namespace LeanLab.PNTPort.LargeSieve

open Finset Real

lemma cW_le_two_div {ℓ : ℕ} (hℓ : 3 ≤ ℓ) : cW ℓ ≤ 2 / ((ℓ : ℝ) - 2) := by
  have h3 : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  unfold cW
  rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith

/-- **Upper bound for the Goldbach count, explicit, from Montgomery's sieve.** -/
theorem goldbach_upper_montgomery (N Q : ℕ) (hN : Even N) (hN4 : 4 ≤ N) (hQ : 3 ≤ Q) :
    ((((range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)).card : ℕ) : ℝ) ≤
      2 * Q + (N + 2 * (Q : ℝ) ^ 2) * ((N : ℝ) / N.totient) ^ 2 /
        (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)
  set Pbig := P.filter (fun p => Q < p ∧ Q < N - p)
  set Psmall := P.filter (fun p => ¬ (Q < p ∧ Q < N - p))
  have hsplit : P.card = Pbig.card + Psmall.card := (card_filter_add_card_filter_not _).symm
  have hsmall : (Psmall.card : ℝ) ≤ 2 * Q := by
    have hsub : Psmall ⊆ (Icc 1 Q) ∪ (Icc 1 Q).image (fun m => N - m) := by
      intro p hp
      simp only [Psmall, P, mem_filter, mem_range, not_and_or, not_lt] at hp
      obtain ⟨⟨hpN, hpp, hqp⟩, h⟩ := hp
      rw [mem_union]
      rcases h with h | h
      · exact Or.inl (mem_Icc.2 ⟨hpp.one_lt.le, h⟩)
      · refine Or.inr (mem_image.2 ⟨N - p, mem_Icc.2 ⟨hqp.one_lt.le, h⟩, by omega⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    have h2 := card_image_le (s := Icc 1 Q) (f := fun m => N - m)
    rw [Nat.card_Icc] at this h2
    exact_mod_cast (by omega : Psmall.card ≤ 2 * Q)
  set A : Finset ℤ := Pbig.image (fun p : ℕ => (p : ℤ))
  have hAcard : A.card = Pbig.card := card_image_of_injective _ Nat.cast_injective
  have hA : A ⊆ Ioc (0 : ℤ) (0 + (N : ℕ)) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_range] at hp
    rw [mem_Ioc]
    have := hp.1.2.1.pos
    constructor <;> push_cast <;> omega
  set B : ℕ → Finset ℕ := fun ℓ => {0, N % ℓ}
  have hB : ∀ ℓ, ℓ.Prime → B ℓ ⊆ range ℓ ∧ (B ℓ).card < ℓ := by
    intro ℓ hℓ
    refine ⟨?_, ?_⟩
    · intro b hb
      simp only [B, mem_insert, mem_singleton] at hb
      rw [mem_range]
      rcases hb with rfl | rfl
      · exact hℓ.pos
      · exact Nat.mod_lt _ hℓ.pos
    · rcases hℓ.eq_two_or_odd' with rfl | hodd
      · have : N % 2 = 0 := Nat.even_iff.1 hN
        simp [B, this]
      · have h3 : 3 ≤ ℓ := by
          rcases hodd with ⟨m, hm⟩
          have := hℓ.two_le; omega
        exact (card_insert_le _ _).trans_lt (by rw [card_singleton]; omega)
  have hAB : ∀ ℓ, ℓ.Prime → ℓ ≤ Q → ∀ n ∈ A, (n % (ℓ : ℤ)).toNat ∉ B ℓ := by
    intro ℓ hℓ hℓQ n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_range] at hp
    obtain ⟨⟨hpN, hpp, hqp⟩, hQp, hQq⟩ := hp
    simp only [B, mem_insert, mem_singleton]
    rw [← Int.natCast_mod, Int.toNat_natCast]
    rintro (h0 | h1)
    · have := (Nat.prime_dvd_prime_iff_eq hℓ hpp).1 (Nat.dvd_of_mod_eq_zero h0)
      omega
    · have hdvd : ℓ ∣ N - p := by
        apply Nat.dvd_of_mod_eq_zero
        exact Nat.sub_mod_eq_zero_of_mod_eq h1.symm
      have := (Nat.prime_dvd_prime_iff_eq hℓ hqp).1 hdvd
      omega
  have hmont := montgomery_sieve (by omega : 1 ≤ Q) 0 N A hA B hB hAB
  -- the sieve sum from below
  have hN1 : 1 ≤ N := by omega
  have hcop : ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q N), fC q ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q := by
    have hsub : (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q N) ⊆
        (Icc 1 Q).filter Squarefree := by
      intro q hq; rw [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩
    have hle : ∀ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q N),
        fC q ≤ hW B q := by
      intro q hq
      rw [mem_filter] at hq
      unfold fC hW
      apply Finset.prod_le_prod₀ (fun ℓ hℓ => cW_nonneg (Nat.prime_of_mem_primeFactors hℓ))
      intro ℓ hℓ
      have hℓp := Nat.prime_of_mem_primeFactors hℓ
      have hℓN : ¬ ℓ ∣ N := by
        intro h
        have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hℓ) h
        rw [hq.2.2.gcd_eq_one] at this
        exact hℓp.one_lt.ne' (Nat.dvd_one.1 this)
      have hℓ3 : 3 ≤ ℓ := by
        rcases hℓp.eq_two_or_odd' with rfl | hodd
        · exact absurd (even_iff_two_dvd.1 hN) hℓN
        · rcases hodd with ⟨m, hm⟩; have := hℓp.two_le; omega
      have hcard : (B ℓ).card = 2 := by
        simp only [B]
        rw [card_pair]
        intro h
        exact hℓN (Nat.dvd_of_mod_eq_zero h.symm)
      rw [hcard]
      push_cast
      exact cW_le_two_div hℓ3
    rw [← sum_congr rfl (fun q _ => rfl)]
    refine (sum_le_sum hle).trans (sum_le_sum_of_subset_of_nonneg hsub ?_)
    intro q _ _
    unfold hW
    refine prod_nonneg fun ℓ hℓ => ?_
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have := (hB ℓ hℓp).2
    have : ((B ℓ).card : ℝ) < ℓ := by exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsplitC := sum_sqf_c_le_coprime hN1 Q
  have htau := sum_tau_le_sum_sqf Q
  have hge := sum_tau_ge Q hQ
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hR : (0 : ℝ) < ((N : ℝ) / N.totient) ^ 2 := by positivity
  -- `log² 4 / 2 > 3/4`
  have hD : 0 < Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4 := by
    have h4 : Real.log 4 ≤ Real.log ((Q : ℝ) + 1) := by
      apply Real.log_le_log (by norm_num)
      have : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  set S := ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q
  have hS : (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) ≤ ((N : ℝ) / N.totient) ^ 2 * S := by
    have h1 : ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q ≤ ((N : ℝ) / N.totient) ^ 2 * S :=
      hsplitC.trans (mul_le_mul_of_nonneg_left hcop hR.le)
    have h2 : ∑ n ∈ Icc 1 Q, tau n / n ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q := htau
    linarith
  have hbig : (Pbig.card : ℝ) ≤ (N + 2 * (Q : ℝ) ^ 2) * ((N : ℝ) / N.totient) ^ 2 /
      (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
    rw [le_div_iff₀ hD, ← hAcard]
    have hm : (A.card : ℝ) * S ≤ N + 2 * (Q : ℝ) ^ 2 := hmont
    calc (A.card : ℝ) * (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4)
        ≤ (A.card : ℝ) * (((N : ℝ) / N.totient) ^ 2 * S) :=
          mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
      _ = ((A.card : ℝ) * S) * ((N : ℝ) / N.totient) ^ 2 := by ring
      _ ≤ (N + 2 * (Q : ℝ) ^ 2) * ((N : ℝ) / N.totient) ^ 2 :=
          mul_le_mul_of_nonneg_right hm hR.le
  rw [hsplit, Nat.cast_add]
  linarith

end LeanLab.PNTPort.LargeSieve
