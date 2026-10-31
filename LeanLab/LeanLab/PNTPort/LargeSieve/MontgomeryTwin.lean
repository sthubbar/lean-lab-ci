import LeanLab.PNTPort.LargeSieve.MontgomeryGoldbach

/-!
# An explicit upper bound for twin primes from Montgomery's sieve

Lab proof, unit U-5558, CLOUD 20261019T1321Z-cloud25. AI wrote this file. Known mathematics,
Brun 1919 for the order `N/log² N`. No cited input. The twin prime conjecture is open; this is an
upper bound.

* `twin_upper_montgomery`: for `N ≥ 1` and `Q ≥ 3`,
  `#{p ≤ N : p, p + 2 prime} ≤ Q + 4 (N + 2Q²)/(log²(Q + 1)/2 - 3/4)`.
  With `Q` near `√N/log N` this is `(32 + o(1)) N/log² N`, that is `(16/C₂ + o(1)) · 2C₂N/log² N`.

The sieve: modulo a prime `ℓ ≤ Q`, a prime `p > Q` with `p + 2` prime misses the classes `0` and
`-2 mod ℓ`; for `ℓ = 2` these coincide.
-/

namespace LeanLab.PNTPort.LargeSieve

open Finset Real

/-- **Twin prime upper bound, explicit, from Montgomery's sieve.** -/
theorem twin_upper_montgomery (N Q : ℕ) (hN : 1 ≤ N) (hQ : 3 ≤ Q) :
    ((((Icc 1 N).filter (fun p => p.Prime ∧ (p + 2).Prime)).card : ℕ) : ℝ) ≤
      Q + 4 * (N + 2 * (Q : ℝ) ^ 2) / (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
  set P := (Icc 1 N).filter (fun p => p.Prime ∧ (p + 2).Prime)
  set Pbig := P.filter (fun p => Q < p)
  set Psmall := P.filter (fun p => ¬ Q < p)
  have hsplit : P.card = Pbig.card + Psmall.card := (card_filter_add_card_filter_not _).symm
  have hsmall : (Psmall.card : ℝ) ≤ Q := by
    have hsub : Psmall ⊆ Icc 1 Q := by
      intro p hp
      simp only [Psmall, P, mem_filter, mem_Icc, not_lt] at hp
      exact mem_Icc.2 ⟨hp.1.1.1, hp.2⟩
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : Psmall.card ≤ Q)
  set A : Finset ℤ := Pbig.image (fun p : ℕ => (p : ℤ))
  have hAcard : A.card = Pbig.card := card_image_of_injective _ Nat.cast_injective
  have hA : A ⊆ Ioc (0 : ℤ) (0 + (N : ℕ)) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Icc] at hp
    rw [mem_Ioc]
    constructor <;> push_cast <;> omega
  set B : ℕ → Finset ℕ := fun ℓ => {0, (ℓ - 2 % ℓ) % ℓ}
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
      · simp [B]
      · have h3 : 3 ≤ ℓ := by
          rcases hodd with ⟨m, hm⟩
          have := hℓ.two_le; omega
        exact (card_insert_le _ _).trans_lt (by rw [card_singleton]; omega)
  have hAB : ∀ ℓ, ℓ.Prime → ℓ ≤ Q → ∀ n ∈ A, (n % (ℓ : ℤ)).toNat ∉ B ℓ := by
    intro ℓ hℓ hℓQ n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
    simp only [Pbig, P, mem_filter, mem_Icc] at hp
    obtain ⟨⟨-, hpp, hqp⟩, hQp⟩ := hp
    simp only [B, mem_insert, mem_singleton]
    rw [← Int.natCast_mod, Int.toNat_natCast]
    rintro (h0 | h1)
    · have := (Nat.prime_dvd_prime_iff_eq hℓ hpp).1 (Nat.dvd_of_mod_eq_zero h0)
      omega
    · have hdvd : ℓ ∣ p + 2 := by
        apply Nat.dvd_of_mod_eq_zero
        have h2 : 2 % ℓ ≤ ℓ := (Nat.mod_lt _ hℓ.pos).le
        rw [Nat.add_mod, h1]
        rcases Nat.lt_or_ge (2 % ℓ) 1 with h | h
        · have : 2 % ℓ = 0 := by omega
          rw [this, Nat.sub_zero, Nat.mod_self]; simp
        · rw [Nat.mod_eq_of_lt (by omega : ℓ - 2 % ℓ < ℓ), Nat.sub_add_cancel h2, Nat.mod_self]
      have := (Nat.prime_dvd_prime_iff_eq hℓ hqp).1 hdvd
      omega
  have hmont := montgomery_sieve (by omega : 1 ≤ Q) 0 N A hA B hB hAB
  have hcop : ∑ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q 2), fC q ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, hW B q := by
    have hsub : (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q 2) ⊆
        (Icc 1 Q).filter Squarefree := by
      intro q hq; rw [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩
    have hle : ∀ q ∈ (Icc 1 Q).filter (fun q => Squarefree q ∧ Nat.Coprime q 2),
        fC q ≤ hW B q := by
      intro q hq
      rw [mem_filter] at hq
      unfold fC hW
      apply Finset.prod_le_prod₀ (fun ℓ hℓ => cW_nonneg (Nat.prime_of_mem_primeFactors hℓ))
      intro ℓ hℓ
      have hℓp := Nat.prime_of_mem_primeFactors hℓ
      have hℓ2 : ¬ ℓ ∣ 2 := by
        intro h
        have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hℓ) h
        rw [hq.2.2.gcd_eq_one] at this
        exact hℓp.one_lt.ne' (Nat.dvd_one.1 this)
      have hℓ3 : 3 ≤ ℓ := by
        rcases hℓp.eq_two_or_odd' with rfl | hodd
        · exact absurd (dvd_refl 2) hℓ2
        · rcases hodd with ⟨m, hm⟩; have := hℓp.two_le; omega
      have hcard : (B ℓ).card = 2 := by
        simp only [B]
        rw [card_pair]
        rw [Nat.mod_eq_of_lt (by omega : 2 < ℓ), Nat.mod_eq_of_lt (by omega : ℓ - 2 < ℓ)]
        omega
      rw [hcard]
      push_cast
      exact cW_le_two_div hℓ3
    refine (sum_le_sum hle).trans (sum_le_sum_of_subset_of_nonneg hsub ?_)
    intro q _ _
    unfold hW
    refine prod_nonneg fun ℓ hℓ => ?_
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have := (hB ℓ hℓp).2
    have : ((B ℓ).card : ℝ) < ℓ := by exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsplitC := sum_sqf_c_le_coprime (by norm_num : 1 ≤ 2) Q
  have h2 : ((2 : ℕ) : ℝ) / (Nat.totient 2 : ℝ) = 2 := by
    rw [Nat.totient_prime Nat.prime_two]; norm_num
  rw [h2] at hsplitC
  have htau : ∑ n ∈ Icc 1 Q, tau n / n ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q :=
    sum_tau_le_sum_sqf Q
  have hge := sum_tau_ge Q hQ
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
  have hS : (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) ≤ 4 * S := by
    have h1 : ∑ q ∈ (Icc 1 Q).filter Squarefree, fC q ≤ (2 : ℝ) ^ 2 * S :=
      hsplitC.trans (mul_le_mul_of_nonneg_left hcop (by norm_num))
    linarith
  have hbig : (Pbig.card : ℝ) ≤ 4 * (N + 2 * (Q : ℝ) ^ 2) /
      (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4) := by
    rw [le_div_iff₀ hD, ← hAcard]
    have hm : (A.card : ℝ) * S ≤ N + 2 * (Q : ℝ) ^ 2 := hmont
    calc (A.card : ℝ) * (Real.log ((Q : ℝ) + 1) ^ 2 / 2 - 3 / 4)
        ≤ (A.card : ℝ) * (4 * S) := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
      _ = 4 * ((A.card : ℝ) * S) := by ring
      _ ≤ 4 * (N + 2 * (Q : ℝ) ^ 2) := by linarith
  rw [hsplit, Nat.cast_add]
  linarith

end LeanLab.PNTPort.LargeSieve
