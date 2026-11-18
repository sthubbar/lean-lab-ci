/-
P0083 Perelli 1996, page 481 between equations 3 and 4 and page 487 equation 28, elementary divisor mean support.
Proves a Landreau type divisor majorant: every m has a small e with e ^ κ ≤ m whose divisor count controls that of m.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

namespace LeanLab.Perelli1996.DivMean
open Finset

/-- Selection: a subset T of S, of size about S.card / κ, whose product to the κ is at most the product of S. -/
theorem selection (κ : ℕ) (hκ : 1 ≤ κ) : ∀ (n : ℕ) (S : Finset ℕ), S.card = n → (∀ p ∈ S, 1 ≤ p) →
    ∃ T : Finset ℕ, T ⊆ S ∧ S.card < κ * (T.card + 1) ∧ (∏ p ∈ T, p) ^ κ ≤ ∏ p ∈ S, p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS h1
    by_cases hlt : S.card < κ
    · refine ⟨∅, empty_subset _, by simpa using hlt, ?_⟩
      simp only [prod_empty, one_pow]
      exact Finset.one_le_prod₀ h1
    · rw [not_lt] at hlt
      obtain ⟨U, hUS, hUc⟩ := exists_subset_card_eq hlt
      have hUne : U.Nonempty := card_pos.1 (by omega)
      obtain ⟨x, hxU, hxmin⟩ : ∃ x ∈ U, ∀ y ∈ U, x ≤ y :=
        ⟨U.min' hUne, U.min'_mem hUne, fun y hy => U.min'_le y hy⟩
      have hcard2 : (S \ U).card + U.card = S.card := card_sdiff_add_card_eq_card hUS
      have hcard : (S \ U).card = S.card - κ := by omega
      obtain ⟨T', hT'S, hT'c, hT'p⟩ := ih (S.card - κ) (by omega) (S \ U) hcard
        (fun p hp => h1 p (mem_sdiff.1 hp).1)
      have hxT' : x ∉ T' := fun h => (mem_sdiff.1 (hT'S h)).2 hxU
      refine ⟨insert x T', ?_, ?_, ?_⟩
      · intro y hy
        rcases mem_insert.1 hy with h | hy
        · rw [h]; exact hUS hxU
        · exact (mem_sdiff.1 (hT'S hy)).1
      · rw [card_insert_of_notMem hxT']
        have h2 : κ * (T'.card + 1 + 1) = κ * (T'.card + 1) + κ := by ring
        rw [h2]
        linarith
      · rw [prod_insert hxT', mul_pow, ← prod_sdiff hUS, mul_comm]
        apply Nat.mul_le_mul hT'p
        calc x ^ κ = ∏ _p ∈ U, x := by rw [prod_const, hUc]
          _ ≤ ∏ p ∈ U, p :=
            Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun p hp => hxmin p hp)

/-- Factorization of a product of prime powers over a finset of primes. -/
theorem factorization_prod_prime_pow (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (g : ℕ → ℕ) (q : ℕ) :
    (∏ p ∈ s, p ^ g p).factorization q = if q ∈ s then g q else 0 := by
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hs p hp).ne_zero)]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(hs p hp).factorization_pow, Finsupp.single_apply] :
      ∀ p ∈ s, ((p ^ g p).factorization) q = if p = q then g p else 0)]
  exact Finset.sum_ite_eq' s q g

/-- Divisor count of a product of prime powers over a finset of primes. -/
theorem card_divisors_prod_prime_pow (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (g : ℕ → ℕ) :
    (∏ p ∈ s, p ^ g p).divisors.card = ∏ p ∈ s, (g p + 1) := by
  have hne : (∏ p ∈ s, p ^ g p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ (hs p hp).ne_zero)
  rw [Nat.card_divisors hne]
  have hsub : (∏ p ∈ s, p ^ g p).primeFactors ⊆ s := by
    intro q hq
    by_contra hqs
    have h0 := factorization_prod_prime_pow s hs g q
    simp only [hqs, ↓reduceIte] at h0
    have hpos := (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd hne
      (Nat.dvd_of_mem_primeFactors hq)
    omega
  refine (Finset.prod_subset hsub ?_).trans ?_
  · intro q _ hnq
    have h0 : (∏ p ∈ s, p ^ g p).factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      rw [Nat.mem_primeFactors] at hnq
      tauto
    simp [h0]
  · exact Finset.prod_congr rfl (fun q hq => by
      simp only [factorization_prod_prime_pow s hs g q, hq, ↓reduceIte])

/-- For x at least 2 and κ at least 1, κ * x ≤ x ^ κ. -/
theorem mul_le_pow_self (κ x : ℕ) (hκ : 1 ≤ κ) (hx : 2 ≤ x) : κ * x ≤ x ^ κ := by
  obtain ⟨j, rfl⟩ : ∃ j, κ = j + 1 := ⟨κ - 1, by omega⟩
  rw [pow_succ]
  apply Nat.mul_le_mul_right
  calc j + 1 ≤ 2 ^ j := Nat.succ_le_of_lt Nat.lt_two_pow_self
    _ ≤ x ^ j := Nat.pow_le_pow_left hx j

/-- Landreau type divisor majorant. -/
theorem divisor_majorant (k κ : ℕ) (hκ : 2 ≤ κ) (hk : k ≤ κ) (m : ℕ) (hm : 0 < m) :
    ∃ e : ℕ, 0 < e ∧ e ^ κ ≤ m ∧ m.divisors.card ≤ κ ^ (κ - 1) * e.divisors.card ^ (κ ^ 2) ∧
      ∀ p b : ℕ, p.Prime → 1 ≤ b → p ^ b ∣ e → p ^ (1 + k * (b - 1)) ∣ m := by
  classical
  have hm0 : m ≠ 0 := hm.ne'
  have hκ0 : 0 < κ := by omega
  have hP : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hapos : ∀ p ∈ m.primeFactors, 1 ≤ m.factorization p := fun p hp =>
    (hP p hp).factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ,
      S = m.primeFactors.filter (fun p => m.factorization p < κ) := ⟨_, rfl⟩
  have hSmem : ∀ p, p ∈ S ↔ p ∈ m.primeFactors ∧ m.factorization p < κ := by
    intro p; rw [hS, mem_filter]
  obtain ⟨T, hTS, hTc, hTp⟩ := selection κ (by omega) S.card S rfl
    (fun p hp => (hP p ((hSmem p).1 hp).1).pos)
  have hTlt : ∀ p ∈ T, m.factorization p < κ := fun p hp => ((hSmem p).1 (hTS hp)).2
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ,
      ∀ p, g p = m.factorization p / κ + if p ∈ T then 1 else 0 := ⟨_, fun _ => rfl⟩
  have hgS : ∀ p, m.factorization p < κ → g p = if p ∈ T then 1 else 0 := by
    intro p h; rw [hg, Nat.div_eq_of_lt h, zero_add]
  have hgN : ∀ p, ¬ m.factorization p < κ → g p = m.factorization p / κ := by
    intro p h
    have hT : p ∉ T := fun hT => h (hTlt p hT)
    simp only [hg, hT, ↓reduceIte, add_zero]
  have hfac := factorization_prod_prime_pow m.primeFactors hP g
  have hcard := card_divisors_prod_prime_pow m.primeFactors hP g
  have hene : (∏ p ∈ m.primeFactors, p ^ g p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)
  have hmprod : ∏ p ∈ m.primeFactors, p ^ m.factorization p = m :=
    (Nat.prod_factorization_eq_prod_primeFactors _).symm.trans
      (Nat.prod_factorization_pow_eq_self hm0)
  refine ⟨∏ p ∈ m.primeFactors, p ^ g p, Nat.pos_of_ne_zero hene, ?_, ?_, ?_⟩
  · -- e ^ κ ≤ m
    refine le_of_le_of_eq ?_ hmprod
    have h1 := Finset.prod_filter_mul_prod_filter_not m.primeFactors
      (fun p => m.factorization p < κ) (fun p => (p ^ g p) ^ κ)
    have h2 := Finset.prod_filter_mul_prod_filter_not m.primeFactors
      (fun p => m.factorization p < κ) (fun p => p ^ m.factorization p)
    rw [← hS] at h1 h2
    rw [← Finset.prod_pow, ← h1, ← h2]
    apply Nat.mul_le_mul
    · have hpg : ∀ p ∈ S, p ^ g p = if p ∈ T then p else 1 := by
        intro p hp
        rw [hgS p ((hSmem p).1 hp).2]
        split_ifs <;> simp
      have hS1 : ∏ p ∈ S, (p ^ g p) ^ κ = (∏ p ∈ T, p) ^ κ := by
        rw [Finset.prod_pow, Finset.prod_congr rfl hpg, Finset.prod_ite_mem,
          Finset.inter_eq_right.2 hTS]
      rw [hS1]
      refine hTp.trans (Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun p hp => ?_))
      have h3 := hapos p ((hSmem p).1 hp).1
      exact Nat.le_self_pow (by omega) p
    · apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
      intro p hp
      have hp' := (mem_filter.1 hp).2
      rw [hgN p hp', ← pow_mul]
      exact Nat.pow_le_pow_right (hP p (mem_filter.1 hp).1).pos (Nat.div_mul_le_self _ _)
  · -- divisor count
    have h3 := Finset.prod_filter_mul_prod_filter_not m.primeFactors
      (fun p => m.factorization p < κ) (fun p => m.factorization p + 1)
    have h4 := Finset.prod_filter_mul_prod_filter_not m.primeFactors
      (fun p => m.factorization p < κ) (fun p => g p + 1)
    rw [← hS] at h3 h4
    have hm_card : m.divisors.card = (∏ p ∈ S, (m.factorization p + 1)) *
        ∏ p ∈ m.primeFactors with ¬ m.factorization p < κ, (m.factorization p + 1) := by
      rw [Nat.card_divisors hm0]; exact h3.symm
    have hq : ∀ p ∈ S, g p + 1 = if p ∈ T then 2 else 1 := by
      intro p hp
      rw [hgS p ((hSmem p).1 hp).2]
      split_ifs <;> rfl
    have hS2 : ∏ p ∈ S, (g p + 1) = 2 ^ T.card := by
      rw [Finset.prod_congr rfl hq, Finset.prod_ite_mem, Finset.inter_eq_right.2 hTS,
        Finset.prod_const]
    have he_card : (∏ p ∈ m.primeFactors, p ^ g p).divisors.card = 2 ^ T.card *
        ∏ p ∈ m.primeFactors with ¬ m.factorization p < κ, (g p + 1) := by
      rw [hcard, ← h4, hS2]
    -- the S part
    have hA1 : ∏ p ∈ S, (m.factorization p + 1) ≤ κ ^ S.card := by
      calc ∏ p ∈ S, (m.factorization p + 1) ≤ ∏ _p ∈ S, κ :=
            Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
              (fun p hp => ((hSmem p).1 hp).2)
        _ = κ ^ S.card := Finset.prod_const _
    have hκ2 : κ ^ κ ≤ 2 ^ (κ ^ 2) := by
      calc κ ^ κ ≤ (2 ^ κ) ^ κ := Nat.pow_le_pow_left Nat.lt_two_pow_self.le κ
        _ = 2 ^ (κ ^ 2) := by rw [← pow_mul, sq]
    have hA2 : κ ^ S.card ≤ κ ^ (κ - 1) * (2 ^ T.card) ^ (κ ^ 2) := by
      have hc : S.card ≤ (κ - 1) + κ * T.card := by
        have h5 : κ * (T.card + 1) = κ * T.card + κ := by ring
        rw [h5] at hTc
        omega
      calc κ ^ S.card ≤ κ ^ ((κ - 1) + κ * T.card) := Nat.pow_le_pow_right hκ0 hc
        _ = κ ^ (κ - 1) * (κ ^ κ) ^ T.card := by rw [pow_add, pow_mul]
        _ ≤ κ ^ (κ - 1) * (2 ^ (κ ^ 2)) ^ T.card :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hκ2 _)
        _ = κ ^ (κ - 1) * (2 ^ T.card) ^ (κ ^ 2) := by
            rw [← pow_mul, ← pow_mul, mul_comm (κ ^ 2)]
    -- the complement part
    have hB : ∏ p ∈ m.primeFactors with ¬ m.factorization p < κ, (m.factorization p + 1) ≤
        (∏ p ∈ m.primeFactors with ¬ m.factorization p < κ, (g p + 1)) ^ (κ ^ 2) := by
      rw [← Finset.prod_pow]
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
      intro p hp
      have hp' := (mem_filter.1 hp).2
      rw [hgN p hp']
      have hb1 : 1 ≤ m.factorization p / κ := Nat.div_pos (by omega) hκ0
      have h6 : m.factorization p < κ * (m.factorization p / κ + 1) :=
        Nat.lt_mul_div_succ _ hκ0
      have h7 := mul_le_pow_self κ (m.factorization p / κ + 1) (by omega) (by omega)
      have h8 : (m.factorization p / κ + 1) ^ κ ≤ (m.factorization p / κ + 1) ^ (κ ^ 2) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_self_pow (by norm_num) κ)
      omega
    rw [hm_card, he_card, mul_pow]
    calc (∏ p ∈ S, (m.factorization p + 1)) *
          ∏ p ∈ m.primeFactors with ¬ m.factorization p < κ, (m.factorization p + 1)
        ≤ (κ ^ (κ - 1) * (2 ^ T.card) ^ (κ ^ 2)) *
          (∏ p ∈ m.primeFactors with ¬ m.factorization p < κ, (g p + 1)) ^ (κ ^ 2) :=
          Nat.mul_le_mul (hA1.trans hA2) hB
      _ = _ := mul_assoc _ _ _
  · -- prime power clause
    intro p b hp hb hdvd
    have hb' := (hp.pow_dvd_iff_le_factorization hene).1 hdvd
    rw [hfac] at hb'
    by_cases hpP : p ∈ m.primeFactors
    · simp only [hpP, ↓reduceIte] at hb'
      rw [hp.pow_dvd_iff_le_factorization hm0]
      by_cases hlt : m.factorization p < κ
      · have h9 : g p ≤ 1 := by
          rw [hgS p hlt]; split_ifs <;> omega
        have h10 := hapos p hpP
        have hb1 : b = 1 := by omega
        subst hb1
        simpa using h10
      · rw [hgN p hlt] at hb'
        have h5 : b * κ ≤ m.factorization p := (Nat.le_div_iff_mul_le hκ0).1 hb'
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
        have h6 : k * c ≤ κ * c := Nat.mul_le_mul_right c hk
        have h7 : (c + 1) * κ = κ * c + κ := by ring
        rw [h7] at h5
        rw [Nat.add_sub_cancel]
        linarith
    · simp only [hpP, ↓reduceIte] at hb'; omega

#print axioms selection
#print axioms divisor_majorant

end LeanLab.Perelli1996.DivMean
