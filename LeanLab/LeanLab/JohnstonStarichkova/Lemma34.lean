/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3: Lemma 3.4 and Theorem 1.3.
Unit U-0342, run 20261017T1803Z-21479.
Lemma 3.4 bounds the number of prime factors of a square-free η < X₂ coprime to 30030 by the
largest K with p₇ p₈ ... p_{K+6} < X₂. With X₂ = exp exp 7.816 as printed, that K is 368:
the product of the first 368 primes from 17 is below X₂ and that of the first 369 is above.
The paper prints K = 369. Theorem 1.3 is assembled here from its three cited inputs, the sieve
range N ≥ X₂, Hathi-Johnston 2021 Theorem 1.5 and Oliveira e Silva-Herzog-Pardi, and holds
with 368; so it is CONDITIONAL ON those inputs, not PROVED.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.AlmostPrimes.Statements
import LeanLab.JohnstonStarichkova.Primes

namespace LeanLab.JohnstonStarichkova

open Finset Nat

/-- Distinct primes at least 17 have product at least that of the first that many of them. -/
theorem prod_nth_le (S : Finset ℕ) (hS : ∀ s ∈ S, P17 s) :
    ∏ i ∈ range S.card, nth P17 i ≤ ∏ s ∈ S, s := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem ha, prod_range_succ, prod_insert ha]
    have ih' := ih (fun x hx => hS x (mem_insert_of_mem hx))
    have hPa : P17 a := hS a (mem_insert_self a s)
    have hcard : s.card ≤ count P17 a := by
      rw [count_eq_card_filter_range]
      apply card_le_card
      intro x hx
      simp only [mem_filter, mem_range]
      exact ⟨hlt x hx, hS x (mem_insert_of_mem hx)⟩
    have hnth : nth P17 s.card ≤ a :=
      calc nth P17 s.card ≤ nth P17 (count P17 a) := nth_monotone P17_infinite hcard
        _ = a := nth_count hPa
    rw [mul_comm]
    exact Nat.mul_le_mul hnth ih'

/-- The prime factors of an η coprime to 30030 are at least 17. -/
theorem P17_of_dvd {η s : ℕ} (hcop : Nat.Coprime η 30030) (hs : s ∈ η.primeFactorsList) :
    P17 s := by
  have hp := Nat.prime_of_mem_primeFactorsList hs
  have hd := Nat.dvd_of_mem_primeFactorsList hs
  refine ⟨hp, ?_⟩
  by_contra hlt
  push_neg at hlt
  have h30 : s ∣ 30030 := by interval_cases s <;> first | (exfalso; revert hp; norm_num; done) | norm_num
  have h1 := Nat.dvd_gcd hd h30
  rw [Nat.Coprime.gcd_eq_one hcop] at h1
  exact hp.ne_one (Nat.dvd_one.mp h1)

/-- Lemma 3.4, arithmetic core: a square-free η < X coprime to 30030 has at most k prime
factors when the first k + 1 primes from 17 have product at least X. -/
theorem length_le_of_prod {η X k : ℕ} (hsq : Squarefree η) (hcop : Nat.Coprime η 30030)
    (hηX : η < X) (hk : X ≤ ∏ i ∈ range (k + 1), nth P17 i) :
    η.primeFactorsList.length ≤ k := by
  by_contra hcon
  push_neg at hcon
  have h0 : η ≠ 0 := by rintro rfl; exact not_squarefree_zero hsq
  have hnd := (squarefree_iff_nodup_primeFactorsList h0).mp hsq
  have hcard : η.primeFactorsList.toFinset.card = η.primeFactorsList.length :=
    List.toFinset_card_of_nodup hnd
  have hprod : ∏ s ∈ η.primeFactorsList.toFinset, s = η := by
    rw [List.prod_toFinset _ hnd]; simp [Nat.prod_primeFactorsList h0]
  have hS : ∀ s ∈ η.primeFactorsList.toFinset, P17 s :=
    fun s hs => P17_of_dvd hcop (List.mem_toFinset.mp hs)
  have h1 : ∏ i ∈ range (k + 1), nth P17 i ≤
      ∏ i ∈ range η.primeFactorsList.toFinset.card, nth P17 i := by
    apply prod_le_prod_of_subset_of_one_le'
    · exact range_subset_range.mpr (by omega)
    · intro i _ _
      exact le_trans (by norm_num) (nth_mem_of_infinite P17_infinite i).2
  have h2 := prod_nth_le _ hS
  rw [hprod] at h2
  omega

/-! ### The numbers -/

/-- The paper's X₂ = exp(exp 7.816). -/
noncomputable def X2 : ℝ := Real.exp (Real.exp 7.816)

theorem exp_816_le : Real.exp 0.816 ≤ 2.2615 := by
  have h := Real.exp_bound' (x := 0.816) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_816_ge : 2.2614 ≤ Real.exp 0.816 := by
  have h := Real.sum_le_exp_of_nonneg (x := 0.816) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp7816_eq : Real.exp 7.816 = Real.exp 1 ^ 7 * Real.exp 0.816 := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem exp7816_lt : Real.exp 7.816 < 2485 := by
  rw [exp7816_eq]
  have h3 : Real.exp 1 ^ 7 < 2.7182818286 ^ 7 := by
    gcongr; exact Real.exp_one_lt_d9
  calc Real.exp 1 ^ 7 * Real.exp 0.816 ≤ 2.7182818286 ^ 7 * 2.2615 :=
        mul_le_mul h3.le exp_816_le (Real.exp_pos _).le (by positivity)
    _ < 2485 := by norm_num

theorem exp7816_gt : 2479 < Real.exp 7.816 := by
  rw [exp7816_eq]
  have h3 : 2.7182818283 ^ 7 < Real.exp 1 ^ 7 := by
    gcongr; exact Real.exp_one_gt_d9
  calc (2479 : ℝ) < 2.7182818283 ^ 7 * 2.2614 := by norm_num
    _ ≤ Real.exp 1 ^ 7 * Real.exp 0.816 :=
        mul_le_mul h3.le exp_816_ge (by norm_num) (by positivity)

theorem big369 : (27182818286 : ℕ) ^ 2485 < (∏ i ∈ range 369, Q.getD i 0) * 10 ^ 24850 := by
  decide +kernel

theorem big368 : (∏ i ∈ range 368, Q.getD i 0) * 10 ^ 24790 < (27182818283 : ℕ) ^ 2479 := by
  decide +kernel

theorem prod369_gt : Real.exp 2485 < ((∏ i ∈ range 369, Q.getD i 0 : ℕ) : ℝ) := by
  have he : Real.exp 2485 = Real.exp 1 ^ 2485 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 : Real.exp 1 ^ 2485 < ((27182818286 : ℝ) / 10 ^ 10) ^ 2485 := by
    gcongr
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  rw [he]
  refine h1.trans ?_
  rw [div_pow, div_lt_iff₀ (by positivity), ← pow_mul]
  rw [show 10 * 2485 = 24850 from rfl]
  exact_mod_cast big369

theorem prod368_lt : ((∏ i ∈ range 368, Q.getD i 0 : ℕ) : ℝ) < Real.exp 2479 := by
  have he : Real.exp 2479 = Real.exp 1 ^ 2479 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 : ((27182818283 : ℝ) / 10 ^ 10) ^ 2479 < Real.exp 1 ^ 2479 := by
    gcongr
    have := Real.exp_one_gt_d9
    norm_num at this ⊢
    linarith
  rw [he]
  refine lt_trans ?_ h1
  rw [div_pow, lt_div_iff₀ (by positivity), ← pow_mul]
  rw [show 10 * 2479 = 24790 from rfl]
  exact_mod_cast big368

theorem prodP17_eq {k : ℕ} (hk : k ≤ 370) :
    ∏ i ∈ range k, nth P17 i = ∏ i ∈ range k, Q.getD i 0 :=
  prod_congr rfl (fun i hi => nth_P17 (by simp at hi; omega))

theorem prodPrime_eq {k : ℕ} (hk : k ≤ 370) :
    ∏ i ∈ range k, nth Nat.Prime (i + 6) = ∏ i ∈ range k, Q.getD i 0 :=
  prod_congr rfl (fun i hi => nth_prime_Q (by simp at hi; omega))

/-- The paper's K, read off its own definition: the largest K with
p₇ p₈ ... p_{K+6} < X₂ is 368, since that product is below X₂ for K = 368 and above for
K = 369. Here `nth Nat.Prime (i + 6)` is p_{i+7}, primes counted from p₁ = 2. -/
theorem K_eq_368 :
    ((∏ i ∈ range 368, nth Nat.Prime (i + 6) : ℕ) : ℝ) < X2 ∧
      X2 < ((∏ i ∈ range 369, nth Nat.Prime (i + 6) : ℕ) : ℝ) := by
  rw [prodPrime_eq (by norm_num), prodPrime_eq (by norm_num)]
  constructor
  · exact prod368_lt.trans (Real.exp_lt_exp.mpr exp7816_gt)
  · exact (Real.exp_lt_exp.mpr exp7816_lt).trans prod369_gt

/-- Lemma 3.4 as it applies with the printed X₂: a square-free η < X₂ coprime to 30030
has at most 368 prime factors, counted with multiplicity. -/
theorem lemma34_omega {η : ℕ} (hsq : Squarefree η) (hcop : Nat.Coprime η 30030)
    (hη : (η : ℝ) < X2) : η.primeFactorsList.length ≤ 368 := by
  apply length_le_of_prod hsq hcop (X := ∏ i ∈ range 369, nth P17 i) _ le_rfl
  rw [prodP17_eq (by norm_num)]
  have : (η : ℝ) < ((∏ i ∈ range 369, Q.getD i 0 : ℕ) : ℝ) :=
    hη.trans ((Real.exp_lt_exp.mpr exp7816_lt).trans prod369_gt)
  exact_mod_cast this

/-! ### Theorem 1.3 from its cited inputs -/

open LeanLab.AlmostPrimes in
/-- Cited: the sieve range of the Theorem 1.3 proof, every even N ≥ X₂ is a prime plus a
number with at most M - 1 = 39 prime factors. -/
def SieveRange : Prop := ∀ N : ℕ, Even N → X2 ≤ N → PrimePlusAlmostPrime 39 N

/-- Cited: Hathi-Johnston 2021 Theorem 1.5 as the Lemma 3.4 proof uses it, for
4 · 10^18 < N < X₂, N = p + η with η square-free, η > 1, coprime to 30030. -/
def HJ21 : Prop := ∀ N : ℕ, Even N → 4 * 10 ^ 18 < N → (N : ℝ) < X2 →
  ∃ p η : ℕ, p.Prime ∧ Squarefree η ∧ 1 < η ∧ Nat.Coprime η 30030 ∧ N = p + η

open LeanLab.AlmostPrimes in
theorem primePlus_mono {k k' N : ℕ} (h : PrimePlusAlmostPrime k N) (hk : k ≤ k') :
    PrimePlusAlmostPrime k' N := by
  obtain ⟨p, m, hp, hm, hN, hO⟩ := h
  exact ⟨p, m, hp, hm, hN, hO.trans hk⟩

open LeanLab.AlmostPrimes in
/-- Theorem 1.3 with 368 in place of the printed 369, CONDITIONAL ON the three cited inputs. -/
theorem theorem1_3_368 (hS : SieveRange) (hH : HJ21) (hG : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ N : ℕ, Even N → 4 ≤ N → PrimePlusAlmostPrime 368 N := by
  intro N hN h4
  by_cases hsmall : N ≤ 4 * 10 ^ 18
  · obtain ⟨p, q, hp, hq, hpq⟩ := hG N hN h4 hsmall
    refine ⟨p, q, hp, hq.pos, hpq.symm, ?_⟩
    simp [bigOmega, Nat.primeFactorsList_prime hq]
  · push_neg at hsmall
    by_cases hX : (N : ℝ) < X2
    · obtain ⟨p, η, hp, hsq, h1, hcop, hpη⟩ := hH N hN hsmall hX
      refine ⟨p, η, hp, by omega, hpη, ?_⟩
      have : (η : ℝ) < X2 := lt_of_le_of_lt (by exact_mod_cast (by omega : η ≤ N)) hX
      exact lemma34_omega hsq hcop this
    · push_neg at hX
      exact primePlus_mono (hS N hN hX) (by norm_num)

open LeanLab.AlmostPrimes in
/-- The printed Theorem 1.3, 369 prime factors, CONDITIONAL ON the same inputs. -/
theorem theorem1_3 (hS : SieveRange) (hH : HJ21) (hG : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ N : ℕ, Even N → 4 ≤ N → PrimePlusAlmostPrime 369 N :=
  fun N hN h4 => primePlus_mono (theorem1_3_368 hS hH hG N hN h4) (by norm_num)

open LeanLab.AlmostPrimes in
/-- The lab's earlier statement from the v2 abstract, 395, follows. -/
theorem johnston_starichkova_of (hS : SieveRange) (hH : HJ21)
    (hG : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ N : ℕ, Even N → 4 ≤ N → PrimePlusAlmostPrime 395 N :=
  fun N hN h4 => primePlus_mono (theorem1_3_368 hS hH hG N hN h4) (by norm_num)

end LeanLab.JohnstonStarichkova
