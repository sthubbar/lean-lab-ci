/-
ROUTE BURST session 4, 2026-11-12. Split of `LeanLab.AlmostPrimes.johnston_starichkova`.

Paper P0019: D. R. Johnston, V. V. Starichkova, Some explicit results on the sum of a prime and an
almost prime, arXiv 2208.01229, version v3 dated April 14, 2025, Theorem 1.3, with K = 395 and
X₂ = exp(exp 7.9). Local copy papers/P0019.pdf, pages 9, 13 and 14 checked.

AI wrote this Lean code. Binary Goldbach is OPEN.

The proof of Theorem 1.3 on pp. 13 and 14 has three ranges.
* `N ≤ 4 · 10^18`: Goldbach verification [26], used in the proof of Lemma 3.5, p. 9.
* `4 · 10^18 < N < X₂`: Hathi and Johnston [19, Theorem 1.5], then the prime counting in
  Lemma 3.5, p. 9, which with X₂ = exp(exp 7.9) gives K = 395.
* `N ≥ X₂`: Theorem 4.2 with the parameters (4.6), u₀ = 400, δ = 1.3, α = 0.25, M = 40 gives
  S(A, P(z)) > 0 with z = N^{1/40}, and π_{M-1}(N) ≥ S(A, P(z)), Section 4 opening, p. 9.

Leaves, sorry marks the cited or deep ones:
1. `leaf_goldbach_4e18`, sorry, cited [26] Oliveira e Silva, Herzog, Pardi.
2. `leaf_hathi_johnston`, sorry, cited [19, Theorem 1.5] as quoted in Section 5.2, p. 15.
3. `leaf_lemma35_count`, PROVED, the counting step of Lemma 3.5 at X₂ = exp(exp 7.9), from the
   folder's `JohnstonStarichkova.Novelty1602.js_v3_K395` and `Theorem14.length_le_of_prod_ge`.
4. `leaf_theorem42_positive`, sorry, Theorem 4.2 at the parameters of the proof of Theorem 1.3.
5. `leaf_sifted_omega`, PROVED, π_{M-1}(N) ≥ S(A, P(z)) for M = 40, Section 4, p. 9.
-/
import Mathlib
import LeanLab.AlmostPrimes.Statements
import LeanLab.JohnstonStarichkova.Novelty1602

namespace LeanLab.AlmostPrimes.Burst4Split

open LeanLab.AlmostPrimes LeanLab.JohnstonStarichkova Finset Nat

/-- X₂ = exp(exp 7.9), the v3 choice in the proof of Theorem 1.3, p. 13. -/
noncomputable def X2v3 : ℝ := Real.exp (Real.exp 7.9)

/-- A = {N − p : p ≤ N, p ∤ N}, Section 2, p. 3 to 4. -/
def setA (N : ℕ) : Finset ℕ :=
  ((range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ N)).image (fun p => N - p)

open Classical in
/-- S(A, P(z)): the elements of A with no prime factor p < z, p ∤ N, where
P(z) = ∏_{p < z, p ∤ N} p, Section 2, p. 4. The paper writes S(A, P(z)) for its size. -/
noncomputable def siftedSet (N : ℕ) (z : ℝ) : Finset ℕ :=
  (setA N).filter (fun a => ∀ q : ℕ, q.Prime → (q : ℝ) < z → ¬ q ∣ N → ¬ q ∣ a)

/-! ### Leaves -/

/-- LEAF: leaf 1, cited. Goldbach's conjecture holds for even N ≤ 4 · 10^18, reference [26] of P0019,
used in the proof of Lemma 3.5, p. 9, and in the proof of Theorem 4.2, p. 13. -/
theorem leaf_goldbach_4e18 : EvenGoldbachUpTo (4 * 10 ^ 18) := by
  sorry

/-- LEAF: leaf 2, cited. Hathi and Johnston [19, Theorem 1.5], as P0019 states it in Section 5.2,
p. 15, and uses it in the proof of Lemma 3.5, p. 9: every even N ≥ 40 is a prime plus a
square-free number coprime to 2 · 3 · 5 · 7 · 11 · 13 = 30030. -/
theorem leaf_hathi_johnston : ∀ N : ℕ, Even N → 40 ≤ N →
    ∃ p η : ℕ, p.Prime ∧ Squarefree η ∧ Nat.Coprime η 30030 ∧ N = p + η := by
  sorry

/-- LEAF: leaf 3, PROVED. Lemma 3.5, p. 9, counting step at X₂ = exp(exp 7.9): a square-free η < X₂
coprime to 30030 has at most K = 395 prime factors, since the 396 primes 17 to 2753 multiply to
at least X₂. -/
theorem leaf_lemma35_count {η : ℕ} (hsq : Squarefree η) (hcop : Nat.Coprime η 30030)
    (hη : (η : ℝ) < X2v3) : bigOmega η ≤ 395 := by
  have e : ∀ i, nth (Pge 17) i = nth Nat.Prime (6 + i) := by
    intro i
    rw [← Novelty1602.nth_prime_six, nth_Pge, add_comm]
  have hX : X2v3 ≤ ((∏ i ∈ range 396, nth (Pge 17) i : ℕ) : ℝ) := by
    have h := Novelty1602.js_v3_K395.2
    rw [Finset.prod_Ico_eq_prod_range, show (402 : ℕ) - 6 = 396 from rfl] at h
    rw [Nat.cast_prod]
    unfold X2v3
    refine h.trans (le_of_eq (Finset.prod_congr rfl (fun i _ => ?_)))
    rw [e i]
  have hlt : η < ∏ i ∈ range 396, nth (Pge 17) i := by
    exact_mod_cast hη.trans_le hX
  have hbc : ∀ s, s.Prime → s < 17 → s ∣ 30030 := by
    intro s hp hs
    interval_cases s <;> first | (exfalso; revert hp; norm_num; done) | norm_num
  exact length_le_of_prod_ge (b := 17) (c := 30030) (k := 395) hbc hsq hcop hlt le_rfl

/-- LEAF: leaf 4, deep. Theorem 4.2, pp. 11 to 12, applied in the proof of Theorem 1.3, p. 13, with
(Y₀, α₁, α₂, C) = (7.9, 7, 2, 3.98) from (4.6), u₀ = 400, δ = 1.3, α = 0.25, M = 40 and
X₂ = exp(exp 7.9): S(A, P(z)) > 0 for every even N ≥ X₂ with z = N^{1/40}. The paper gets
S(A, P(z)) > 38 U_N N / log² N or > 5 U_N N / log² N in the cases k₁ < K_δ(x₁) and
k₁ ≥ K_δ(x₁). -/
theorem leaf_theorem42_positive : ∀ N : ℕ, Even N → X2v3 ≤ (N : ℝ) →
    0 < (siftedSet N ((N : ℝ) ^ ((1 : ℝ) / 40))).card := by
  sorry

/-- Products of naturals each at least z ≥ 0 are at least z ^ length. -/
theorem pow_length_le_prod (z : ℝ) (hz : 0 ≤ z) :
    ∀ l : List ℕ, (∀ q ∈ l, z ≤ (q : ℝ)) → z ^ l.length ≤ ((l.prod : ℕ) : ℝ)
  | [], _ => by simp
  | q :: l, h => by
    rw [List.length_cons, _root_.pow_succ', List.prod_cons, Nat.cast_mul]
    exact mul_le_mul (h q List.mem_cons_self)
      (pow_length_le_prod z hz l (fun r hr => h r (List.mem_cons_of_mem q hr)))
      (pow_nonneg hz _) (Nat.cast_nonneg _)

/-- LEAF: leaf 5, PROVED. Section 4, p. 9: π_{M-1}(N) ≥ S(A, P(z)) for z = N^{1/M}, here M = 40.
Every element a = N − p of the sifted set has all prime factors at least N^{1/40} and a < N,
so a has at most 39 prime factors. -/
theorem leaf_sifted_omega (N : ℕ) (hN : 1 ≤ N) (a : ℕ)
    (ha : a ∈ siftedSet N ((N : ℝ) ^ ((1 : ℝ) / 40))) :
    ∃ p : ℕ, p.Prime ∧ N = p + a ∧ 0 < a ∧ bigOmega a ≤ 39 := by
  classical
  set z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 40) with hzdef
  unfold siftedSet at ha
  rw [mem_filter] at ha
  obtain ⟨hA, hsift⟩ := ha
  unfold setA at hA
  rw [mem_image] at hA
  obtain ⟨p, hp, rfl⟩ := hA
  rw [mem_filter, mem_range] at hp
  obtain ⟨hpN, hpr, hpnd⟩ := hp
  have hpN' : p < N := by
    rcases Nat.lt_or_ge p N with h | h
    · exact h
    · exfalso
      have : p = N := by omega
      exact hpnd (this ▸ dvd_refl p)
  refine ⟨p, hpr, by omega, by omega, ?_⟩
  have ha0 : N - p ≠ 0 := by omega
  have hfac : ∀ q ∈ (N - p).primeFactorsList, z ≤ (q : ℝ) := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactorsList hq
    have hqd := Nat.dvd_of_mem_primeFactorsList hq
    by_contra hlt
    push_neg at hlt
    by_cases hqN : q ∣ N
    · have h1 : q ∣ N - (N - p) := Nat.dvd_sub hqN hqd
      rw [Nat.sub_sub_self hpN'.le] at h1
      have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hpr).mp h1
      exact hpnd (hqp' ▸ hqN)
    · exact hsift q hqp hlt hqN hqd
  have hz0 : 0 ≤ z := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hz1 : 1 ≤ z := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hz40 : z ^ (40 : ℕ) = (N : ℝ) := by
    rw [hzdef, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hprod := pow_length_le_prod z hz0 _ hfac
  rw [Nat.prod_primeFactorsList ha0] at hprod
  unfold bigOmega
  by_contra hcon
  push_neg at hcon
  have h1 : z ^ (40 : ℕ) ≤ z ^ (N - p).primeFactorsList.length :=
    pow_le_pow_right₀ hz1 (by omega)
  have hp0 := hpr.pos
  have h2 : ((N - p : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : N - p < N)
  linarith

/-! ### Proved intermediate steps -/

/-- Lemma 3.5, p. 9, at X₂ = exp(exp 7.9) and K = 395, from leaves 1, 2 and 3. -/
theorem lemma35 (N : ℕ) (hE : Even N) (h4 : 4 ≤ N) (hX : (N : ℝ) < X2v3) :
    PrimePlusAlmostPrime 395 N := by
  by_cases hs : N ≤ 4 * 10 ^ 18
  · obtain ⟨p, q, hp, hq, hpq⟩ := leaf_goldbach_4e18 N hE h4 hs
    refine ⟨p, q, hp, hq.pos, hpq.symm, ?_⟩
    simp [bigOmega, Nat.primeFactorsList_prime hq]
  · push_neg at hs
    obtain ⟨p, η, hp, hsq, hcop, hpη⟩ := leaf_hathi_johnston N hE (by omega)
    have hη0 : 0 < η := by
      rcases Nat.eq_zero_or_pos η with h | h
      · exact absurd (h ▸ hsq) not_squarefree_zero
      · exact h
    have hlt : (η : ℝ) < X2v3 :=
      lt_of_le_of_lt (by exact_mod_cast (by omega : η ≤ N)) hX
    exact ⟨p, η, hp, hη0, hpη, leaf_lemma35_count hsq hcop hlt⟩

/-- The sieve range, from leaves 4 and 5: every even N ≥ X₂ is a prime plus a number with at
most M − 1 = 39 prime factors, proof of Theorem 1.3, pp. 13 to 14. -/
theorem sieve_range (N : ℕ) (hE : Even N) (hX : X2v3 ≤ (N : ℝ)) :
    PrimePlusAlmostPrime 39 N := by
  have hpos := leaf_theorem42_positive N hE hX
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have hN : 1 ≤ N := by
    by_contra h
    push_neg at h
    have h0 : N = 0 := by omega
    subst h0
    have : (0 : ℝ) < X2v3 := Real.exp_pos _
    simp at hX
    linarith
  obtain ⟨p, hp, hNa, ha0, hO⟩ := leaf_sifted_omega N hN a ha
  exact ⟨p, a, hp, ha0, hNa, hO⟩

/-- Theorem 1.3 of P0019 v3, the same statement as `LeanLab.AlmostPrimes.johnston_starichkova`,
proved from the five leaves. -/
theorem johnston_starichkova_of_split :
    ∀ N : ℕ, Even N → 4 ≤ N → PrimePlusAlmostPrime 395 N := by
  intro N hE h4
  by_cases hX : (N : ℝ) < X2v3
  · exact lemma35 N hE h4 hX
  · push_neg at hX
    obtain ⟨p, m, hp, hm, hN, hO⟩ := sieve_range N hE hX
    exact ⟨p, m, hp, hm, hN, hO.trans (by norm_num)⟩

/-- Type check against the cited statement: both are proofs of the same proposition. -/
theorem johnston_starichkova_of_split_eq_type :
    @johnston_starichkova_of_split = @LeanLab.AlmostPrimes.johnston_starichkova := rfl

end LeanLab.AlmostPrimes.Burst4Split
