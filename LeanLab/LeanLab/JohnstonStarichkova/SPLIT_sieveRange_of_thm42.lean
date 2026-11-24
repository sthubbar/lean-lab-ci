/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, page 13, proof of Theorem 1.3.
SPLIT of sieveRange_of_thm42 from DecompJ274.lean, ROUTE BURST S98 burst-20261122.
The sieve positivity S(A, P(z)) > 0 with z = N^(1/40) is split from the elementary
step that a number below N with no prime factor below N^(1/40) has at most 39 prime
factors, which is proved here. The range of SieveRange starts at
X2 = exp(exp 7.816) from Lemma34.lean, from arXiv v1 and v2, while v3 states the sieve
only for N at least exp(exp 7.9), so the gap range is a separate leaf.
AI wrote this Lean code.
-/
import LeanLab.JohnstonStarichkova.DecompJ274

namespace LeanLab.JohnstonStarichkova
open LeanLab.AlmostPrimes

/-- LEAF: P0019 v3 page 13, proof of Theorem 1.3, Theorem 4.2 applied with
(Y0, α1, α2, C) = (7.9, 7, 2, 3.98) from display (4.6), u0 = 400, δ = 1.3,
α = 0.25, M = 40, z = N^(1/40): S(A, P(z)) > 0 for every even N ≥ exp(exp 7.9),
where A = {N - p : p < N prime}. Positivity of the sifted sum gives a prime p < N
with every prime factor q of N - p at least z, written here as N ≤ q^40.
Class HARD. -/
theorem sieve_positive_v3 (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    ∃ p : ℕ, p.Prime ∧ p < N ∧ ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40 := by
  sorry

/-- LEAF: P0019 arXiv v1 and v2, proof of Theorem 1.3, the same Theorem 4.2 sieve
positivity S(A, P(z)) > 0 with z = N^(1/40), on the range
exp(exp 7.816) ≤ N < exp(exp 7.9) that the SieveRange statement of Lemma34.lean
covers but v3 does not. v3 page 13 only claims N ≥ exp(exp 7.9), so this leaf rests on
the earlier versions, with their parameters, and is a QUESTION against v3.
Class HARD. -/
theorem sieve_positive_gap (N : ℕ) (hN : Even N) (hlo : X2 ≤ N)
    (hhi : (N : ℝ) < Real.exp (Real.exp 7.9)) :
    ∃ p : ℕ, p.Prime ∧ p < N ∧ ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40 := by
  sorry

/-- P0019 page 13, last step of the proof of Theorem 1.3: an m with 0 < m < N whose
prime factors q all satisfy N ≤ q^40 has at most M - 1 = 39 prime factors. -/
theorem bigOmega_le_39_of_rough {N m : ℕ} (hm : 0 < m) (hmN : m < N)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → N ≤ q ^ 40) : bigOmega m ≤ 39 := by
  by_contra hc
  push_neg at hc
  set l := m.primeFactorsList with hl
  have hprod : l.prod = m := Nat.prod_primeFactorsList hm.ne'
  have hall : ∀ x ∈ l.map (· ^ 40), N ≤ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact h q (Nat.prime_of_mem_primeFactorsList hq) (Nat.dvd_of_mem_primeFactorsList hq)
  have h1 := List.pow_length_le_prod (l.map (· ^ 40)) N hall
  have hpow : ∀ l' : List ℕ, (l'.map (· ^ 40)).prod = l'.prod ^ 40 := by
    intro l'
    induction l' with
    | nil => simp
    | cons a t ih => simp [List.prod_cons, ih, mul_pow]
  rw [List.length_map, hpow, hprod] at h1
  have hlen : 40 ≤ l.length := hc
  have hN1 : 1 ≤ N := by omega
  have h2 : N ^ 40 ≤ N ^ l.length := Nat.pow_le_pow_right hN1 hlen
  have h3 : N ^ 40 ≤ m ^ 40 := h2.trans h1
  have h4 : N ≤ m := (Nat.pow_le_pow_iff_left (by norm_num)).mp h3
  omega

/-- From sieve positivity to a prime plus an almost prime with at most 39 factors. -/
theorem primePlus_of_sieve {N : ℕ}
    (h : ∃ p : ℕ, p.Prime ∧ p < N ∧ ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40) :
    PrimePlusAlmostPrime 39 N := by
  obtain ⟨p, hp, hpN, hq⟩ := h
  refine ⟨p, N - p, hp, by omega, by omega, ?_⟩
  have hp2 := hp.two_le
  exact bigOmega_le_39_of_rough (by omega) (by omega) hq

theorem sieveRange_of_thm42_split :
  (∃ Y0 α1 α2 C u0 δ α : ℝ, ∃ M : ℕ, ∃ X2 : ℝ,
    Y0 = 7.9 ∧ α1 = 7 ∧ α2 = 2 ∧ C = 3.98 ∧
    u0 = 400 ∧ δ = 1.3 ∧ α = 0.25 ∧ M = 40 ∧
    X2 = Real.exp (Real.exp 7.9)) →
  SieveRange := by
  intro _ N hN hX
  by_cases hhi : (N : ℝ) < Real.exp (Real.exp 7.9)
  · exact primePlus_of_sieve (sieve_positive_gap N hN hX hhi)
  · exact primePlus_of_sieve (sieve_positive_v3 N hN (not_lt.mp hhi))

end LeanLab.JohnstonStarichkova
