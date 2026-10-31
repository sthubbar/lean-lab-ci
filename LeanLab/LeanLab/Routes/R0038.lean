import Mathlib

/-
# R-0038, T3 MOONSHOT: the large prime factor ladder for N - p, and the cofactor at theta = 1

Unit U-1349, PC run 20261021T0403Z-14344. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it. KNOWN IN SUBSTANCE:
Goldfeld 1969, Hooley 1973, Fouvry 1985, Baker-Harman 1998 for p + a; Huang-Li arXiv 2005.03811.

Write n = N - p = a * q with q = P⁺(n) the largest prime factor and a the cofactor. Level of
distribution D = N^ϑ for A = {N - p} gives, by Chebyshev's identity log n = Σ_{d ∣ n} Λ(d),
many p with P⁺(N - p) > N^ϑ' (Goldfeld at ϑ = 1/2); under a level 1 - ε hypothesis, many p with
cofactor a ≤ N^ε. Binary Goldbach is cofactor a = 1. The parity barrier sits exactly there:
on the Selberg fake set {λ(n) = +1}, every n = a * q has Ω(a) odd, so a ≠ 1.

* `large_prime_factor_unique`: n ≤ N has at most one prime factor q with q² > N.
* `large_prime_factor_sq_not_dvd`: such a q divides n exactly once.
* `card_large_primeFactors_le_one`, `sum_log_large_le`: the deterministic core of Goldfeld's count.
* `prime_iff_cofactor_one`: for n = a * q, q prime, n is prime iff a = 1.
* `liouville_mul_prime`: (-1)^Ω(a q) = -(-1)^Ω(a).
* `fake_cofactor_ne_one`: on {(-1)^Ω(n) = 1}, the cofactor of a prime is never 1: the parity wall.
* `goldbach_of_cofactor_one`: cofactor 1 for N - p is a Goldbach representation.
-/

namespace LeanLab.Routes.R0038

open ArithmeticFunction Finset

/-- A positive n ≤ N has at most one prime factor q with N < q². -/
theorem large_prime_factor_unique {n N p q : ℕ} (hn0 : 0 < n) (hnN : n ≤ N)
    (hp : p.Prime) (hq : q.Prime) (hpN : N < p * p) (hqN : N < q * q)
    (hpd : p ∣ n) (hqd : q ∣ n) : p = q := by
  by_contra hne
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  have hpq : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
  have hle : p * q ≤ n := Nat.le_of_dvd hn0 hpq
  rcases le_total p q with h | h
  · have : p * p ≤ p * q := Nat.mul_le_mul_left p h
    omega
  · have : q * q ≤ p * q := Nat.mul_le_mul_right q h
    omega

/-- A prime q with N < q² divides a positive n ≤ N at most once. -/
theorem large_prime_factor_sq_not_dvd {n N q : ℕ} (hn0 : 0 < n) (hnN : n ≤ N)
    (hqN : N < q * q) : ¬ q * q ∣ n := by
  intro h
  have := Nat.le_of_dvd hn0 h
  omega

/-- The prime factors q of n with N < q² form a set of size at most one. -/
theorem card_large_primeFactors_le_one {n N : ℕ} (hn0 : 0 < n) (hnN : n ≤ N) :
    ((n.primeFactors).filter (fun q => N < q * q)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at ha hb
  exact large_prime_factor_unique hn0 hnN ha.1.1 hb.1.1 ha.2 hb.2 ha.1.2.1 hb.1.2.1

/-- Goldfeld's deterministic core: the log-mass of prime factors above √N of one n ≤ N is at
most log N, and it is zero unless P⁺(n) > √N. Summed over n = N - p this turns the Type I
deficit Σ log(N - p) - Σ_{d ≤ √N} Λ(d) π(N; d, N) into a count of p with P⁺(N - p) > √N. -/
theorem sum_log_large_le {n N : ℕ} (hn0 : 0 < n) (hnN : n ≤ N) :
    ∑ q ∈ (n.primeFactors).filter (fun q => N < q * q), Real.log q
      ≤ Real.log N * ((n.primeFactors).filter (fun q => N < q * q)).card := by
  rw [mul_comm, ← nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro q hq
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.1.1.pos
  have hqn : q ≤ N := le_trans (Nat.le_of_dvd hn0 hq.1.2.1) hnN
  exact Real.log_le_log hq0 (by exact_mod_cast hqn)

/-- For n = a * q with q prime, n is prime iff the cofactor a is 1. -/
theorem prime_iff_cofactor_one {a q : ℕ} (hq : q.Prime) : (a * q).Prime ↔ a = 1 := by
  rw [Nat.prime_mul_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact absurd h hq.one_lt.ne'
    · exact h
  · intro h
    exact Or.inr ⟨hq, h⟩

/-- Liouville flips sign on multiplying by a prime: (-1)^Ω(a q) = -(-1)^Ω(a). -/
theorem liouville_mul_prime {a q : ℕ} (ha : a ≠ 0) (hq : q.Prime) :
    ((-1 : ℤ) ^ cardFactors (a * q)) = -((-1 : ℤ) ^ cardFactors a) := by
  rw [cardFactors_mul ha hq.ne_zero, cardFactors_apply_prime hq, pow_succ]
  ring

/-- The parity wall: on Selberg's fake set {(-1)^Ω(n) = +1}, an element n = a * q with q prime
never has cofactor a = 1, so it never is a prime. Every level-of-distribution argument that
cannot tell A from this half of A stops at a cofactor with Ω(a) odd. -/
theorem fake_cofactor_ne_one {a q : ℕ} (ha : a ≠ 0) (hq : q.Prime)
    (hfake : ((-1 : ℤ) ^ cardFactors (a * q)) = 1) : a ≠ 1 := by
  rintro rfl
  rw [liouville_mul_prime one_ne_zero hq] at hfake
  simp at hfake

/-- Cofactor one for N - p is a Goldbach representation of N. -/
theorem goldbach_of_cofactor_one {N p q : ℕ} (hp : p.Prime) (hpN : p ≤ N) (hq : q.Prime)
    (hcof : N - p = 1 * q) : ∃ p' q', p'.Prime ∧ q'.Prime ∧ p' + q' = N :=
  ⟨p, q, hp, hq, by omega⟩

/-- Vacuity: N = 15, n = 15 = 3 * 5, the prime 5 has 5² > 15 and divides 15. -/
example : (5 : ℕ).Prime ∧ 15 < 5 * 5 ∧ 5 ∣ 15 := by norm_num

/-- Vacuity of the fake set lemma: 15 = 3 * 5 has Ω = 2, (-1)^2 = 1, cofactor 3 ≠ 1. -/
example : ((-1 : ℤ) ^ cardFactors (3 * 5)) = 1 := by
  rw [liouville_mul_prime (by norm_num) (by norm_num : (5 : ℕ).Prime),
    cardFactors_apply_prime (by norm_num : (3 : ℕ).Prime)]
  norm_num

/-- Vacuity of the Goldbach link: N = 100, p = 97, N - p = 3 = 1 * 3. -/
example : ∃ p' q', p'.Prime ∧ q'.Prime ∧ p' + q' = 100 :=
  goldbach_of_cofactor_one (by norm_num : (97 : ℕ).Prime) (by norm_num)
    (by norm_num : (3 : ℕ).Prime) (by norm_num)

end LeanLab.Routes.R0038
