import Mathlib

/-!
# R-0020 Hilbert primes: Goldbach in the 1 mod 4 monoid

Route R-0020, unit U-1162, PC run 20261020T0503Z-11094. AI wrote this Lean code.

The Hilbert numbers are the n with n % 4 = 1, closed under multiplication. A Hilbert prime is
a Hilbert number above 1 with no factorization into two Hilbert numbers above 1.

* `hilbertPrime_iff`: a Hilbert prime is exactly an ordinary prime p ≡ 1 mod 4 or a product
  p * q of two ordinary primes p, q ≡ 3 mod 4.
* `rho`: ρ(n) = Σ_{d ∣ n} χ₄(d). For distinct odd primes p, q with p * q ≡ 1 mod 4,
  `hilbertPrime_mul_iff_rho`: p * q is a Hilbert prime iff ρ(p q) = 0.
* `parity_witness`: 21 = 3 * 7 and 105 = 3 * 5 * 7 are both Hilbert numbers with ρ = 0,
  one is a Hilbert prime and the other is not, so below N^{1/3}-roughness ρ alone cannot see
  Hilbert primality; the split is an Ω = 2 against Ω = 3 parity split.

Binary Goldbach itself is OPEN; this file proves nothing about it.
-/

namespace LeanLab.Routes.R0020

/-- A Hilbert prime: n ≡ 1 mod 4, n > 1, and no factorization into two Hilbert numbers above 1. -/
def HilbertPrime (n : ℕ) : Prop :=
  n % 4 = 1 ∧ 1 < n ∧ ∀ a b : ℕ, a % 4 = 1 → b % 4 = 1 → a * b = n → a = 1 ∨ b = 1

lemma mod4_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd := hp.eq_one_or_self_of_dvd 2
  have : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hp with h | h
    · exact absurd h h2
    · exact h
  omega

lemma mul_mod4 (a b : ℕ) : (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Nat.mul_mod a b 4

/-- Forward direction: a Hilbert prime is a prime or a product of two primes ≡ 3 mod 4. -/
theorem hilbertPrime_cases {n : ℕ} (h : HilbertPrime n) :
    n.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ n = p * q := by
  obtain ⟨h1, hgt, hirr⟩ := h
  by_cases hn : n.Prime
  · exact Or.inl hn
  right
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ : p ∣ n := Nat.minFac_dvd n
  have hp2 : p ≠ 2 := by
    intro h2; rw [h2] at hm; omega
  have hm1 : 1 < m := by
    rcases Nat.lt_or_ge 1 m with h | h
    · exact h
    · interval_cases m
      · omega
      · exact absurd (by rw [hm, mul_one]; exact hp) hn
  have hpm : p % 4 = 3 := by
    rcases mod4_odd_prime hp hp2 with h | h
    · exfalso
      have hm4 : m % 4 = 1 := by
        have := mul_mod4 p m; rw [← hm, h1, h] at this
        have : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
        interval_cases hh : m % 4 <;> omega
      rcases hirr p m h hm4 hm.symm with h' | h'
      · exact hp.one_lt.ne' h'
      · omega
    · exact h
  have hm3 : m % 4 = 3 := by
    have := mul_mod4 p m; rw [← hm, h1, hpm] at this
    have : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hh : m % 4 <;> omega
  by_cases hmp : m.Prime
  · exact ⟨p, m, hp, hmp, hpm, hm3, hm⟩
  exfalso
  set q := m.minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  obtain ⟨k, hk⟩ : q ∣ m := Nat.minFac_dvd m
  have hk1 : 1 < k := by
    rcases Nat.lt_or_ge 1 k with h | h
    · exact h
    · interval_cases k
      · omega
      · exact absurd (by rw [hk, mul_one]; exact hq) hmp
  have hq2 : q ≠ 2 := by
    intro h2; rw [h2] at hk; omega
  have hq3 : q % 4 = 3 := by
    rcases mod4_odd_prime hq hq2 with h | h
    · exfalso
      -- q ≡ 1 divides m, so p * k ≡ 1 and n = q * (p * k)
      have hk3 : k % 4 = 3 := by
        have := mul_mod4 q k; rw [← hk, hm3, h] at this
        have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
        interval_cases hh : k % 4 <;> omega
      have hpk : (p * k) % 4 = 1 := by rw [mul_mod4, hpm, hk3]
      rcases hirr q (p * k) h hpk (by rw [hm, hk]; ring) with h' | h'
      · exact hq.one_lt.ne' h'
      · have : 1 < p * k := by nlinarith [hp.one_lt]
        omega
    · exact h
  have hk4 : k % 4 = 1 := by
    have := mul_mod4 q k; rw [← hk, hm3, hq3] at this
    have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hh : k % 4 <;> omega
  have hpq : (p * q) % 4 = 1 := by rw [mul_mod4, hpm, hq3]
  rcases hirr (p * q) k hpq hk4 (by rw [hm, hk]; ring) with h' | h'
  · have : 1 < p * q := by nlinarith [hp.one_lt, hq.one_lt]
    omega
  · omega

/-- Reverse direction for a product of two primes ≡ 3 mod 4. -/
theorem hilbertPrime_of_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) : HilbertPrime (p * q) := by
  refine ⟨by rw [mul_mod4, hp3, hq3], by nlinarith [hp.one_lt, hq.one_lt], ?_⟩
  intro a b ha hb hab
  have hadvd : a ∣ p * q := ⟨b, hab.symm⟩
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.mp hadvd
  have hpq : 0 < p * q := by nlinarith [hp.one_lt, hq.one_lt]
  rcases (Nat.dvd_prime hp).mp hy with hy' | hy' <;>
    rcases (Nat.dvd_prime hq).mp hz with hz' | hz' <;> rw [hy', hz'] at hyz
  · left; rw [← hyz]
  · exfalso; rw [← hyz, one_mul] at ha; omega
  · exfalso; rw [← hyz, mul_one] at ha; omega
  · right
    rw [← hyz] at hab
    have : p * q * b = p * q * 1 := by rw [mul_one]; exact hab
    exact Nat.eq_of_mul_eq_mul_left hpq this

/-- Reverse direction for a prime. -/
theorem hilbertPrime_of_prime {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) : HilbertPrime p := by
  refine ⟨hp1, hp.one_lt, ?_⟩
  intro a b _ _ hab
  rcases (Nat.dvd_prime hp).mp ⟨b, hab.symm⟩ with h | h
  · exact Or.inl h
  · right; subst h
    have : a * b = a * 1 := by rw [mul_one]; exact hab
    exact Nat.eq_of_mul_eq_mul_left hp.pos this

/-- The characterization of Hilbert primes. -/
theorem hilbertPrime_iff (n : ℕ) :
    HilbertPrime n ↔ n % 4 = 1 ∧
      (n.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ n = p * q) := by
  constructor
  · intro h; exact ⟨h.1, hilbertPrime_cases h⟩
  · rintro ⟨h1, hp | ⟨p, q, hp, hq, hp3, hq3, rfl⟩⟩
    · exact hilbertPrime_of_prime hp h1
    · exact hilbertPrime_of_mul hp hq hp3 hq3

/-- χ₄ on naturals, as an integer: 1 on 1 mod 4, -1 on 3 mod 4, 0 on evens. -/
def chi4 (n : ℕ) : ℤ := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

/-- ρ(n) = Σ_{d ∣ n} χ₄(d), a quarter of the number of representations of n as a sum of two squares. -/
def rho (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi4 d

lemma divisors_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p * q).divisors = {1, p, q, p * q} := by
  rw [Nat.divisors_mul, hp.divisors, hq.divisors]
  ext x
  simp only [Finset.mem_mul, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rcases hy with h | h <;> rcases hz with h' | h' <;> simp [h, h']
  · rintro (h | h | h | h) <;> rw [h]
    · exact ⟨1, Or.inl rfl, 1, Or.inl rfl, by ring⟩
    · exact ⟨p, Or.inr rfl, 1, Or.inl rfl, by ring⟩
    · exact ⟨1, Or.inl rfl, q, Or.inr rfl, by ring⟩
    · exact ⟨p, Or.inr rfl, q, Or.inr rfl, rfl⟩

/-- For distinct primes p, q both odd, ρ(p q) = (1 + χ₄ p)(1 + χ₄ q). -/
theorem rho_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    rho (p * q) = (1 + chi4 p) * (1 + chi4 q) := by
  unfold rho
  rw [divisors_mul_primes hp hq hpq]
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hq1 : q ≠ 1 := hq.one_lt.ne'
  have hpq1 : p * q ≠ 1 := by
    intro h; exact hp1 (Nat.eq_one_of_mul_eq_one_right h)
  have hpqp : p * q ≠ p := by
    intro h
    have : p * q = p * 1 := by rw [mul_one]; exact h
    exact hq1 (Nat.eq_of_mul_eq_mul_left hp.pos this)
  have hpqq : p * q ≠ q := by
    intro h
    have : p * q = 1 * q := by rw [one_mul]; exact h
    exact hp1 (Nat.eq_of_mul_eq_mul_right hq.pos this)
  rw [Finset.sum_insert (by simp [Ne.symm hp1, Ne.symm hq1, Ne.symm hpq1]),
    Finset.sum_insert (by simp [hpq, Ne.symm hpqp]),
    Finset.sum_insert (by simp [Ne.symm hpqq]), Finset.sum_singleton]
  have hp' := mod4_odd_prime hp hp2
  have hq' := mod4_odd_prime hq hq2
  have hpq4 : (p * q) % 4 = ((p % 4) * (q % 4)) % 4 := mul_mod4 p q
  unfold chi4
  rcases hp' with h | h <;> rcases hq' with h' | h' <;> simp [h, h', hpq4]

/-- For distinct odd primes with p q ≡ 1 mod 4, p q is a Hilbert prime iff ρ(p q) = 0. -/
theorem hilbertPrime_mul_iff_rho {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (h1 : (p * q) % 4 = 1) :
    HilbertPrime (p * q) ↔ rho (p * q) = 0 := by
  rw [rho_mul_primes hp hq hpq hp2 hq2]
  have hp' := mod4_odd_prime hp hp2
  have hq' := mod4_odd_prime hq hq2
  have hpq4 := mul_mod4 p q
  constructor
  · intro h
    rcases hilbertPrime_cases h with hpr | ⟨a, b, ha, hb, ha3, hb3, hab⟩
    · exfalso
      rcases (Nat.dvd_prime hpr).mp (dvd_mul_right p q) with h' | h'
      · exact hp.one_lt.ne' h'
      · have : p * q = p * 1 := by rw [mul_one]; exact h'.symm
        exact hq.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hp.pos this)
    · -- p divides a * b, so p = a or p = b, and then the other matches by cancellation
      have hpa : p ∣ a * b := ⟨q, hab.symm⟩
      have hp3 : p % 4 = 3 := by
        rcases (Nat.Prime.dvd_mul hp).mp hpa with h' | h'
        · rw [(Nat.prime_dvd_prime_iff_eq hp ha).mp h']; exact ha3
        · rw [(Nat.prime_dvd_prime_iff_eq hp hb).mp h']; exact hb3
      have hq3 : q % 4 = 3 := by
        rw [hpq4, hp3] at h1
        rcases hq' with h' | h'
        · rw [h'] at h1; norm_num at h1
        · exact h'
      unfold chi4; simp [hp3, hq3]
  · intro h
    rcases hp' with hp1 | hp3
    · exfalso
      have hq1 : q % 4 = 1 := by
        rw [hpq4, hp1] at h1
        rcases hq' with h' | h'
        · exact h'
        · rw [h'] at h1; norm_num at h1
      unfold chi4 at h; simp [hp1, hq1] at h
    · have hq3 : q % 4 = 3 := by
        rw [hpq4, hp3] at h1
        rcases hq' with h' | h'
        · rw [h'] at h1; norm_num at h1
        · exact h'
      exact hilbertPrime_of_mul hp hq hp3 hq3

/-- The parity witness: 21 and 105 are Hilbert numbers with ρ = 0; 21 is a Hilbert prime,
105 = 21 * 5 is not. -/
theorem parity_witness :
    rho 21 = 0 ∧ rho 105 = 0 ∧ HilbertPrime 21 ∧ ¬ HilbertPrime 105 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · have := hilbertPrime_of_mul (p := 3) (q := 7) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    simpa using this
  · intro h
    rcases h.2.2 21 5 (by norm_num) (by norm_num) (by norm_num) with h' | h' <;> omega

/-- Vacuity: the hypotheses of `hilbertPrime_mul_iff_rho` hold for p = 3, q = 7. -/
theorem vacuity : HilbertPrime (3 * 7) ∧ rho (3 * 7) = 0 := by
  have h := hilbertPrime_mul_iff_rho (p := 3) (q := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hh : HilbertPrime (3 * 7) :=
    hilbertPrime_of_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hh, h.mp hh⟩

end LeanLab.Routes.R0020
