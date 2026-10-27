import LeanLab.RamareSaouter2003.Decomp126b

/-!
P0099, Lemma 9 on p. 28 and Lemma 10 on p. 29.
These are the two prime generation families used in Section 8.
AI wrote this Lean code. Binary Goldbach is OPEN.
The reductions are CONDITIONAL ON Lemma 8.
-/

namespace LeanLab.RamareSaouter2003.PrimeFamilies126

open LeanLab.RamareSaouter2003.Decomp126b

/-- One half-power congruence gives the Fermat congruence and the gcd
condition for the prime factor two. Lemmas 9 and 10, pp. 28 and 29. -/
theorem half_certificate {N : ℕ} (hOdd : Odd N) {a : ℤ}
    (hhalf : Int.ModEq (N : ℤ) (a ^ ((N - 1) / 2)) (-1)) :
    Int.ModEq (N : ℤ) (a ^ (N - 1)) 1 ∧ Int.gcd (a ^ ((N - 1) / 2) - 1) N = 1 := by
  have heven : Even (N - 1) := by
    obtain ⟨k, hk⟩ := hOdd
    refine ⟨k, ?_⟩
    omega
  have hexp : (N - 1) / 2 * 2 = N - 1 := Nat.div_mul_cancel (even_iff_two_dvd.mp heven)
  constructor
  · have hh := hhalf.pow 2
    rw [← pow_mul, hexp] at hh
    simpa using hh
  · have hh := hhalf.sub (Int.ModEq.refl 1)
    have heq : (a ^ ((N - 1) / 2) - 1) % (N : ℤ) = (-2) % (N : ℤ) := by
      simpa only [Int.ModEq, show (-1 : ℤ) - 1 = -2 by norm_num] using hh
    have hg : Int.gcd (a ^ ((N - 1) / 2) - 1) N = Int.gcd (-2) N := by
      rw [← Int.gcd_emod (a ^ ((N - 1) / 2) - 1) (N : ℤ), heq, Int.gcd_emod]
    rw [hg]
    change Nat.gcd 2 N = 1
    exact hOdd.coprime_two_left

/-- CITED. Lemma 9, p. 28. The positive exponent makes F = 2^k an even
known factor. The decomposition of R defines the paper's s and r. -/
def lemma9_stmt : Prop := ∀ N R k s r : ℕ,
    1 ≤ k → Odd R → N % 10 = 3 → N = 2 ^ k * R + 1 →
    R = 2 ^ (k + 1) * s + r → r < 2 ^ (k + 1) → N ≤ 2 ^ (3 * k + 1) →
    Int.ModEq (N : ℤ) ((5 : ℤ) ^ ((N - 1) / 2)) (-1) →
    (N.Prime ↔ s = 0 ∨ ¬ IsSquare ((r : ℤ) ^ 2 - 8 * s))

/-- CITED. Lemma 10, p. 29, including the stated quotient and remainder
R = 4ps + r. -/
def lemma10_stmt : Prop := ∀ N R p s r : ℕ,
    p.Prime → Nat.Coprime (2 * p) R → N = 2 * p * R + 1 →
    R = 4 * p * s + r → r < 4 * p → N ≤ 16 * p ^ 3 →
    (∃ a : ℤ, Int.ModEq (N : ℤ) (a ^ ((N - 1) / 2)) (-1) ∧
      Int.gcd (a ^ ((N - 1) / p) - 1) N = 1) →
    (N.Prime ↔ s = 0 ∨ ¬ IsSquare ((r : ℤ) ^ 2 - 8 * s))

/-- Lemma 9 from Lemma 8. CONDITIONAL ON the cited Lemma 8. -/
theorem lemma9_of_lemma8 (h8 : lemma8_stmt) : lemma9_stmt := by
  intro N R k s r hk hRodd hmod hN hR hr hbound hhalf
  have hN2 : 2 ≤ N := by omega
  have hOdd : Odd N := Nat.odd_iff.mpr (by omega)
  have hFdvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hF : Even (2 ^ k) := even_iff_two_dvd.mpr hFdvd
  have hFpos : 0 < 2 ^ k := by positivity
  have hF2 : 2 ≤ 2 ^ k := by
    have hh : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    simpa using hh
  have hcop : Nat.Coprime R (2 ^ k) := hRodd.coprime_two_right.pow_right k
  have hN8 : N = R * 2 ^ k + 1 := by nlinarith [hN]
  have hR8 : R = 2 * 2 ^ k * s + r := by
    rw [pow_succ] at hR
    nlinarith [hR]
  have hr8 : r < 2 * 2 ^ k := by rw [pow_succ] at hr; nlinarith
  have hpow : 2 ^ (3 * k + 1) = 2 * (2 ^ k) ^ 3 := by
    rw [show 3 * k + 1 = k * 3 + 1 by omega, pow_add, pow_mul]
    ring
  rw [hpow] at hbound
  have hstrict : N < 2 * (2 ^ k) ^ 3 := by
    obtain ⟨t, ht⟩ := hOdd
    omega
  have hc := half_certificate hOdd hhalf
  apply h8 N R (2 ^ k) s r hN2 hF2 hF hcop hOdd hN8 hR8 hr8 hstrict
  refine ⟨5, hc.1, ?_⟩
  intro q hq hqF
  have hq2 : q ∣ 2 := hq.dvd_of_dvd_pow hqF
  have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2
  subst q
  exact hc.2

/-- Lemma 10 from Lemma 8. CONDITIONAL ON the cited Lemma 8. -/
theorem lemma10_of_lemma8 (h8 : lemma8_stmt) : lemma10_stmt := by
  intro N R p s r hp hcop hN hR hr hbound hcert
  obtain ⟨a, hhalf, hgp⟩ := hcert
  have hp2 : 2 ≤ p := hp.two_le
  have hR0 : 0 < R := by
    by_contra h
    have hz : R = 0 := by omega
    rw [hz] at hcop
    simp only [Nat.coprime_zero_right] at hcop
    nlinarith
  have hN2 : 2 ≤ N := by nlinarith [mul_pos (show 0 < 2 * p by omega) hR0]
  have hOdd : Odd N := by
    refine ⟨p * R, ?_⟩
    nlinarith [hN]
  have hF2 : 2 ≤ 2 * p := by omega
  have hF : Even (2 * p) := even_iff_two_dvd.mpr ⟨p, rfl⟩
  have hN8 : N = R * (2 * p) + 1 := by nlinarith [hN]
  have hR8 : R = 2 * (2 * p) * s + r := by nlinarith [hR]
  have hr8 : r < 2 * (2 * p) := by omega
  have hstrict : N < 2 * (2 * p) ^ 3 := by
    have hb : N < 16 * p ^ 3 := by
      obtain ⟨t, ht⟩ := hOdd
      omega
    nlinarith [hb]
  have hc := half_certificate hOdd hhalf
  apply h8 N R (2 * p) s r hN2 hF2 hF hcop.symm hOdd hN8 hR8 hr8 hstrict
  refine ⟨a, hc.1, ?_⟩
  intro q hq hqF
  rcases hq.dvd_mul.mp hqF with hq2 | hqp
  · have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2
    subst q
    exact hc.2
  · have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    subst q
    exact hgp

/-- Lemma 9, CONDITIONAL ON the external Pocklington leaf through Lemma 8. -/
theorem lemma9 : lemma9_stmt := lemma9_of_lemma8 Decomp126b.lemma8

/-- Lemma 10, CONDITIONAL ON the external Pocklington leaf through Lemma 8. -/
theorem lemma10 : lemma10_stmt := lemma10_of_lemma8 Decomp126b.lemma8

end LeanLab.RamareSaouter2003.PrimeFamilies126
