/-
P0072 A. Togashi and S. Uchiyama 1964, On the representation of large even integers as sums
of two almost primes I, J. Fac. Sci. Hokkaido Univ. Ser. I 18, pp. 60 to 68. Lab copy
papers/P0072.pdf and papers/P0072.txt. Unit U-1544, run 20261026T0808Z-17522, type DECOMPOSE,
track T1, file a of three.

Target of the three files: the Section 3 summed upper sieve bound, the hypothesis
`TogashiUchiyamaScale.UpperSieveInput`, Σ_{z<q≤z₁} S(q) ≤ I(ε) M + 3εM, which is one of the two
remaining inputs of `TogashiUchiyamaScale.section5_of_two_sieve_inputs`.

This file a: Lemma 1, p. 61, and the Selberg step, pp. 63 to 64,
S(q) ≤ 2φ(N)/(q W_q) + R_q. The sieve problem for S(q) is a `SelbergSieve` whose support is
the set of values a_n = n(N - n), n in `Aq N q`, with multiplicity weights, density
ν(p) = 2/p and sifting range the odd primes p ∤ N with p⁶ ≤ N. The Λ² bound itself is the
lab's PROVED `LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple`, so the step reduces to
bookkeeping leaves.

Leaves, all OPEN: `card_rootsMod`, `dvd_iff_mod_mem_rootsMod`, `card_progression_moebius`,
`card_mul_mod_eq`, `sum_moebius_div_eq_totient`, `sum_abs_moebius_divisors`,
`siftedSum_sieveQ`, `multSum_sieveQ`, `nuT_of_squarefree`, `sqfree_coprime_mul_q`,
`selbergTerms_sieveQ`, `sum_six_pow_omega_le`.
Assemblies, CONDITIONAL ON those leaves, no sorry of their own:
`card_progression_coprime`; `lemma1`, Lemma 1 with B_N = 2^{ν(N)}; `rem_sieveQ_le`;
`Sq_le_selberg`, the first display of Section 3 with an explicit R_q.

AI-written Lean code, Claude, 2026-10-26. Binary Goldbach is OPEN; nothing here is progress
on it.
-/
import Mathlib
import LeanLab.PNTSieve.SelbergBounds
import LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.AlmostPrimeSums.Decomp1544a
open LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5

/-! ### Lemma 1, p. 61 -/

/-- The residues r mod d with d ∣ r(N - r), computed in ℤ. -/
def rootsMod (N d : ℕ) : Finset ℕ :=
  (range d).filter (fun r => (d : ℤ) ∣ (r : ℤ) * ((N : ℤ) - r))

/-- LEAF. Unit U-1544. For squarefree d coprime to N the congruence r(N - r) ≡ 0 mod d has
exactly 2^{ν(d)} solutions mod d: by the Chinese remainder theorem, r ≡ 0 or r ≡ N mod each
p ∣ d, and these differ since p ∤ N. This is the count ω(d) = 2^{ν(d)} of Lemma 1, p. 61. -/
theorem card_rootsMod {N d : ℕ} (hd : Squarefree d) (hdN : d.Coprime N) :
    (rootsMod N d).card = 2 ^ ω d := by
  sorry

/-- LEAF. Unit U-1544. For 0 < d and n ≤ N, d ∣ n(N - n) iff n mod d is a root, since
n ≡ n mod d and the natural subtraction N - n is the integer one. Lemma 1, p. 61. -/
theorem dvd_iff_mod_mem_rootsMod {N d n : ℕ} (hd : 0 < d) (hn : n ≤ N) :
    d ∣ n * (N - n) ↔ n % d ∈ rootsMod N d := by
  sorry

/-- LEAF. Unit U-1544. Möbius inclusion and exclusion over e ∣ N for the condition (n, N) = 1:
#{1 ≤ n ≤ N : (n, N) = 1, n mod d = r} = Σ_{e ∣ N} μ(e) #{1 ≤ m ≤ N/e : em mod d = r}.
Lemma 1, p. 61, the step behind R(d). -/
theorem card_progression_moebius (N d r : ℕ) :
    (((Aset N).filter (fun n => n % d = r)).card : ℝ) =
      ∑ e ∈ N.divisors, (μ e : ℝ) *
        (((Icc 1 (N / e)).filter (fun m => (e * m) % d = r)).card : ℝ) := by
  sorry

/-- LEAF. Unit U-1544. If e is coprime to d > 0 and r < d, then m ↦ em mod d permutes the
residues, so #{1 ≤ m ≤ M : em mod d = r} is ⌊M/d⌋ or ⌈M/d⌉ and differs from M/d by at most 1.
Lemma 1, p. 61. -/
theorem card_mul_mod_eq {d e r : ℕ} (M : ℕ) (hd : 0 < d) (hed : e.Coprime d) (hr : r < d) :
    |(((Icc 1 M).filter (fun m => (e * m) % d = r)).card : ℝ) - (M : ℝ) / d| ≤ 1 := by
  sorry

/-- LEAF. Unit U-1544. φ(N) = Σ_{e ∣ N} μ(e) N/e, Möbius inversion of Σ_{e ∣ N} φ(e) = N,
Mathlib `Nat.sum_totient`. Used in Lemma 1, p. 61. -/
theorem sum_moebius_div_eq_totient (N : ℕ) :
    ∑ e ∈ N.divisors, (μ e : ℝ) * ((N / e : ℕ) : ℝ) = N.totient := by
  sorry

/-- LEAF. Unit U-1544. Σ_{e ∣ N} |μ(e)| = 2^{ν(N)} for N ≥ 1: the squarefree divisors of N are
the subsets of its prime factors. This is the constant B_N = c 2^{ν(N)} of Lemma 1, p. 61. -/
theorem sum_abs_moebius_divisors {N : ℕ} (hN : N ≠ 0) :
    ∑ e ∈ N.divisors, |(μ e : ℝ)| = 2 ^ ω N := by
  sorry

/-- Assembly, CONDITIONAL ON `card_progression_moebius`, `card_mul_mod_eq`,
`sum_moebius_div_eq_totient`, `sum_abs_moebius_divisors`: for 0 < d coprime to N ≥ 1 and r < d,
|#{1 ≤ n ≤ N : (n, N) = 1, n mod d = r} - φ(N)/d| ≤ 2^{ν(N)}. Lemma 1, p. 61. -/
theorem card_progression_coprime {N d r : ℕ} (hN : 1 ≤ N) (hd : 0 < d) (hdN : d.Coprime N)
    (hr : r < d) :
    |(((Aset N).filter (fun n => n % d = r)).card : ℝ) - (N.totient : ℝ) / d| ≤ 2 ^ ω N := by
  rw [card_progression_moebius, ← sum_moebius_div_eq_totient, Finset.sum_div,
    ← Finset.sum_sub_distrib, ← sum_abs_moebius_divisors (by omega)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
  have heN : e ∣ N := Nat.dvd_of_mem_divisors he
  have hed : e.Coprime d := (Nat.Coprime.coprime_dvd_left heN hdN.symm)
  have h1 := card_mul_mod_eq (N / e) hd hed hr
  rw [show (μ e : ℝ) * (((Icc 1 (N / e)).filter (fun m => (e * m) % d = r)).card : ℝ) -
      (μ e : ℝ) * ((N / e : ℕ) : ℝ) / d = (μ e : ℝ) *
      ((((Icc 1 (N / e)).filter (fun m => (e * m) % d = r)).card : ℝ) - ((N / e : ℕ) : ℝ) / d)
      by ring, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) h1

/-- **Lemma 1**, p. 61, with B_N = 2^{ν(N)}: for squarefree d coprime to N ≥ 1,
S_d = #{1 ≤ n ≤ N : (n, N) = 1, d ∣ n(N - n)} satisfies
|S_d - 2^{ν(d)} φ(N)/d| ≤ 2^{ν(d)} 2^{ν(N)}.
Assembly, CONDITIONAL ON `card_rootsMod`, `dvd_iff_mod_mem_rootsMod` and the leaves of
`card_progression_coprime`. -/
theorem lemma1 {N d : ℕ} (hN : 1 ≤ N) (hd : Squarefree d) (hdN : d.Coprime N) :
    |(((Aset N).filter (fun n => d ∣ n * (N - n))).card : ℝ) -
        2 ^ ω d * (N.totient : ℝ) / d| ≤ 2 ^ ω d * 2 ^ ω N := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hle : ∀ n ∈ Aset N, n ≤ N := fun n hn => (mem_Aset.mp hn).2.1
  set A' := (Aset N).filter (fun n => d ∣ n * (N - n)) with hA'
  have hmaps : ∀ n ∈ A', n % d ∈ rootsMod N d := by
    intro n hn
    rw [hA', mem_filter] at hn
    exact (dvd_iff_mod_mem_rootsMod hd0 (hle n hn.1)).1 hn.2
  have hcard : A'.card = ∑ r ∈ rootsMod N d, (A'.filter (fun n => n % d = r)).card :=
    card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ r ∈ rootsMod N d,
      A'.filter (fun n => n % d = r) = (Aset N).filter (fun n => n % d = r) := by
    intro r hr
    ext n
    simp only [hA', mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, (dvd_iff_mod_mem_rootsMod hd0 (hle n h1)).2 (h3 ▸ hr)⟩, h3⟩
  have hroots : ((rootsMod N d).card : ℝ) = 2 ^ ω d := by
    rw [card_rootsMod hd hdN]; push_cast; ring
  rw [hcard, Nat.cast_sum, ← hroots,
    show ((rootsMod N d).card : ℝ) * (N.totient : ℝ) / d =
      ∑ r ∈ rootsMod N d, (N.totient : ℝ) / d by rw [sum_const, nsmul_eq_mul]; ring,
    ← Finset.sum_sub_distrib,
    show ((rootsMod N d).card : ℝ) * 2 ^ ω N = ∑ r ∈ rootsMod N d, (2 : ℝ) ^ ω N by
      rw [sum_const, nsmul_eq_mul]]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
  rw [hfib r hr]
  have hrd : r < d := by
    have := (mem_filter.mp hr).1
    exact mem_range.mp this
  exact card_progression_coprime hN hd0 hdN hrd

/-! ### The sieve problem for S(q), p. 63 -/

/-- The sifting primes: odd primes p ∤ N with p⁶ ≤ N, that is p ≤ z = N^{1/6}. For even N the
primes p ∣ N, 2 among them, never divide a_n with (n, N) = 1, so this is the paper's range. -/
def siftPrimes (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p ∧ p ^ 6 ≤ N ∧ ¬ p ∣ N)

lemma mem_siftPrimes {N p : ℕ} :
    p ∈ siftPrimes N ↔ p ≤ N ∧ p.Prime ∧ 2 < p ∧ p ^ 6 ≤ N ∧ ¬ p ∣ N := by
  simp [siftPrimes, Nat.lt_succ_iff]

/-- P(z), the product of the sifting primes. -/
def Pz (N : ℕ) : ℕ := ∏ p ∈ siftPrimes N, p

lemma Pz_ne_zero (N : ℕ) : Pz N ≠ 0 :=
  prod_ne_zero_iff.mpr (fun p hp => (mem_siftPrimes.1 hp).2.1.ne_zero)

lemma Pz_squarefree (N : ℕ) : Squarefree (Pz N) :=
  LeanLab.PNTSieve.Sieve.prodDistinctPrimes_squarefree _ (fun p hp => (mem_siftPrimes.1 hp).2.1)

lemma prime_dvd_Pz {N p : ℕ} (hp : p.Prime) (h : p ∣ Pz N) : p ∈ siftPrimes N := by
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  have hrp := (mem_siftPrimes.1 hr).2.1
  rwa [(Nat.prime_dvd_prime_iff_eq hp hrp).1 hpr]

/-- The n of S(q) before sifting: 1 ≤ n ≤ N, (n, N) = 1, q ∣ n(N - n). -/
def Aq (N q : ℕ) : Finset ℕ := (Aset N).filter (fun n => q ∣ n * (N - n))

/-- The density ν(d) = ∏_{p ∣ d} 2/p, which is ω(d)/d of Lemma 1 on squarefree d coprime to N. -/
def nuT : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (fun p => 2 / (p : ℝ))

lemma nuT_prime {p : ℕ} (hp : p.Prime) : nuT p = 2 / (p : ℝ) := by
  simp [nuT, hp.ne_zero, hp.primeFactors]

/-- The Selberg sieve problem for S(q): support the values a_n = n(N - n), n ∈ Aq N q, with
multiplicity weights; total mass X = 2φ(N)/q; density ν; sifting primes `siftPrimes N`;
level y. -/
def sieveQ (N q : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := (Aq N q).image (fun n => n * (N - n))
  prodPrimes := Pz N
  prodPrimes_squarefree := Pz_squarefree N
  weights := fun m => (((Aq N q).filter (fun n => n * (N - n) = m)).card : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := 2 * (N.totient : ℝ) / q
  nu := nuT
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => by rw [nuT_prime hp]; have := hp.pos; positivity
  nu_lt_one_of_prime := fun p hp hd => by
    have h2 := (mem_siftPrimes.1 (prime_dvd_Pz hp hd)).2.2.1
    rw [nuT_prime hp]
    have h2' : (2 : ℝ) < p := by exact_mod_cast h2
    rw [div_lt_one (by linarith)]; exact h2'
  level := y
  one_le_level := hy

/-- LEAF. Unit U-1544. For even N the sifted sum of `sieveQ` is S(q) of p. 63: the weights
count each n ∈ Aq N q once, and for (n, N) = 1 the condition (P(z), n(N - n)) = 1 is the
condition `sieved N n`, since a prime p ∣ N, 2 included, divides neither n nor N - n. -/
theorem siftedSum_sieveQ {N q : ℕ} (y : ℝ) (hy : 1 ≤ y) (hN : Even N) :
    BoundingSieve.siftedSum (s := (sieveQ N q y hy).toBoundingSieve) = ((Sq N q).card : ℝ) := by
  sorry

/-- LEAF. Unit U-1544. For q ∈ Qset N and d ∣ P(z), the mass of `sieveQ` on multiples of d is
#{n ∈ Aset N : dq ∣ n(N - n)}: the primes of d are below q, so (d, q) = 1 and
q ∣ a ∧ d ∣ a ↔ dq ∣ a. The count A_{dq} of Lemma 1 used on p. 63. -/
theorem multSum_sieveQ {N q d : ℕ} (y : ℝ) (hy : 1 ≤ y) (hq : q ∈ Qset N) (hd : d ∣ Pz N) :
    BoundingSieve.multSum (s := (sieveQ N q y hy).toBoundingSieve) d =
      (((Aset N).filter (fun n => d * q ∣ n * (N - n))).card : ℝ) := by
  sorry

/-- LEAF. Unit U-1544. On squarefree d, ν(d) = 2^{ν(d)}/d, the ratio ω(d)/d of Lemma 1, p. 61. -/
theorem nuT_of_squarefree {d : ℕ} (hd : Squarefree d) : nuT d = 2 ^ ω d / (d : ℝ) := by
  sorry

/-- LEAF. Unit U-1544. For q ∈ Qset N and d ∣ P(z): dq is squarefree, (dq, N) = 1 and q ∤ d,
because every prime p of d has p⁶ ≤ N < q⁶ and p ∤ N. Used for A_{dq} on p. 63. -/
theorem sqfree_coprime_mul_q {N q d : ℕ} (hq : q ∈ Qset N) (hd : d ∣ Pz N) :
    Squarefree (d * q) ∧ (d * q).Coprime N ∧ ¬ q ∣ d := by
  sorry

/-- LEAF. Unit U-1544. The Selberg terms of `sieveQ` are 1/f₁(l) = ∏_{p ∣ l} 2/(p - 2) for
l ∣ P(z): with ν(p) = 2/p, ν(p)/(1 - ν(p)) = 2/(p - 2). These are the terms μ²(m)/f₁(m) of W_q,
pp. 61 and 64. -/
theorem selbergTerms_sieveQ {N q l : ℕ} (y : ℝ) (hy : 1 ≤ y) (hl : l ∣ Pz N) :
    LeanLab.PNTSieve.SelbergSieve.selbergTerms (sieveQ N q y hy).toBoundingSieve l =
      ∏ p ∈ l.primeFactors, 2 / ((p : ℝ) - 2) := by
  sorry

/-- LEAF. Unit U-1544. For y ≥ 1, Σ_{d ≤ y, d squarefree} 6^{ν(d)} ≤ y (1 + log y)⁶.
Route: the sum is at most y Σ_{d ≤ y} μ²(d) 6^{ν(d)}/d, and the true size is ≍ y log⁵ y.
This bounds the remainder R_q = O(B_N z^{2a} ...) of p. 64, where 3^{ν(d)}|R(dq)| ≤ 2 B_N 6^{ν(d)}. -/
theorem sum_six_pow_omega_le {y : ℝ} (hy : 1 ≤ y) :
    ∑ d ∈ (Icc 1 ⌊y⌋₊).filter Squarefree, (6 : ℝ) ^ ω d ≤ y * (1 + log y) ^ 6 := by
  sorry

lemma omega_mul_prime {d p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) :
    ω (d * p) = ω d + 1 := by
  rw [ArithmeticFunction.cardDistinctFactors_mul
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm,
    ArithmeticFunction.cardDistinctFactors_apply_prime hp]

/-- The remainder of `sieveQ`: |r_d| ≤ 2^{ν(d)+1} 2^{ν(N)} for d ∣ P(z), q ∈ Qset N, N ≥ 1.
Assembly, CONDITIONAL ON `multSum_sieveQ`, `nuT_of_squarefree`, `sqfree_coprime_mul_q` and the
leaves of `lemma1`. This is R(dq) of Lemma 1 with ω(dq) = 2ω(d), p. 63. -/
theorem rem_sieveQ_le {N q d : ℕ} (y : ℝ) (hy : 1 ≤ y) (hN : 1 ≤ N) (hq : q ∈ Qset N)
    (hd : d ∣ Pz N) :
    |BoundingSieve.rem (s := (sieveQ N q y hy).toBoundingSieve) d| ≤
      2 ^ (ω d + 1) * 2 ^ ω N := by
  obtain ⟨hsq, hcop, hqd⟩ := sqfree_coprime_mul_q hq hd
  have hqp : q.Prime := (mem_filter.mp hq).2.1
  have hd0 : d ≠ 0 := fun h => Pz_ne_zero N (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hdsq : Squarefree d := (Pz_squarefree N).squarefree_of_dvd hd
  have hL := lemma1 hN hsq hcop
  rw [omega_mul_prime hqp hqd] at hL
  unfold BoundingSieve.rem
  rw [multSum_sieveQ y hy hq hd]
  have hnu : (sieveQ N q y hy).toBoundingSieve.nu d = 2 ^ ω d / (d : ℝ) := nuT_of_squarefree hdsq
  have hX : (sieveQ N q y hy).toBoundingSieve.totalMass = 2 * (N.totient : ℝ) / q := rfl
  rw [hnu, hX]
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have heq : (2 : ℝ) ^ ω d / d * (2 * (N.totient : ℝ) / q) =
      2 ^ (ω d + 1) * (N.totient : ℝ) / ((d * q : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [heq]
  exact hL

/-- W_q of p. 64: the sum of μ²(m)/f₁(m) = ∏_{p ∣ m} 2/(p - 2) over m ≤ w with every prime
factor of m at most z = N^{1/6}, odd and prime to N; that is, over the divisors m ≤ w of P(z).
On p. 64, w = z^a. -/
def Wq (N : ℕ) (w : ℝ) : ℝ :=
  ∑ l ∈ (Pz N).divisors.filter (fun l : ℕ => (l : ℝ) ≤ w),
    ∏ p ∈ l.primeFactors, 2 / ((p : ℝ) - 2)

/-- **The Selberg step**, first display of Section 3, p. 63: for even N ≥ 1, q ∈ Qset N and
w ≥ 1, with sieve level w², S(q) ≤ 2φ(N)/(q W_q) + R_q where
R_q ≤ 2^{ν(N)+1} w² (1 + log w²)⁶. Assembly from the lab's PROVED
`LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple`, CONDITIONAL ON `siftedSum_sieveQ`,
`selbergTerms_sieveQ`, `sum_six_pow_omega_le` and the leaves of `rem_sieveQ_le`. -/
theorem Sq_le_selberg {N q : ℕ} {w : ℝ} (hN : Even N) (hN1 : 1 ≤ N) (hq : q ∈ Qset N)
    (hw : 1 ≤ w) :
    ((Sq N q).card : ℝ) ≤ 2 * (N.totient : ℝ) / (q * Wq N w) +
      2 ^ (ω N + 1) * (w ^ 2 * (1 + log (w ^ 2)) ^ 6) := by
  have hy : (1 : ℝ) ≤ w ^ 2 := by nlinarith
  set s := sieveQ N q (w ^ 2) hy with hs
  have hb := LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple s
  rw [hs, siftedSum_sieveQ (w ^ 2) hy hN] at hb
  have hS : LeanLab.PNTSieve.SelbergSieve.selbergBoundingSum (sieveQ N q (w ^ 2) hy) = Wq N w := by
    rw [LeanLab.PNTSieve.SelbergSieve.selbergBoundingSum, Wq, sum_filter]
    refine sum_congr rfl fun l hl => ?_
    have hlP : l ∣ Pz N := Nat.dvd_of_mem_divisors hl
    rw [selbergTerms_sieveQ (w ^ 2) hy hlP]
    have hiff : ((l : ℝ) ^ 2 ≤ w ^ 2) ↔ ((l : ℝ) ≤ w) :=
      pow_le_pow_iff_left₀ (Nat.cast_nonneg l) (by linarith) two_ne_zero
    have hlev : (sieveQ N q (w ^ 2) hy).level = w ^ 2 := rfl
    rw [hlev]
    by_cases h : (l : ℝ) ≤ w
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  rw [hS] at hb
  have hX : (sieveQ N q (w ^ 2) hy).toBoundingSieve.totalMass = 2 * (N.totient : ℝ) / q := rfl
  rw [hX] at hb
  have hmain : 2 * (N.totient : ℝ) / q / Wq N w = 2 * (N.totient : ℝ) / (q * Wq N w) := by
    rw [div_div]
  rw [hmain] at hb
  refine hb.trans (add_le_add le_rfl ?_)
  -- the remainder
  have hP : (sieveQ N q (w ^ 2) hy).toBoundingSieve.prodPrimes = Pz N := rfl
  rw [hP]
  calc ∑ d ∈ (Pz N).divisors, (if (d : ℝ) ≤ w ^ 2 then (3 : ℝ) ^ ω d *
          |BoundingSieve.rem (s := (sieveQ N q (w ^ 2) hy).toBoundingSieve) d| else 0)
      ≤ ∑ d ∈ (Pz N).divisors, (if (d : ℝ) ≤ w ^ 2 then
          2 ^ (ω N + 1) * (6 : ℝ) ^ ω d else 0) := by
        refine sum_le_sum fun d hd => ?_
        split_ifs
        · have hr := rem_sieveQ_le (w ^ 2) hy hN1 hq (Nat.dvd_of_mem_divisors hd)
          calc (3 : ℝ) ^ ω d * |BoundingSieve.rem (s := (sieveQ N q (w ^ 2) hy).toBoundingSieve) d|
              ≤ 3 ^ ω d * (2 ^ (ω d + 1) * 2 ^ ω N) :=
                mul_le_mul_of_nonneg_left hr (by positivity)
            _ = 2 ^ (ω N + 1) * (6 : ℝ) ^ ω d := by
                rw [show (6 : ℝ) = 3 * 2 by norm_num, mul_pow]; ring
        · exact le_rfl
    _ = 2 ^ (ω N + 1) * ∑ d ∈ (Pz N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ w ^ 2),
          (6 : ℝ) ^ ω d := by
        rw [mul_sum, sum_filter]
    _ ≤ 2 ^ (ω N + 1) * ∑ d ∈ (Icc 1 ⌊w ^ 2⌋₊).filter Squarefree, (6 : ℝ) ^ ω d := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ?_ ?_) (by positivity)
        · intro d hd
          rw [mem_filter, Nat.mem_divisors] at hd
          have hd0 : d ≠ 0 := fun h => Pz_ne_zero N (Nat.eq_zero_of_zero_dvd (h ▸ hd.1.1))
          rw [mem_filter, mem_Icc]
          exact ⟨⟨Nat.pos_of_ne_zero hd0, Nat.le_floor hd.2⟩,
            (Pz_squarefree N).squarefree_of_dvd hd.1.1⟩
        · intro d _ _; positivity
    _ ≤ 2 ^ (ω N + 1) * (w ^ 2 * (1 + log (w ^ 2)) ^ 6) :=
        mul_le_mul_of_nonneg_left (sum_six_pow_omega_le hy) (by positivity)

/-! ### Vacuity instances -/

/-- The hypotheses of `Sq_le_selberg` can hold: N = 30030 = 2·3·5·7·11·13 is even and
q = 17 lies in Qset N, since 17⁶ > 30030 ≥ 17³ and 17 ∤ 30030; w = 1. -/
theorem vacuity_a1 : Even 30030 ∧ 1 ≤ 30030 ∧ 17 ∈ Qset 30030 ∧ (1 : ℝ) ≤ 1 := by
  refine ⟨by decide, by norm_num, ?_, le_rfl⟩
  simp only [Qset, mem_filter, mem_range]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The hypotheses of `lemma1` can hold: N = 8, d = 15 squarefree and coprime to 8. -/
theorem vacuity_a2 : 1 ≤ 8 ∧ Squarefree 15 ∧ Nat.Coprime 15 8 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  show Squarefree (3 * 5)
  exact Nat.squarefree_mul_iff.2
    ⟨by norm_num, Nat.prime_three.squarefree, Nat.prime_five.squarefree⟩

/-- The sieve problem `sieveQ` exists for concrete data, and its level is 1. -/
theorem vacuity_a3 : (sieveQ 30030 17 1 le_rfl).level = 1 := rfl

end LeanLab.AlmostPrimeSums.Decomp1544a
