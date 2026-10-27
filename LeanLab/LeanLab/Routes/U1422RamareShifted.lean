/-
# U-1422, T3 MOONSHOT: the Matomaki-Radziwill route on the shifted prime support

PC run 20261021T1403Z-5629, unit U-1422. AI wrote this Lean code.

Matomaki-Radziwill break parity for the Liouville function in almost all short intervals. Their
first step is Ramare's identity: since `λ` is completely multiplicative, for a finite set `S` of
primes and `ω_S(n)` the number of `q ∈ S` dividing `n`, one has `ω_S(n) λ(n) = Σ_{q ∈ S, q ∣ n}
λ(q) λ(n / q)`, which turns any sum of `λ` into a bilinear, Type II, sum for free. This file
records the exact identities of the route when the support is the shifted primes `N - p`.

PROVED here, unconditional:
* `ramare_pointwise`: `ω_S(n) λ(n) = Σ_{q ∈ S, q ∣ n} λ(q) λ(n/q)` for every `n`.
* `ramare_indexed`: summed over any finite family `f : ι → ℕ`, the left side is
  `Σ_{q ∈ S} λ(q) Σ_{i, q ∣ f i} λ(f i / q)`.
* `ramare_shifted`: the case `f p = N - p` over primes `p < N`; the inner sum runs over
  primes `p` in the class `p ≡ N mod q`, it is the same twisted sum in a progression.
* `dvd_sub_iff_modEq`: `q ∣ N - p ↔ p ≡ N [MOD q]` for `p ≤ N`.
* `average_over_N`: `Σ_{N < X} Σ_{p ≤ N prime} λ(N - p) = Σ_{p < X prime} Σ_{m < X - p} λ(m)`,
  so the average over `N` is a sum of long Liouville sums, the only part the method can reach.
* vacuity instances `vacuity_primes`, `vacuity_ramare_ten`.
KNOWN mathematics, elementary. Binary Goldbach is OPEN; this route is not progress on it.
-/
import Mathlib

namespace LeanLab.Routes.U1422

open Finset ArithmeticFunction

/-- `ω_S(n)`, the number of elements of `S` dividing `n`. -/
def omegaS (S : Finset ℕ) (n : ℕ) : ℕ := (S.filter (fun q => q ∣ n)).card

theorem liouville_prime' {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  rw [liouville_apply hp.ne_zero, cardFactors_apply_prime hp, pow_one]

/-- Ramare's identity, pointwise: complete multiplicativity of `λ`. -/
theorem ramare_pointwise (S : Finset ℕ) (n : ℕ) :
    (omegaS S n : ℤ) * liouville n =
      ∑ q ∈ S.filter (fun q => q ∣ n), liouville q * liouville (n / q) := by
  have h : ∀ q ∈ S.filter (fun q => q ∣ n), liouville q * liouville (n / q) = liouville n := by
    intro q hq
    have hd : q ∣ n := (mem_filter.mp hq).2
    rw [← liouville_apply_mul, Nat.mul_div_cancel' hd]
  rw [sum_congr rfl h, sum_const, nsmul_eq_mul, omegaS]

/-- Ramare's identity summed over any finite family: the Type II form. -/
theorem ramare_indexed {ι : Type*} (I : Finset ι) (f : ι → ℕ) (S : Finset ℕ) :
    ∑ i ∈ I, (omegaS S (f i) : ℤ) * liouville (f i) =
      ∑ q ∈ S, liouville q * ∑ i ∈ I.filter (fun i => q ∣ f i), liouville (f i / q) := by
  simp_rw [ramare_pointwise, sum_filter, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun q _ => sum_congr rfl (fun i _ => ?_))
  split_ifs <;> simp

/-- The case of binary Goldbach: the support `N - p`, `p < N` prime. Each inner sum is the
twisted sum `Σ λ((N - p)/q)` over primes in one class, the same problem one level down. -/
theorem ramare_shifted (N : ℕ) (S : Finset ℕ) :
    ∑ p ∈ (range N).filter Nat.Prime, (omegaS S (N - p) : ℤ) * liouville (N - p) =
      ∑ q ∈ S, liouville q *
        ∑ p ∈ ((range N).filter Nat.Prime).filter (fun p => q ∣ N - p),
          liouville ((N - p) / q) :=
  ramare_indexed _ (fun p => N - p) S

/-- The inner condition is the progression `p ≡ N mod q`. -/
theorem dvd_sub_iff_modEq {q N p : ℕ} (h : p ≤ N) : q ∣ N - p ↔ p ≡ N [MOD q] :=
  (Nat.modEq_iff_dvd' h).symm

/-- When every element of `S` is prime, the weights are `λ(q) = -1`. -/
theorem ramare_shifted_primes (N : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ p ∈ (range N).filter Nat.Prime, (omegaS S (N - p) : ℤ) * liouville (N - p) =
      - ∑ q ∈ S, ∑ p ∈ ((range N).filter Nat.Prime).filter (fun p => q ∣ N - p),
          liouville ((N - p) / q) := by
  rw [ramare_shifted, ← sum_neg_distrib]
  refine sum_congr rfl (fun q hq => ?_)
  rw [liouville_prime' (hS q hq), neg_one_mul]

/-- Averaging over the target `N` turns the twisted Goldbach sums into long Liouville sums,
which the prime number theorem controls: the almost all `N` information. -/
theorem average_over_N (X : ℕ) :
    ∑ N ∈ range X, ∑ p ∈ (range (N + 1)).filter Nat.Prime, liouville (N - p) =
      ∑ p ∈ (range X).filter Nat.Prime, ∑ m ∈ range (X - p), liouville m := by
  rw [sum_comm' (t' := (range X).filter Nat.Prime) (s' := fun p => Ico p X)]
  · refine sum_congr rfl (fun p _ => ?_)
    rw [sum_Ico_eq_sum_range]
    refine sum_congr rfl (fun m _ => ?_)
    congr 1
    omega
  · intro N p
    simp only [mem_range, mem_filter, mem_Ico]
    constructor
    · rintro ⟨hN, hp, hpr⟩
      exact ⟨⟨by omega, hN⟩, by omega, hpr⟩
    · rintro ⟨⟨h1, h2⟩, hp, hpr⟩
      exact ⟨h2, by omega, hpr⟩

/-- Vacuity: the hypothesis of `ramare_shifted_primes` holds for `S = {3, 5}`. -/
theorem vacuity_primes : ∀ q ∈ ({3, 5} : Finset ℕ), q.Prime := by
  intro q hq
  simp only [mem_insert, mem_singleton] at hq
  rcases hq with rfl | rfl <;> norm_num

/-- Vacuity: at `N = 10`, `p = 7`, `S = {3}`, the weight `ω_S(N - p) = 1` is nonzero, so the
identity is not about an empty sum. -/
theorem vacuity_ramare_ten : omegaS {3} (10 - 7) = 1 := by decide

end LeanLab.Routes.U1422
