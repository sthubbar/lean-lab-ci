/-
Ramaré 1995, P0008, unit U-1526, run 20261025T2003Z-426. DECOMPOSE file b of three.
The second moment `Σ_{N even in ]X, 2X]} rep(N)²` from a Selberg-type upper bound.

Route, standard and much weaker than Ramaré's enveloping sieve of Sections 2.1, 2.2 and 4 to 8:
an individual upper bound `gcount N ≤ A h(N) N / (log N)²`, with
`h(N) = ∏_{p ∣ N, p > 2} (p - 1)/(p - 2)`, gives `rep N ≤ A h(N) N`, and the mean value
`Σ_{m ≤ n} h(m)² ≤ 2.65 n` closes the sum. Sources: Halberstam-Richert, Sieve Methods,
Thm 3.11 and Ch. 3; the mean value is the Euler product computation of Riesel-Vaughan 1983
Section 2 and Ramaré 1995 Section 3, p. 656 to 667, in its simplest case.
The infinite product `∏_{p > 2} (1 + (2p - 3)/(p (p - 2)²)) = 2.63985...`, Python, primes
below 10^7, run 20261025T2003Z-426.

`h` duplicates `LeanLab.ChenDoubleSieve.oddFactor` by design: importing that folder costs a
long build. A link lemma can be added later.

AI-written Lean code, Claude, 2026-10-25. Checked only by the Lean kernel.
Binary Goldbach is OPEN; this is an upper bound for representation counts on average.
-/
import Mathlib
import LeanLab.Ramare1995.Decomp1526a

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.Ramare1995.Decomp1526b
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Decomp1526a

/-- `h(N) = ∏_{p ∣ N, p > 2} (p - 1)/(p - 2)`, the odd part of the singular series. -/
def oddFac (N : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- `g(d) = ∏_{p ∣ d} (2p - 3)/(p - 2)²` on odd squarefree `d`, `0` elsewhere, so that
`h(m)² = Σ_{d ∣ m} g(d)`. -/
def gfun (d : ℕ) : ℝ :=
  if Squarefree d ∧ ¬ Even d then
    ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2) else 0

theorem oddFac_one_le (N : ℕ) : 1 ≤ oddFac N := by
  unfold oddFac
  calc (1 : ℝ) = ∏ p ∈ N.primeFactors.filter (2 < ·), (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
      intro p hp; simp only [mem_filter] at hp
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
      rw [le_div_iff₀ (by linarith)]; linarith

/-- LEAF. `h(2m) = h(m)` for every `m`: the factor 2 is excluded from `h`.
Definition of `oddFac`. Unit U-1526. -/
theorem oddFac_two_mul (m : ℕ) : oddFac (2 * m) = oddFac m := by
  by_cases h : m = 0
  · simp [h, oddFac]
  · unfold oddFac
    congr 1
    ext p
    simp only [mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hd, _⟩, hl⟩
      refine ⟨⟨hp, ?_, h⟩, hl⟩
      have hd' : p ∣ 2 ∨ p ∣ m := (Nat.Prime.dvd_mul hp).mp hd
      rcases hd' with h1 | h2
      · have : p = 2 := Nat.dvd_prime Nat.prime_two |>.mp h1 |>.resolve_left hp.ne_one
        linarith
      · exact h2
    · rintro ⟨⟨hp, hd, _⟩, hl⟩
      refine ⟨⟨hp, dvd_mul_of_dvd_right hd _, mul_ne_zero two_ne_zero h⟩, hl⟩

/-- LEAF. `g(d) ≥ 0`: each factor `(2p - 3)/(p - 2)²` is nonnegative for a prime `p`
(for `p = 2` the factor is `1/0 = 0` in Lean, and `g` vanishes on even `d` anyway).
Definition of `gfun`. Unit U-1526. -/
theorem gfun_nonneg (d : ℕ) : 0 ≤ gfun d := by
  unfold gfun
  split_ifs with h
  · apply Finset.prod_nonneg
    intro p hp
    have h1 : (3 : ℝ) ≤ p := by
      have : p ∈ d.primeFactors := hp
      rw [Nat.mem_primeFactors] at this
      have hp2 : p ≠ 2 := by
        rintro rfl
        have : 2 ∣ d := this.2.1
        have : Even d := even_iff_two_dvd.mpr this
        exact h.2 this
      have hpp : Nat.Prime p := this.1
      have hp3 : 3 ≤ p := by
        have : 2 ≤ p := hpp.two_le
        omega
      exact_mod_cast hp3
    have hnum : 0 ≤ 2 * (p : ℝ) - 3 := by linarith
    have hden : 0 ≤ ((p : ℝ) - 2) ^ 2 := sq_nonneg _
    positivity
  · rfl

/-- LEAF. Divisor expansion `h(m)² = Σ_{d ∣ m} g(d)` for `m ≥ 1`: for an odd prime `p`,
`((p - 1)/(p - 2))² = 1 + (2p - 3)/(p - 2)²`, and expanding the product over the odd primes of
`m` gives the sum over odd squarefree divisors. Halberstam-Richert Ch. 3, multiplicative
expansions; Ramaré 1995 Section 3, p. 656. Unit U-1526. -/
theorem oddFac_sq_eq_sum_divisors {m : ℕ} (hm : m ≠ 0) :
    oddFac m ^ 2 = ∑ d ∈ m.divisors, gfun d := by
  sorry

/-- LEAF. Interchange and `⌊n/d⌋ ≤ n/d`: for `g ≥ 0`,
`Σ_{m ≤ n} Σ_{d ∣ m} g(d) ≤ n Σ_{d ≤ n} g(d)/d`. Elementary, Nathanson GTM 164 Section 7.4;
Montgomery-Vaughan, Multiplicative Number Theory I, Section 2.1. Unit U-1526. -/
theorem sum_Icc_sum_divisors_le (n : ℕ) :
    ∑ m ∈ Icc 1 n, ∑ d ∈ m.divisors, gfun d ≤ n * ∑ d ∈ Icc 1 n, gfun d / d := by
  sorry

/-- LEAF. Rankin-free Euler product bound: `Σ_{d ≤ n} g(d)/d ≤ ∏_{2 < p ≤ n} (1 + g(p)/p)`,
since `g(d)/d` is multiplicative, supported on odd squarefree `d`, and every such `d ≤ n`
has its primes `≤ n`. Montgomery-Vaughan I, Section 2.1. Unit U-1526. -/
theorem sum_gfun_div_le_prod (n : ℕ) :
    ∑ d ∈ Icc 1 n, gfun d / d ≤
      ∏ p ∈ (Icc 3 n).filter Nat.Prime,
        (1 + (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2)) := by
  sorry

/-- LEAF. Numerical bound: `∏_{2 < p ≤ n} (1 + (2p - 3)/(p (p - 2)²)) ≤ 2.65` for every `n`.
The full product is `2.63985...`; a proof can bound the primes up to 100 exactly and the
tail by `∏_{k > 100} (1 + 2/(k - 2)²) ≤ exp (2/97)`. Python, run 20261025T2003Z-426;
Ramaré 1995 Section 3, p. 656 to 667 for products of this kind. Unit U-1526. -/
theorem prod_odd_primes_le (n : ℕ) :
    ∏ p ∈ (Icc 3 n).filter Nat.Prime,
        (1 + (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2)) ≤ 2.65 := by
  sorry

/-- **Mean value of `h²`**, assembly, zero sorry of its own: `Σ_{m ≤ n} h(m)² ≤ 2.65 n`. -/
theorem sum_oddFac_sq_le (n : ℕ) : ∑ m ∈ Icc 1 n, oddFac m ^ 2 ≤ 2.65 * n := by
  have e : ∑ m ∈ Icc 1 n, oddFac m ^ 2 = ∑ m ∈ Icc 1 n, ∑ d ∈ m.divisors, gfun d := by
    refine sum_congr rfl fun m hm => ?_
    rw [mem_Icc] at hm
    exact oddFac_sq_eq_sum_divisors (by omega)
  rw [e]
  have h1 := sum_Icc_sum_divisors_le n
  have h2 := (sum_gfun_div_le_prod n).trans (prod_odd_primes_le n)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left h2 hn]

/-- LEAF. Reindex the even block by `N = 2m`, `m ≤ X`, and use `h(2m) = h(m)` and the mean
value: `Σ_{N even in ]X, 2X]} h(N)² ≤ 2.65 X` for `X ≥ 0`. Uses `oddFac_two_mul`,
`sum_oddFac_sq_le`. Unit U-1526. -/
theorem sum_evenBlock_oddFac_sq_le {X : ℝ} (hX : 0 ≤ X) :
    ∑ N ∈ evenBlock X, oddFac N ^ 2 ≤ 2.65 * X := by
  calc ∑ N ∈ evenBlock X, oddFac N ^ 2
    _ ≤ ∑ N ∈ (Ioc 0 ⌊2 * X⌋₊).filter Even, oddFac N ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro N hN
        rw [evenBlock, mem_filter] at hN
        rw [mem_filter, mem_Ioc]
        have h1 : ⌊X⌋₊ < N := (mem_Ioc.mp hN.1).1
        have h2 : N ≤ ⌊2 * X⌋₊ := (mem_Ioc.mp hN.1).2
        have h3 : 0 < N := by
          have : 0 ≤ ⌊X⌋₊ := Nat.zero_le _
          omega
        exact ⟨⟨h3, h2⟩, hN.2⟩
      · intro i hi _
        positivity
    _ = ∑ m ∈ Icc 1 (⌊2 * X⌋₊ / 2), oddFac (2 * m) ^ 2 := by
      have e : (Ioc 0 ⌊2 * X⌋₊).filter Even = (Icc 1 (⌊2 * X⌋₊ / 2)).image (fun m => 2 * m) := by
        ext a
        rw [mem_filter, mem_image]
        constructor
        · rintro ⟨ha1, ha2⟩
          rw [mem_Ioc] at ha1
          rw [even_iff_two_dvd] at ha2
          rcases ha2 with ⟨k, hk⟩
          use k
          constructor
          · rw [mem_Icc]
            have h0 : 0 < k := by
              have : 0 < 2 * k := by omega
              omega
            have hk2 : k ≤ ⌊2 * X⌋₊ / 2 := by
              rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
              omega
            exact ⟨h0, hk2⟩
          · omega
        · rintro ⟨m, hm1, hm2⟩
          rw [mem_Icc] at hm1
          constructor
          · rw [mem_Ioc]
            have h1 : 0 < 2 * m := by omega
            have h2 : 2 * m ≤ ⌊2 * X⌋₊ := by
              have : m ≤ ⌊2 * X⌋₊ / 2 := hm1.2
              rw [mul_comm]
              exact Nat.mul_le_of_le_div 2 m _ this
            omega
          · rw [even_iff_two_dvd]
            use m
            omega
      rw [e]
      apply sum_image
      intro x hx y hy heq
      have : 2 * x = 2 * y := heq
      omega
    _ = ∑ m ∈ Icc 1 (⌊2 * X⌋₊ / 2), oddFac m ^ 2 := by
      apply sum_congr rfl
      intro m _
      rw [oddFac_two_mul]
    _ ≤ 2.65 * (⌊2 * X⌋₊ / 2 : ℕ) := sum_oddFac_sq_le _
    _ ≤ 2.65 * X := by
      have : ((⌊2 * X⌋₊ / 2 : ℕ) : ℝ) ≤ X := by
        calc ((⌊2 * X⌋₊ / 2 : ℕ) : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) / 2 := by
              exact_mod_cast Nat.cast_div_le
          _ ≤ (2 * X) / 2 := by
              have : (⌊2 * X⌋₊ : ℝ) ≤ 2 * X := Nat.floor_le (by linarith)
              linarith
          _ = X := by linarith
      have : 0 ≤ (2.65 : ℝ) := by norm_num
      nlinarith

/-- LEAF. From an unweighted bound `gcount N ≤ A h(N) N / (log N)²`, `N ≥ 2`, to the weighted
`rep N ≤ A h(N) N`. Uses `rep_le_log_sq_mul_gcount`. Halberstam-Richert Ch. 3.
Unit U-1526. -/
theorem rep_le_of_gcount_le {A : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (h : (gcount N : ℝ) ≤ A * oddFac N * N / Real.log N ^ 2) :
    rep N ≤ A * oddFac N * N := by
  calc rep N
    _ ≤ Real.log N ^ 2 * gcount N := rep_le_log_sq_mul_gcount N
    _ ≤ Real.log N ^ 2 * (A * oddFac N * N / Real.log N ^ 2) := by
      apply mul_le_mul_of_nonneg_left h
      positivity
    _ = A * oddFac N * N := by
      rw [mul_div_cancel₀]
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have : 0 < Real.log (N : ℝ) := by
        apply Real.log_pos
        linarith
      positivity

/-- LEAF. Explicit Selberg upper bound in the range of Theorem 2: for even `N ≥ exp 67`,
`gcount N ≤ 800 h(N) N / (log N)²`. Selberg's sieve at level `z = N^{1/4}`,
Halberstam-Richert Thm 3.11; in the lab, `LeanLab.SchnirelmannGoldbach.S1.r_le_of_even`
gives `r(N) ≤ 32 N ∏_{p ∣ N}(1 + 1/p) / (log z)² + z (1 + log z)⁶ + 2 (z + 1)`, and the
computation in `LeanLab.ChenDoubleSieve.goldbachUpper_1200` bounds this by `769 h(N) N/(log N)²`
once `4 (log N)⁸ ≤ N^{3/4}`, true for `log N ≥ 67`; `gcount N = r N` since `N - N = 0` is not
prime. Unit U-1526. -/
theorem gcount_le_selberg {N : ℕ} (hN : Even N) (hN67 : exp 67 ≤ N) :
    (gcount N : ℝ) ≤ 800 * oddFac N * N / Real.log N ^ 2 := by
  sorry

/-- LEAF. **Second moment from an individual bound**: if `gcount N ≤ A h(N) N/(log N)²` for
every even `N ≥ exp 67`, then `Σ_{N even in ]X, 2X]} rep(N)² ≤ 10.6 A² X³` for `X ≥ exp 67`:
`rep N ≤ A h(N) N ≤ 2 A X h(N)`, then `sum_evenBlock_oddFac_sq_le`. Uses
`rep_le_of_gcount_le`. Unit U-1526. -/
theorem second_moment_of {A : ℝ} (hA : 0 ≤ A)
    (hW : ∀ N : ℕ, Even N → exp 67 ≤ N → (gcount N : ℝ) ≤ A * oddFac N * N / Real.log N ^ 2)
    {X : ℝ} (hX : exp 67 ≤ X) :
    ∑ N ∈ evenBlock X, rep N ^ 2 ≤ 10.6 * A ^ 2 * X ^ 3 := by
  calc ∑ N ∈ evenBlock X, rep N ^ 2
    _ ≤ ∑ N ∈ evenBlock X, (A * oddFac N * N) ^ 2 := by
      apply sum_le_sum
      intro N hN
      have hEven : Even N := (mem_filter.mp hN).2
      have hIoc : N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ := (mem_filter.mp hN).1
      have hX_pos : 0 < X := by linarith [exp_pos 67]
      have hn_exp : exp 67 ≤ N := by
        have : ⌊X⌋₊ < N := (mem_Ioc.mp hIoc).1
        have : X < N := by
          calc X < ⌊X⌋₊ + 1 := Nat.lt_floor_add_one X
            _ ≤ N := by exact_mod_cast this
        linarith
      have hn2 : 2 ≤ N := by
        have : (2 : ℝ) ≤ exp 67 := by linarith [Real.exp_monotone (by linarith : (1 : ℝ) ≤ 67), Real.exp_one_gt_d9]
        exact_mod_cast (this.trans hn_exp)
      have h1 := hW N hEven hn_exp
      have h2 := rep_le_of_gcount_le hn2 h1
      have h_pos : 0 ≤ rep N := rep_nonneg N
      nlinarith
    _ = A ^ 2 * ∑ N ∈ evenBlock X, oddFac N ^ 2 * N ^ 2 := by
      calc ∑ N ∈ evenBlock X, (A * oddFac N * N) ^ 2
        _ = ∑ N ∈ evenBlock X, (A ^ 2 * oddFac N ^ 2 * (N : ℝ) ^ 2) := by
          apply sum_congr rfl
          intro N _
          ring
        _ = A ^ 2 * ∑ N ∈ evenBlock X, (oddFac N ^ 2 * (N : ℝ) ^ 2) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro N _
          ring
    _ ≤ A ^ 2 * ∑ N ∈ evenBlock X, oddFac N ^ 2 * (2 * X) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply sum_le_sum
        intro N hN
        have hIoc : N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ := (mem_filter.mp hN).1
        have hX_pos : 0 ≤ X := by linarith [exp_pos 67]
        have hNX : (N : ℝ) ≤ 2 * X := by
          have : N ≤ ⌊2 * X⌋₊ := (mem_Ioc.mp hIoc).2
          calc (N : ℝ) ≤ ⌊2 * X⌋₊ := by exact_mod_cast this
            _ ≤ 2 * X := Nat.floor_le (by linarith)
        have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        have h1 : (N : ℝ) ^ 2 ≤ (2 * X) ^ 2 := by
          nlinarith
        have h2 : 0 ≤ oddFac N ^ 2 := sq_nonneg _
        nlinarith
      · exact sq_nonneg A
    _ = A ^ 2 * (2 * X) ^ 2 * ∑ N ∈ evenBlock X, oddFac N ^ 2 := by
      calc A ^ 2 * ∑ N ∈ evenBlock X, oddFac N ^ 2 * (2 * X) ^ 2
        _ = ∑ N ∈ evenBlock X, A ^ 2 * (oddFac N ^ 2 * (2 * X) ^ 2) := by rw [mul_sum]
        _ = ∑ N ∈ evenBlock X, (A ^ 2 * (2 * X) ^ 2) * oddFac N ^ 2 := by
          apply sum_congr rfl
          intro N _
          ring
        _ = A ^ 2 * (2 * X) ^ 2 * ∑ N ∈ evenBlock X, oddFac N ^ 2 := by rw [← mul_sum]
    _ ≤ A ^ 2 * (2 * X) ^ 2 * (2.65 * X) := by
      have : 0 ≤ A ^ 2 * (2 * X) ^ 2 := by positivity
      have h1 := sum_evenBlock_oddFac_sq_le (by linarith [exp_pos 67])
      nlinarith
    _ = 10.6 * A ^ 2 * X ^ 3 := by ring

/-- **Second moment, explicit**, assembly, zero sorry of its own: for `X ≥ exp 67`,
`Σ_{N even in ]X, 2X]} rep(N)² ≤ 6 784 000 X³`, from the Selberg leaf with `A = 800`. -/
theorem second_moment {X : ℝ} (hX : exp 67 ≤ X) :
    ∑ N ∈ evenBlock X, rep N ^ 2 ≤ 6784000 * X ^ 3 := by
  have := second_moment_of (A := 800) (by norm_num)
    (fun N hN h67 => gcount_le_selberg hN h67) hX
  norm_num at this ⊢
  linarith

/-- Vacuity: `h(15)` has two odd prime factors, so the product in `oddFac` is not empty;
`h ≥ 1` always. -/
example : 1 ≤ oddFac 15 := oddFac_one_le 15

end LeanLab.Ramare1995.Decomp1526b
