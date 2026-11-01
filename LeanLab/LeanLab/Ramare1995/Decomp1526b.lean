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
import LeanLab.Ramare1995.AristotleTrial04
import LeanLab.Ramare1995.AristotleTrial05
import LeanLab.ChenDoubleSieve.SelbergUpper
import LeanLab.ChenExplicit.GammaBounds
import LeanLab.RieselVaughan1983.Lemma1Gamma1
import LeanLab.RieselVaughan1983.Stieltjes1Enclosure

open Finset Real Filter Topology
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
  exact AristotleTrial04.oddFac_sq_eq_sum_divisors hm

/-- LEAF. Interchange and `⌊n/d⌋ ≤ n/d`: for `g ≥ 0`,
`Σ_{m ≤ n} Σ_{d ∣ m} g(d) ≤ n Σ_{d ≤ n} g(d)/d`. Elementary, Nathanson GTM 164 Section 7.4;
Montgomery-Vaughan, Multiplicative Number Theory I, Section 2.1. Unit U-1526. -/
theorem sum_Icc_sum_divisors_le (n : ℕ) :
    ∑ m ∈ Icc 1 n, ∑ d ∈ m.divisors, gfun d ≤ n * ∑ d ∈ Icc 1 n, gfun d / d := by
  exact AristotleTrial05.sum_Icc_sum_divisors_le n

/-- LEAF. Rankin-free Euler product bound: `Σ_{d ≤ n} g(d)/d ≤ ∏_{2 < p ≤ n} (1 + g(p)/p)`,
since `g(d)/d` is multiplicative, supported on odd squarefree `d`, and every such `d ≤ n`
has its primes `≤ n`. Montgomery-Vaughan I, Section 2.1. Unit U-1526. -/
theorem sum_gfun_div_le_prod (n : ℕ) :
    ∑ d ∈ Icc 1 n, gfun d / d ≤
      ∏ p ∈ (Icc 3 n).filter Nat.Prime,
        (1 + (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2)) := by
  let S := (Icc 1 n).filter (fun d => Squarefree d ∧ ¬ Even d)
  let P := (Icc 3 n).filter Nat.Prime
  let a : ℕ → ℝ := fun p => (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2)
  have hs : ∑ d ∈ Icc 1 n, gfun d / d = ∑ d ∈ S, gfun d / d := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    by_cases h : Squarefree d ∧ ¬ Even d
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      simp only [gfun, ite_eq_right h, zero_div]
  have hf : ∀ d ∈ S, gfun d / d = ∏ p ∈ d.primeFactors, a p := by
    intro d hd
    have hd' := (mem_filter.mp hd).2
    have hdcast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd'.1]
    rw [gfun, ite_eq_left hd', hdcast, ← Finset.prod_div_distrib]
    apply prod_congr rfl
    intro p _
    dsimp [a]
    simp only [div_div, mul_comm]
  have hinj : Set.InjOn Nat.primeFactors (S : Set ℕ) := by
    intro d hd e he hde
    have hd' := (mem_filter.mp hd).2.1
    have he' := (mem_filter.mp he).2.1
    rw [← Nat.prod_primeFactors_of_squarefree hd',
      ← Nat.prod_primeFactors_of_squarefree he', hde]
  have hsub : S.image Nat.primeFactors ⊆ P.powerset := by
    intro T hT
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hT
    have hd' := mem_filter.mp hd
    apply mem_powerset.mpr
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hd'.2.2 (even_iff_two_dvd.mpr hpd)
    have hp3 : 3 ≤ p := by have := hpp.two_le; omega
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp3,
      (Nat.le_of_dvd (by have := (mem_Icc.mp hd'.1).1; omega) hpd).trans
        (mem_Icc.mp hd'.1).2⟩, hpp⟩
  rw [hs, sum_congr rfl hf, ← sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, a p) hinj]
  change _ ≤ ∏ p ∈ P, (1 + a p)
  rw [prod_one_add]
  apply sum_le_sum_of_subset_of_nonneg hsub
  intro T hT _
  apply prod_nonneg
  intro p hp
  have hpm := (mem_powerset.mp hT) hp
  have hp3 : (3 : ℝ) ≤ p := by
    exact_mod_cast (mem_Icc.mp (mem_filter.mp hpm).1).1
  apply div_nonneg
  · linarith
  · positivity

set_option maxHeartbeats 2000000 in
/-- Finite certificate for the product leaf. The cutoff 499 leaves room for a
rational telescoping tail over all integers. Auxiliary computation for the
mean value route in Ramaré 1995 Section 3, p. 656 to 667. -/
theorem prod_odd_primes_499_le :
    (∏ p ∈ (Icc 3 499).filter Nat.Prime,
      (1 + (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2))) ≤
      (2.65 : ℝ) * (497 / 499) := by
  have he : (Icc 3 499).filter Nat.Prime = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499} := by decide +kernel
  rw [he]
  norm_num

/-- Rational tail step for the product leaf. Multiplying the factor at x
by the previous potential gives at most the next potential for x at least 4.
Lab auxiliary estimate for Ramaré 1995 Section 3, p. 656 to 667. -/
theorem euler_factor_step (x : ℝ) (hx : 4 ≤ x) :
    (1 + (2 * x - 3) / (x * (x - 2) ^ 2)) * ((x - 3) / (x - 1)) ≤
      (x - 2) / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hx2 : 0 < x - 2 := by linarith
  rw [← mul_div_assoc, div_le_div_iff₀ hx1 hx0]
  field_simp
  nlinarith [sq_nonneg (x - 2)]

/-- LEAF. Numerical bound: `∏_{2 < p ≤ n} (1 + (2p - 3)/(p (p - 2)²)) ≤ 2.65` for every `n`.
The full product is `2.63985...`; a proof can bound the primes up to 100 exactly and the
tail by `∏_{k > 100} (1 + 2/(k - 2)²) ≤ exp (2/97)`. Python, run 20261025T2003Z-426;
Ramaré 1995 Section 3, p. 656 to 667 for products of this kind. Unit U-1526. -/
theorem prod_odd_primes_le (n : ℕ) :
    ∏ p ∈ (Icc 3 n).filter Nat.Prime,
        (1 + (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2)) ≤ 2.65 := by
  have hbase := prod_odd_primes_499_le
  let f : ℕ → ℝ := fun p => 1 + (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2)
  let F : ℕ → ℝ := fun k => ∏ p ∈ (Icc 3 k).filter Nat.Prime, f p
  have hf : ∀ p, 3 ≤ p → 1 ≤ f p := by
    intro p hp
    have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
    dsimp [f]
    have : 0 ≤ (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2) := by
      apply div_nonneg <;> nlinarith
    linarith
  have hind : ∀ k : ℕ, 499 ≤ k → F k ≤ 2.65 * (((k : ℝ) - 2) / k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simpa only [F, f, Nat.cast_ofNat, show (499 : ℝ) - 2 = 497 by norm_num] using hbase
    | succ k hk ih =>
      have hk' : (499 : ℝ) ≤ k := by exact_mod_cast hk
      have he : F (k + 1) = F k * (if (k + 1).Prime then f (k + 1) else 1) := by
        dsimp [F]
        simp only [prod_filter]
        rw [prod_Icc_succ_top (by omega)]
      rw [he]
      by_cases hp : (k + 1).Prime
      · rw [ite_eq_left hp]
        have hs := euler_factor_step ((k : ℝ) + 1) (by linarith)
        have hs' : f (k + 1) * (((k : ℝ) - 2) / k) ≤
            ((((k + 1 : ℕ) : ℝ) - 2) / (k + 1)) := by
          simpa only [f, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
            show ∀ x : ℝ, x + 1 - 3 = x - 2 by intro x; ring] using hs
        calc F k * f (k + 1) ≤ (2.65 * (((k : ℝ) - 2) / k)) * f (k + 1) :=
            mul_le_mul_of_nonneg_right ih (by have := hf (k+1) (by omega); linarith)
          _ = 2.65 * (f (k + 1) * (((k : ℝ) - 2) / k)) := by ring
          _ ≤ _ := by
            simpa only [Nat.cast_add, Nat.cast_one] using
              mul_le_mul_of_nonneg_left hs' (by norm_num : (0 : ℝ) ≤ 2.65)
      · rw [ite_eq_right hp, mul_one]
        refine ih.trans ?_
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        push_cast
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < k) (by positivity : (0 : ℝ) < k + 1)]
        nlinarith
  change F n ≤ 2.65
  by_cases hn : 499 ≤ n
  · refine (hind n hn).trans ?_
    have hn' : (499 : ℝ) ≤ n := by exact_mod_cast hn
    have hratio : ((n : ℝ) - 2) / n ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    nlinarith
  · have hsub : (Icc 3 n).filter Nat.Prime ⊆ (Icc 3 499).filter Nat.Prime := by
      intro p hp
      simp only [mem_filter, mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
    have hm : F n ≤ F 499 := prod_le_prod_of_subset_of_one_le₀ hsub
      (fun p hp => (zero_le_one : (0 : ℝ) ≤ 1).trans (hf p (mem_Icc.mp (mem_filter.mp hp).1).1))
      (fun p hp _ => hf p (mem_Icc.mp (mem_filter.mp hp).1).1)
    exact hm.trans (hbase.trans (by norm_num))

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

/-- Explicit threshold estimate for the Selberg leaf. The twentieth term
of the exponential series suffices for L at least 67. Auxiliary arithmetic
for the range of Theorem 2, Ramaré 1995 p. 646. -/
theorem four_mul_pow_eight_le_exp {L : ℝ} (hL : 67 ≤ L) : 4 * L ^ 8 ≤ exp (3 * L / 4) := by
  have h0 : 0 ≤ L := by linarith
  have hp : (67 : ℝ) ^ 12 ≤ L ^ 12 := pow_le_pow_left₀ (by norm_num) hL 12
  have hc : (4 : ℝ) ≤ ((3 / 4 : ℝ) ^ 20 / (Nat.factorial 20 : ℝ)) * 67 ^ 12 := by
    norm_num
  calc 4 * L ^ 8 ≤ (((3 / 4 : ℝ) ^ 20 / (Nat.factorial 20 : ℝ)) * 67 ^ 12) * L ^ 8 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (((3 / 4 : ℝ) ^ 20 / (Nat.factorial 20 : ℝ)) * L ^ 12) * L ^ 8 := by
      gcongr
    _ = (3 * L / 4) ^ 20 / (Nat.factorial 20 : ℝ) := by ring
    _ ≤ exp (3 * L / 4) := Real.pow_div_factorial_le_exp (3 * L / 4) (by positivity) 20

/-- LEAF. Explicit Selberg upper bound in the range of Theorem 2: for even `N ≥ exp 67`,
`gcount N ≤ 800 h(N) N / (log N)²`. Selberg's sieve at level `z = N^{1/4}`,
Halberstam-Richert Thm 3.11; in the lab, `LeanLab.SchnirelmannGoldbach.S1.r_le_of_even`
gives `r(N) ≤ 32 N ∏_{p ∣ N}(1 + 1/p) / (log z)² + z (1 + log z)⁶ + 2 (z + 1)`, and the
computation in `LeanLab.ChenDoubleSieve.goldbachUpper_1200` bounds this by `769 h(N) N/(log N)²`
once `4 (log N)⁸ ≤ N^{3/4}`, true for `log N ≥ 67`; `gcount N = r N` since `N - N = 0` is not
prime. Unit U-1526. -/
theorem gcount_le_selberg {N : ℕ} (hN : Even N) (hN67 : exp 67 ≤ N) :
    (gcount N : ℝ) ≤ 800 * oddFac N * N / Real.log N ^ 2 := by
  have hN2 : 2 ≤ N := by
    have h := (Real.add_one_le_exp (67 : ℝ)).trans hN67
    exact_mod_cast (show (2 : ℝ) ≤ N by linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let L := Real.log (N : ℝ)
  have hL67 : 67 ≤ L := by
    exact (Real.le_log_iff_exp_le hN0).mpr hN67
  have hL0 : 0 < L := by linarith
  have hpow : 4 * L ^ 8 ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos hN0]
    change 4 * L ^ 8 ≤ exp (L * (3 / 4))
    rw [show L * (3 / 4) = 3 * L / 4 by ring]
    exact four_mul_pow_eight_le_exp hL67
  let z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4)
  have hz1 : 1 < z := Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hz0 : 0 < z := by linarith
  have hlz : Real.log z = L / 4 := by
    change Real.log ((N : ℝ) ^ ((1 : ℝ) / 4)) = L / 4
    rw [Real.log_rpow hN0]
    ring
  have hr := LeanLab.SchnirelmannGoldbach.S1.r_le_of_even hN (by omega) hz1
  rw [hlz] at hr
  have hsp : LeanLab.SchnirelmannGoldbach.singProd N ≤ 3 / 2 * oddFac N :=
    LeanLab.ChenDoubleSieve.singProd_le_oddFactor N hN (by omega)
  have hodd := oddFac_one_le N
  have hmain : 32 * N * LeanLab.SchnirelmannGoldbach.singProd N / (L / 4) ^ 2 ≤
      768 * oddFac N * N / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_left hsp (by positivity : 0 ≤ 32 * (N : ℝ))
    nlinarith [sq_nonneg L, mul_pos hN0 (sq_pos_of_pos hL0)]
  have herr : z * (1 + L / 4) ^ 6 + 2 * (z + 1) ≤ oddFac N * N / L ^ 2 := by
    have h1 : (1 + L / 4) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
    have hzN : z * (N : ℝ) ^ ((3 : ℝ) / 4) = N := by
      change (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) = N
      rw [← Real.rpow_add hN0]
      norm_num
    have hL6 : 4 ≤ L ^ 6 := by
      calc (4 : ℝ) ≤ 4 ^ 6 := by norm_num
        _ ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
    have hz6 : z * (1 + L / 4) ^ 6 + 2 * (z + 1) ≤ 4 * z * L ^ 6 := by
      have a1 := mul_le_mul_of_nonneg_left h1 hz0.le
      have a2 := mul_le_mul_of_nonneg_left hL6 hz0.le
      linarith
    have key : 4 * z * L ^ 6 * L ^ 2 ≤ N := by
      calc 4 * z * L ^ 6 * L ^ 2 = z * (4 * L ^ 8) := by ring
        _ ≤ z * (N : ℝ) ^ ((3 : ℝ) / 4) := mul_le_mul_of_nonneg_left hpow hz0.le
        _ = N := hzN
    rw [le_div_iff₀ (by positivity)]
    calc (z * (1 + L / 4) ^ 6 + 2 * (z + 1)) * L ^ 2 ≤ 4 * z * L ^ 6 * L ^ 2 :=
        mul_le_mul_of_nonneg_right hz6 (by positivity)
      _ ≤ N := key
      _ ≤ oddFac N * N := by nlinarith
  have he : gcount N = LeanLab.SchnirelmannGoldbach.r N := by
    unfold gcount LeanLab.SchnirelmannGoldbach.r
    congr 1
    ext p
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hp, hpr, hq⟩
      refine ⟨?_, hpr, hq⟩
      have hne : p ≠ N := by
        rintro rfl
        exact Nat.not_prime_zero (by simpa using hq)
      omega
    · rintro ⟨hp, hpr, hq⟩
      exact ⟨by omega, hpr, hq⟩
  rw [he]
  calc (LeanLab.SchnirelmannGoldbach.r N : ℝ) ≤ _ := hr
    _ ≤ 768 * oddFac N * N / L ^ 2 + oddFac N * N / L ^ 2 := by linarith
    _ = 769 * oddFac N * N / L ^ 2 := by ring
    _ ≤ 800 * oddFac N * N / L ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith

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

/-- Ramaré 1995, Lemma 3.1, p. 656, at a natural cutoff. Removing the
primes dividing d costs at most their finite Euler product. Conversely,
that Euler product times the restricted sum fits below the sum up to n times d.
The squarefree filter represents the factor mu squared in the paper. -/
theorem lemma31_nat (F : ArithmeticFunction ℝ) (hF : F.IsMultiplicative)
    (hpos : ∀ k, 0 ≤ F k) (n d : ℕ) (hd : d ≠ 0) :
    (∑ m ∈ (Icc 1 n).filter Squarefree, F m) ≤
      (∏ p ∈ d.primeFactors, (1 + F p)) *
        ∑ m ∈ (Icc 1 n).filter (fun m => Squarefree m ∧ Nat.Coprime m d), F m ∧
    (∏ p ∈ d.primeFactors, (1 + F p)) *
        (∑ m ∈ (Icc 1 n).filter (fun m => Squarefree m ∧ Nat.Coprime m d), F m) ≤
      ∑ m ∈ (Icc 1 (n * d)).filter Squarefree, F m := by
  let A := (Icc 1 n).filter Squarefree
  let D := d.divisors.filter Squarefree
  let C := (Icc 1 n).filter (fun m => Squarefree m ∧ Nat.Coprime m d)
  let W : ℕ × ℕ → ℝ := fun x => F x.1 * F x.2
  have hsum : ∑ a ∈ D, F a = ∏ p ∈ d.primeFactors, (1 + F p) := by
    dsimp [D]
    rw [Nat.sum_divisors_filter_squarefree hd, prod_one_add]
    have he : (UniqueFactorizationMonoid.normalizedFactors d).toFinset = d.primeFactors := by
      rw [Nat.factors_eq]
      rfl
    rw [he]
    apply sum_congr rfl
    intro t ht
    have ht' := mem_powerset.mp ht
    have he' : t.val.prod = ∏ a ∈ t, a := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [he', hF.map_prod_of_subset_primeFactors d t ht']
  have emid : (∏ p ∈ d.primeFactors, (1 + F p)) * (∑ m ∈ C, F m) =
      ∑ x ∈ D ×ˢ C, W x := by
    rw [← hsum, sum_product, sum_mul]
    apply sum_congr rfl
    intro a _
    rw [mul_sum]
  change (∑ m ∈ A, F m) ≤ _ ∧ _ ≤ _
  rw [emid]
  constructor
  · let T : ℕ → ℕ × ℕ := fun m => (Nat.gcd m d, m / Nat.gcd m d)
    have hmul : ∀ m, (T m).1 * (T m).2 = m := fun m =>
      Nat.mul_div_cancel' (Nat.gcd_dvd_left m d)
    have hinj : Set.InjOn T (A : Set ℕ) := by
      intro m hm k hk hmk
      have h := congrArg (fun x : ℕ × ℕ => x.1 * x.2) hmk
      simpa only [hmul] using h
    have hsub : A.image T ⊆ D ×ˢ C := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hx
      have hm' := mem_filter.mp hm
      have hmsq := hm'.2
      have hmn := mem_Icc.mp hm'.1
      have hq : m / Nat.gcd m d ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m d)
      have hqpos : 1 ≤ m / Nat.gcd m d := by
        have h := hmul m
        dsimp [T] at h
        rcases Nat.eq_zero_or_pos (m / Nat.gcd m d) with hz | hz
        · rw [hz, mul_zero] at h
          omega
        · exact hz
      apply mem_product.mpr
      constructor
      · apply mem_filter.mpr
        exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right m d, hd⟩,
          Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left m d) hmsq⟩
      · apply mem_filter.mpr
        exact ⟨mem_Icc.mpr ⟨hqpos, (Nat.div_le_self m _).trans hmn.2⟩,
          Squarefree.squarefree_of_dvd hq hmsq, Nat.coprime_div_gcd_of_squarefree hmsq hd⟩
    have hw : ∀ m ∈ A, W (T m) = F m := by
      intro m hm
      have hmsq := (mem_filter.mp hm).2
      have hc := Nat.coprime_div_gcd_of_squarefree hmsq hd
      have hc' : Nat.Coprime (Nat.gcd m d) (m / Nat.gcd m d) :=
        (hc.of_dvd_right (Nat.gcd_dvd_right m d)).symm
      dsimp [W, T]
      rw [← hF.map_mul_of_coprime hc', Nat.mul_div_cancel' (Nat.gcd_dvd_left m d)]
    calc
      (∑ m ∈ A, F m) = ∑ x ∈ A.image T, W x := by
        rw [sum_image hinj]
        exact sum_congr rfl fun m hm => (hw m hm).symm
      _ ≤ ∑ x ∈ D ×ˢ C, W x :=
        sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => mul_nonneg (hpos _) (hpos _))
  · let U : ℕ × ℕ → ℕ := fun x => x.1 * x.2
    have hinj : Set.InjOn U ((D ×ˢ C : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro x hx y hy hxy
      obtain ⟨hxD, hxC⟩ := mem_product.mp hx
      obtain ⟨hyD, hyC⟩ := mem_product.mp hy
      have hxdiv := (Nat.mem_divisors.mp (mem_filter.mp hxD).1).1
      have hydiv := (Nat.mem_divisors.mp (mem_filter.mp hyD).1).1
      have hxcop := (mem_filter.mp hxC).2.2
      have hycop := (mem_filter.mp hyC).2.2
      have hdx : x.1 ∣ y.1 :=
        (hycop.of_dvd_right hxdiv).symm.dvd_of_dvd_mul_right
          (by dsimp [U] at hxy; rw [← hxy]; exact dvd_mul_right _ _)
      have hdy : y.1 ∣ x.1 :=
        (hxcop.of_dvd_right hydiv).symm.dvd_of_dvd_mul_right
          (by dsimp [U] at hxy; rw [hxy]; exact dvd_mul_right _ _)
      have he : x.1 = y.1 := Nat.dvd_antisymm hdx hdy
      apply Prod.ext he
      have hx0 : 0 < x.1 := Nat.pos_of_mem_divisors (mem_filter.mp hxD).1
      dsimp [U] at hxy
      rw [← he] at hxy
      exact Nat.eq_of_mul_eq_mul_left hx0 hxy
    have hsub : (D ×ˢ C).image U ⊆ (Icc 1 (n * d)).filter Squarefree := by
      intro m hm
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hm
      obtain ⟨hxD, hxC⟩ := mem_product.mp hx
      have hxdiv := (Nat.mem_divisors.mp (mem_filter.mp hxD).1).1
      have hxsq := (mem_filter.mp hxD).2
      have hxC' := mem_filter.mp hxC
      have hxcn := mem_Icc.mp hxC'.1
      have hc : Nat.Coprime x.1 x.2 := (hxC'.2.2.of_dvd_right hxdiv).symm
      have hxd : x.1 ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hxdiv
      have hxpos : 1 ≤ x.1 := Nat.pos_of_mem_divisors (mem_filter.mp hxD).1
      apply mem_filter.mpr
      constructor
      · exact mem_Icc.mpr ⟨by dsimp [U]; nlinarith,
          by dsimp [U]; nlinarith [Nat.mul_le_mul hxd hxcn.2]⟩
      · exact Nat.squarefree_mul_iff.mpr ⟨hc, hxsq, hxC'.2.1⟩
    have hw : ∀ x ∈ D ×ˢ C, F (U x) = W x := by
      intro x hx
      obtain ⟨hxD, hxC⟩ := mem_product.mp hx
      have hxdiv := (Nat.mem_divisors.mp (mem_filter.mp hxD).1).1
      have hc := (mem_filter.mp hxC).2.2
      exact hF.map_mul_of_coprime ((hc.of_dvd_right hxdiv).symm)
    calc
      (∑ x ∈ D ×ˢ C, W x) = ∑ m ∈ (D ×ˢ C).image U, F m := by
        rw [sum_image hinj]
        exact sum_congr rfl fun x hx => (hw x hx).symm
      _ ≤ ∑ m ∈ (Icc 1 (n * d)).filter Squarefree, F m :=
        sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hpos m)

/-- Ramaré 1995, Lemma 3.1, p. 656. The two bounds for every real
nonnegative cutoff. Squarefree filters represent mu squared. -/
theorem lemma31 (F : ArithmeticFunction ℝ) (hF : F.IsMultiplicative)
    (hpos : ∀ k, 0 ≤ F k) (x : ℝ) (hx : 0 ≤ x) (d : ℕ) (hd : d ≠ 0) :
    (∑ m ∈ (Icc 1 ⌊x⌋₊).filter Squarefree, F m) ≤
      (∏ p ∈ d.primeFactors, (1 + F p)) *
        ∑ m ∈ (Icc 1 ⌊x⌋₊).filter (fun m => Squarefree m ∧ Nat.Coprime m d), F m ∧
    (∏ p ∈ d.primeFactors, (1 + F p)) *
        (∑ m ∈ (Icc 1 ⌊x⌋₊).filter (fun m => Squarefree m ∧ Nat.Coprime m d), F m) ≤
      ∑ m ∈ (Icc 1 ⌊x * (d : ℝ)⌋₊).filter Squarefree, F m := by
  have h := lemma31_nat F hF hpos ⌊x⌋₊ d hd
  constructor
  · exact h.1
  · refine h.2.trans ?_
    have hcut : ⌊x⌋₊ * d ≤ ⌊x * (d : ℝ)⌋₊ := by
      apply Nat.le_floor
      push_cast
      exact mul_le_mul_of_nonneg_right (Nat.floor_le hx) (Nat.cast_nonneg d)
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      have hm' := mem_filter.mp hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hm'.1).1,
        (mem_Icc.mp hm'.1).2.trans hcut⟩, hm'.2⟩
    · intro m _ _
      exact hpos m

/-- Auxiliary bound for Ramaré 1995 Lemma 3.3, p. 657. For n at least 1
and t between n and n plus 1, the harmonic error is at most 1 divided by 2n.
Uses the existing GammaBounds upper and lower estimates. -/
theorem harmonic_error_le_half_inv {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (hnt : (n : ℝ) ≤ t) (htn : t ≤ (n : ℝ) + 1) :
    |(harmonic n : ℝ) - log t - eulerMascheroniConstant| ≤ 1 / (2 * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ht0 : 0 < t := hn0.trans_le hnt
  have hnh : 0 < (n : ℝ) + 1/2 := by linarith
  have hu := LeanLab.ChenExplicit.Gamma.u_le_gamma n hn
  have hw := LeanLab.ChenExplicit.Gamma.gamma_le_w n
  unfold LeanLab.ChenExplicit.Gamma.u at hu
  unfold LeanLab.ChenExplicit.Gamma.w at hw
  apply abs_le.mpr
  constructor
  · have he := Real.log_le_sub_one_of_pos (div_pos ht0 hnh)
    rw [Real.log_div (ne_of_gt ht0) (ne_of_gt hnh)] at he
    have hdiff : log t - log ((n : ℝ) + 1/2) ≤ 1 / (2 * n) := by
      calc log t - log ((n : ℝ) + 1/2) ≤ t / ((n : ℝ) + 1/2) - 1 := he
        _ = (t - ((n : ℝ) + 1/2)) / ((n : ℝ) + 1/2) := by field_simp
        _ ≤ (1/2) / ((n : ℝ) + 1/2) := by
          apply div_le_div_of_nonneg_right _ hnh.le
          linarith
        _ ≤ (1/2) / (n : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hn0 (by linarith)
        _ = 1 / (2 * n) := by rw [div_div]
    linarith
  · have hlog := Real.log_le_log hn0 hnt
    linarith

/-- Ramaré 1995, p. 658, the numerical constant in the proof of
Lemma 3.3. GammaBounds and twelve exponential series terms certify it. -/
theorem gamma_exp_le_09105 : 3 * exp (-1 - eulerMascheroniConstant / 3) ≤ 0.9105 := by
  have hseries := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 + 0.57720 / 3) 12
  have hnum : (3 / 0.9105 : ℝ) ≤ exp (1 + 0.57720 / 3) := by
    calc
      (3 / 0.9105 : ℝ) ≤ ∑ i ∈ range 12, (1 + 0.57720 / 3 : ℝ)^i / i.factorial := by
        norm_num [sum_range_succ]
      _ ≤ _ := hseries
  have hexp : exp (1 + 0.57720 / 3) ≤ exp (1 + eulerMascheroniConstant / 3) := by
    apply Real.exp_le_exp.mpr
    linarith [LeanLab.ChenExplicit.Gamma.gamma_gt]
  rw [show -1 - eulerMascheroniConstant / 3 = -(1 + eulerMascheroniConstant / 3) by ring,
    Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.9105)).mp (hnum.trans hexp)
  linarith

/-- Ramaré 1995, Lemma 3.3, first estimate, p. 657. For every positive
real t, the harmonic sum up to t differs from log t plus gamma by at most
0.9105 times t to the power negative one third. The range below 1 follows
from the optimization on p. 658. -/
theorem lemma33_harmonic {t : ℝ} (ht : 0 < t) :
    |(harmonic ⌊t⌋₊ : ℝ) - log t - eulerMascheroniConstant| ≤
      0.9105 * t ^ (-1 / 3 : ℝ) := by
  have hmax (g t : ℝ) (ht : 0 < t) :
      (-log t - g) * t ^ (1 / 3 : ℝ) ≤ 3 * exp (-1 - g / 3) := by
    let y := -(log t + g) / 3
    have hcoeff : -log t - g = 3 * y := by dsimp [y]; ring
    have hroot : t ^ (1 / 3 : ℝ) = exp (-y) * exp (-g / 3) := by
      rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
      congr 1
      dsimp [y]
      ring
    rw [hcoeff, hroot]
    calc
      (3 * y) * (exp (-y) * exp (-g / 3)) = (3 * exp (-g / 3)) * (y * exp (-y)) := by ring
      _ ≤ (3 * exp (-g / 3)) * exp (-1) :=
        mul_le_mul_of_nonneg_left (Real.mul_exp_neg_le_exp_neg_one y) (by positivity)
      _ = 3 * exp (-1 - g / 3) := by
        rw [mul_assoc, ← Real.exp_add,
          show -g / 3 + -1 = -1 - g / 3 by ring]
  have hrpos : 0 < t ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos ht _
  rw [show (-1 / 3 : ℝ) = -(1 / 3) by ring, Real.rpow_neg ht.le,
    ← div_eq_mul_inv, le_div_iff₀ hrpos]
  by_cases ht1 : t < 1
  · have hf : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht1
    simp only [hf, harmonic_zero, Rat.cast_zero, zero_sub]
    have hu := (hmax eulerMascheroniConstant t ht).trans gamma_exp_le_09105
    have hlog : log t ≤ 0 := Real.log_nonpos ht.le ht1.le
    have hr : t ^ (1 / 3 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1.le (by norm_num)
    have hl : (log t + eulerMascheroniConstant) * t ^ (1 / 3 : ℝ) ≤ 0.9105 := by
      calc
        (log t + eulerMascheroniConstant) * t ^ (1 / 3 : ℝ) ≤
            (2 / 3) * t ^ (1 / 3 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hrpos.le
          linarith [Real.eulerMascheroniConstant_lt_two_thirds]
        _ ≤ 2 / 3 := by nlinarith
        _ ≤ 0.9105 := by norm_num
    have he : |(-log t - eulerMascheroniConstant) * t ^ (1 / 3 : ℝ)| ≤ 0.9105 :=
      abs_le.mpr ⟨by nlinarith, hu⟩
    simpa only [abs_mul, abs_of_pos hrpos] using he
  · have ht1' : 1 ≤ t := le_of_not_gt ht1
    have hn : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using ht1')
    have hnt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht.le
    have htn : t ≤ (⌊t⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one t).le
    have hrle : t ^ (1 / 3 : ℝ) ≤ t := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht1' (by norm_num : (1 / 3 : ℝ) ≤ 1)
    by_cases hn1 : ⌊t⌋₊ = 1
    · have ht2 : t ≤ 2 := by
        rw [hn1] at htn
        norm_num at htn
        exact htn
      have hlog0 : 0 ≤ log t := Real.log_nonneg ht1'
      have hlog2 : log t ≤ log 2 := Real.log_le_log ht ht2
      have herr : |(harmonic ⌊t⌋₊ : ℝ) - log t - eulerMascheroniConstant| ≤ 0.45 := by
        have hH : (harmonic ⌊t⌋₊ : ℝ) = 1 := by rw [hn1]; norm_num [harmonic]
        rw [hH]
        apply abs_le.mpr
        constructor <;> linarith [LeanLab.ChenExplicit.Gamma.gamma_gt,
          Real.eulerMascheroniConstant_lt_two_thirds, Real.log_two_lt_d9]
      have hm := mul_le_mul herr (hrle.trans ht2) hrpos.le (by norm_num : (0 : ℝ) ≤ 0.45)
      norm_num at hm
      linarith
    · have hn2 : (2 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast (show 2 ≤ ⌊t⌋₊ by omega)
      have herr := harmonic_error_le_half_inv hn hnt htn
      have hm := mul_le_mul herr hrle hrpos.le
        (by positivity : (0 : ℝ) ≤ 1 / (2 * (⌊t⌋₊ : ℝ)))
      have hb : 1 / (2 * (⌊t⌋₊ : ℝ)) * t ≤ 0.75 := by
        rw [show 1 / (2 * (⌊t⌋₊ : ℝ)) * t = t / (2 * (⌊t⌋₊ : ℝ)) by ring,
          div_le_iff₀ (by positivity)]
        linarith
      linarith

/-- Ramaré 1995, Lemma 3.1, p. 656, in the printed notation with
mu squared weights. This is the same theorem as lemma31. -/
theorem lemma31_moebius (F : ArithmeticFunction ℝ) (hF : F.IsMultiplicative)
    (hpos : ∀ k, 0 ≤ F k) (x : ℝ) (hx : 0 ≤ x) (d : ℕ) (hd : d ≠ 0) :
    (∑ m ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius m : ℝ)^2 * F m) ≤
      (∏ p ∈ d.primeFactors, (1 + F p)) *
        ∑ m ∈ (Icc 1 ⌊x⌋₊).filter (fun m => Nat.Coprime m d),
          (ArithmeticFunction.moebius m : ℝ)^2 * F m ∧
    (∏ p ∈ d.primeFactors, (1 + F p)) *
        (∑ m ∈ (Icc 1 ⌊x⌋₊).filter (fun m => Nat.Coprime m d),
          (ArithmeticFunction.moebius m : ℝ)^2 * F m) ≤
      ∑ m ∈ Icc 1 ⌊x * (d : ℝ)⌋₊, (ArithmeticFunction.moebius m : ℝ)^2 * F m := by
  have esum : ∀ s : Finset ℕ,
      (∑ m ∈ s, (ArithmeticFunction.moebius m : ℝ)^2 * F m) =
        ∑ m ∈ s.filter Squarefree, F m := by
    intro s
    rw [sum_filter]
    apply sum_congr rfl
    intro m _
    by_cases hsq : Squarefree m
    · have hm : (ArithmeticFunction.moebius m : ℝ)^2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      rw [hm, one_mul, ite_eq_left hsq]
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      simp [hsq]
  have hfilt : ((Icc 1 ⌊x⌋₊).filter (fun m => Nat.Coprime m d)).filter Squarefree =
      (Icc 1 ⌊x⌋₊).filter (fun m => Squarefree m ∧ Nat.Coprime m d) := by
    ext m
    simp only [mem_filter]
    tauto
  simp_rw [esum]
  rw [hfilt]
  exact lemma31 F hF hpos x hx d hd

/-- QUESTION for independent source review. The literal second estimate
of Ramaré 1995 Lemma 3.3, p. 657, is incompatible with the cited
Riesel and Vaughan 1983 Lemma 1, p. 48. The printed coefficient of the
first Stieltjes constant is one. The cited formula has coefficient two.
This proof compares the two vanishing errors and uses the same proved
logarithmic harmonic limit for the Stieltjes constant. -/
theorem lemma33_divisor_printed_false : ¬ ∀ t : ℝ, 0 < t →
    |(∑ m ∈ Icc 1 ⌊t⌋₊, (m.divisors.card : ℝ) / m) -
        (1 / 2) * log t ^ 2 - 2 * eulerMascheroniConstant * log t -
        eulerMascheroniConstant ^ 2 + LeanLab.RieselVaughan1983.stieltjes1| ≤
      1.641 * t ^ (-(1 / 3 : ℝ)) := by
  let g := LeanLab.RieselVaughan1983.stieltjes1
  have hg : g < 0 := by
    change LeanLab.RieselVaughan1983.stieltjes1 < 0
    have hs := LeanLab.RieselVaughan1983.sigma_bound_stieltjes1 2 (by decide)
    have he : LeanLab.RieselVaughan1983.cseq 2 = log 2 / 4 - log 2 ^ 2 / 2 := by
      norm_num [LeanLab.RieselVaughan1983.cseq, LeanLab.RieselVaughan1983.Lsum,
        show Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
      ring
    rw [he, abs_le] at hs
    norm_num at hs
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  let f : ℝ → ℝ := fun t =>
    (∑ m ∈ Icc 1 ⌊t⌋₊, (m.divisors.card : ℝ) / m) -
      (1 / 2) * log t ^ 2 - 2 * eulerMascheroniConstant * log t - eulerMascheroniConstant ^ 2
  intro h
  change ∀ t : ℝ, 0 < t → |f t + g| ≤ 1.641 * t ^ (-(1 / 3 : ℝ)) at h
  have ht : Tendsto (fun t : ℝ => (2 * 1.641) * t ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (2 * 1.641)
  have hb : ∀ᶠ t : ℝ in atTop, |g| ≤ (2 * 1.641) * t ^ (-(1 / 3 : ℝ)) := by
    filter_upwards [eventually_ge_atTop (16 : ℝ)] with t ht16
    have h1 := h t (by linarith)
    have h2 := LeanLab.RieselVaughan1983.lemma1_ge16_stieltjes1 t ht16
    change |f t + 2 * g| < (1641 / 1000) * t ^ (-(1 / 3 : ℝ)) at h2
    have htriangle := norm_sub_le (f t + 2 * g) (f t + g)
    simp only [Real.norm_eq_abs, show (f t + 2 * g) - (f t + g) = g by ring] at htriangle
    linarith
  have hz : |g| ≤ 0 := ge_of_tendsto ht hb
  have he : g = 0 := abs_nonpos_iff.mp hz
  linarith

/-- Corrected second estimate corresponding to Ramaré 1995 Lemma 3.3,
p. 657. The coefficient two is the one in the cited Riesel and Vaughan
1983 Lemma 1, p. 48. The lab has already proved that cited result. -/
theorem lemma33_divisor_corrected {t : ℝ} (ht : 0 < t) :
    |(∑ m ∈ Icc 1 ⌊t⌋₊, (m.divisors.card : ℝ) / m) -
        (1 / 2) * log t ^ 2 - 2 * eulerMascheroniConstant * log t -
        eulerMascheroniConstant ^ 2 + 2 * LeanLab.RieselVaughan1983.stieltjes1| ≤
      1.641 * t ^ (-(1 / 3 : ℝ)) := by
  have h := LeanLab.RieselVaughan1983.StieltjesCert.lemma1_stieltjes1_unconditional t ht
  simpa only [LeanLab.RieselVaughan1983.lem1E,
    show (1641 / 1000 : ℝ) = 1.641 by norm_num] using h.le

/-- Diagnostic for the sealed Decomp1526c sum_rep_Ioc_eq leaf. At a = 4
and b = 2 the left side is zero and the right side is negative log squared 2.
This is a lab statement issue, already recorded in PROGRESS, not a claim
about the paper. No statement in file c is changed. -/
theorem sum_rep_Ioc_eq_counterexample :
    (∑ N ∈ Ioc 4 2, rep N) ≠
      ∑ p ∈ (range (2 + 1)).filter Nat.Prime,
        Real.log p * (Chebyshev.theta ((2 - p : ℕ) : ℝ) - Chebyshev.theta ((4 - p : ℕ) : ℝ)) := by
  have hI : Ioc 4 2 = (∅ : Finset ℕ) := by decide
  have hP : (range (2 + 1)).filter Nat.Prime = ({2} : Finset ℕ) := by decide
  rw [hI, sum_empty, hP, sum_singleton]
  norm_num [theta_natCast_eq, sum_filter, sum_range_succ]

/-- Vacuity: `h(15)` has two odd prime factors, so the product in `oddFac` is not empty;
`h ≥ 1` always. -/
example : 1 ≤ oddFac 15 := oddFac_one_le 15

end LeanLab.Ramare1995.Decomp1526b
