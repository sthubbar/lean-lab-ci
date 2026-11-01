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

set_option maxHeartbeats 4000000
set_option maxRecDepth 400000

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

private lemma squarefree_prod_of_prime {t : Finset ℕ} (h : ∀ p ∈ t, Nat.Prime p) :
    Squarefree (∏ p ∈ t, p) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.squarefree_mul_iff]
    refine ⟨?_, (h a (Finset.mem_insert_self a s)).squarefree,
      ih fun p hp => h p (Finset.mem_insert_of_mem hp)⟩
    refine Nat.Coprime.prod_right fun p hp => ?_
    exact (Nat.coprime_primes (h a (Finset.mem_insert_self a s))
      (h p (Finset.mem_insert_of_mem hp))).mpr fun hEq => ha (hEq.symm ▸ hp)

/-- `∏ (1 + F p)` over a set of primes is the sum of `∏ F p` over its subsets. -/
private lemma prod_one_add_eq_sum_powerset (s : Finset ℕ) (F : ℕ → ℝ) :
    ∏ p ∈ s, (1 + F p) = ∑ t ∈ s.powerset, ∏ p ∈ t, F p := by
  have hswap : ∏ p ∈ s, (1 + F p) = ∏ p ∈ s, (F p + 1) :=
    Finset.prod_congr rfl fun p _ => add_comm (1 : ℝ) (F p)
  rw [hswap]
  have h := Finset.prod_add F (fun _ => (1 : ℝ)) s
  rw [h]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp

/-- Odd squarefree divisors of `m ≠ 0` correspond, by their set of prime factors, to the subsets
of the odd primes of `m`. -/
private lemma sum_sqfree_odd_divisors_eq_powerset {m : ℕ} (hm : m ≠ 0) (W : ℕ → ℝ) :
    ∑ d ∈ m.divisors.filter (fun d => Squarefree d ∧ ¬ Even d), ∏ p ∈ d.primeFactors, W p
      = ∑ t ∈ (m.primeFactors.filter (2 < ·)).powerset, ∏ p ∈ t, W p := by
  classical
  refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, mem_powerset, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨hdvd, -⟩, hsq, hodd⟩ := hd
    have hd0 : d ≠ 0 :=
      (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hm)).ne'
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    have hp2 : 2 < p := by
      rcases Nat.lt_or_ge 2 p with hlt | hge
      · exact hlt
      · exact absurd (even_iff_two_dvd.mpr (le_antisymm hge hp.1.two_le ▸ hp.2.1)) hodd
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp.1, hp.2.1.trans hdvd, hm⟩, hp2⟩
  · intro d1 hd1 d2 hd2 heq
    simp only [mem_filter] at hd1 hd2
    rw [← Nat.prod_primeFactors_of_squarefree hd1.2.1, heq,
      Nat.prod_primeFactors_of_squarefree hd2.2.1]
  · intro t ht
    simp only [mem_powerset] at ht
    have hprime : ∀ p ∈ t, Nat.Prime p := fun p hp =>
      (Nat.mem_primeFactors.mp (mem_filter.mp (ht hp)).1).1
    refine ⟨∏ p ∈ t, p, ?_, Nat.primeFactors_prod hprime⟩
    rw [mem_filter]
    have hpos : (0 : ℕ) < ∏ p ∈ t, p := Finset.prod_pos fun p hp => (hprime p hp).pos
    refine ⟨Nat.mem_divisors.mpr ⟨?_, hm⟩, squarefree_prod_of_prime hprime, ?_⟩
    · exact (Finset.prod_dvd_prod_of_subset t m.primeFactors (fun p => p)
        (ht.trans (Finset.filter_subset _ _))).trans (Nat.prod_primeFactors_dvd m)
    · rw [even_iff_two_dvd]
      intro h2
      have hmem : 2 ∈ (∏ p ∈ t, p).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hpos.ne'⟩
      rw [Nat.primeFactors_prod hprime] at hmem
      have := ht hmem
      simp only [mem_filter] at this
      omega
  · intro d _
    rfl

/-- LEAF. Divisor expansion `h(m)² = Σ_{d ∣ m} g(d)` for `m ≥ 1`: for an odd prime `p`,
`((p - 1)/(p - 2))² = 1 + (2p - 3)/(p - 2)²`, and expanding the product over the odd primes of
`m` gives the sum over odd squarefree divisors. Halberstam-Richert Ch. 3, multiplicative
expansions; Ramaré 1995 Section 3, p. 656. Unit U-1526. -/
theorem oddFac_sq_eq_sum_divisors {m : ℕ} (hm : m ≠ 0) :
    oddFac m ^ 2 = ∑ d ∈ m.divisors, gfun d := by
  classical
  have hW : ∀ p ∈ m.primeFactors.filter (2 < ·),
      (((p : ℝ) - 1) / ((p : ℝ) - 2)) ^ 2 =
        1 + (2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2 := by
    intro p hp
    simp only [mem_filter] at hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
    have hne : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  have hfac : oddFac m ^ 2 = ∏ p ∈ m.primeFactors.filter (2 < ·),
      (1 + (2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2) := by
    unfold oddFac
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl hW
  have hpa : ∏ p ∈ m.primeFactors.filter (2 < ·),
        (1 + (2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2)
      = ∑ t ∈ (m.primeFactors.filter (2 < ·)).powerset,
          ∏ p ∈ t, ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2) :=
    prod_one_add_eq_sum_powerset _ _
  have hg : ∑ d ∈ m.divisors, gfun d
      = ∑ d ∈ m.divisors.filter (fun d => Squarefree d ∧ ¬ Even d),
          ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2) := by
    have h1 : ∑ d ∈ m.divisors, gfun d
        = ∑ d ∈ m.divisors, if (Squarefree d ∧ ¬ Even d)
            then (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2)) else 0 := by
      refine Finset.sum_congr rfl fun d _ => ?_
      rfl
    rw [h1, Finset.sum_filter]
  rw [hfac, hpa, hg, sum_sqfree_odd_divisors_eq_powerset hm
    (fun p => (2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2)]

/-- The multiples of `d > 0` in `[1, n]` number `n / d`. -/
private lemma card_filter_dvd_Icc (n d : ℕ) :
    #((Icc 1 n).filter fun m => d ∣ m) = n / d := by
  have h : (Icc 1 n).filter (fun m => d ∣ m)
      = (range (n + 1)).filter (fun k => k ≠ 0 ∧ d ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨Nat.lt_succ_of_le h2, by omega, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, by omega⟩, h3⟩
  rw [h, Nat.card_multiples' n d]

/-- Divisors of `m ∈ [1, n]` are the divisors of `m` lying in `[1, n]`. -/
private lemma sum_divisors_eq_sum_Icc (n : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ Icc 1 n, ∑ d ∈ m.divisors, f d
      = ∑ m ∈ Icc 1 n, ∑ d ∈ Icc 1 n, if d ∣ m then f d else 0 := by
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [mem_Icc] at hm
  have hm0 : m ≠ 0 := by omega
  rw [← Finset.sum_filter]
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_Icc]
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos h1 (by omega), (Nat.le_of_dvd (by omega) h1).trans hm.2⟩, h1⟩
  · rintro ⟨⟨-, _⟩, h3⟩
    exact ⟨h3, hm0⟩

/-- LEAF. Interchange and `⌊n/d⌋ ≤ n/d`: for `g ≥ 0`,
`Σ_{m ≤ n} Σ_{d ∣ m} g(d) ≤ n Σ_{d ≤ n} g(d)/d`. Elementary, Nathanson GTM 164 Section 7.4;
Montgomery-Vaughan, Multiplicative Number Theory I, Section 2.1. Unit U-1526. -/
theorem sum_Icc_sum_divisors_le (n : ℕ) :
    ∑ m ∈ Icc 1 n, ∑ d ∈ m.divisors, gfun d ≤ n * ∑ d ∈ Icc 1 n, gfun d / d := by
  rw [sum_divisors_eq_sum_Icc n gfun, Finset.sum_comm]
  have hstep : ∀ d ∈ Icc 1 n,
      ∑ m ∈ Icc 1 n, (if d ∣ m then gfun d else 0)
        = gfun d * ((n / d : ℕ) : ℝ) := by
    intro d hd
    simp only [mem_Icc] at hd
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_dvd_Icc n d, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hstep]
  calc ∑ d ∈ Icc 1 n, gfun d * ((n / d : ℕ) : ℝ)
      ≤ ∑ d ∈ Icc 1 n, gfun d * ((n : ℝ) / d) :=
        Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left Nat.cast_div_le (gfun_nonneg d)
    _ = ∑ d ∈ Icc 1 n, n * (gfun d / d) := Finset.sum_congr rfl fun d _ => by ring
    _ = n * ∑ d ∈ Icc 1 n, gfun d / d :=
        (Finset.mul_sum (s := Icc 1 n) (f := fun d => gfun d / d) (a := (n : ℝ))).symm

/-- LEAF. Rankin-free Euler product bound: `Σ_{d ≤ n} g(d)/d ≤ ∏_{2 < p ≤ n} (1 + g(p)/p)`,
since `g(d)/d` is multiplicative, supported on odd squarefree `d`, and every such `d ≤ n`
has its primes `≤ n`. Montgomery-Vaughan I, Section 2.1. Unit U-1526. -/
theorem sum_gfun_div_le_prod (n : ℕ) :
    ∑ d ∈ Icc 1 n, gfun d / d ≤
      ∏ p ∈ (Icc 3 n).filter Nat.Prime,
        (1 + (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2)) := by
  classical
  set W : ℕ → ℝ := fun p => (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2) with hWdef
  set sf := (Icc 1 n).filter (fun d => Squarefree d ∧ ¬ Even d) with hsf
  set S := (Icc 3 n).filter Nat.Prime with hS
  have hWnonneg : ∀ p ∈ S, 0 ≤ W p := by
    intro p hp
    simp only [hS, mem_filter, mem_Icc] at hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.1.1
    have hnum : 0 ≤ 2 * (p : ℝ) - 3 := by linarith
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 2) ^ 2 := by
      have h1 : (0 : ℝ) < p := by linarith
      have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      positivity
    simp only [hWdef]
    exact div_nonneg hnum hden.le
  -- every odd prime factor of a squarefree odd `d` is at least `3`
  have hpf3 : ∀ d : ℕ, Squarefree d → ¬ Even d → ∀ p ∈ d.primeFactors, 3 ≤ p := by
    intro d _ hodd p hp
    rw [Nat.mem_primeFactors] at hp
    have hp2 : 2 < p := by
      rcases Nat.lt_or_ge 2 p with h | h
      · exact h
      · exact absurd (even_iff_two_dvd.mpr (le_antisymm h hp.1.two_le ▸ hp.2.1)) hodd
    omega
  -- rewrite `g / d` as a product over the prime factors
  have h1 : ∑ d ∈ Icc 1 n, gfun d / d = ∑ d ∈ sf, ∏ p ∈ d.primeFactors, W p := by
    have hite : ∑ d ∈ Icc 1 n, gfun d / d
        = ∑ d ∈ Icc 1 n, if (Squarefree d ∧ ¬ Even d)
            then (∏ p ∈ d.primeFactors, W p) else 0 := by
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [mem_Icc] at hd
      have hd0 : (d : ℝ) ≠ 0 := by
        have : d ≠ 0 := by omega
        exact_mod_cast this
      by_cases hc : Squarefree d ∧ ¬ Even d
      · rw [if_pos hc]
        have hgf : gfun d = ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2) := by
          simp only [gfun, if_pos hc]
        have hdeq : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
          rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hc.1]
        have hfac : ∀ p ∈ d.primeFactors,
            ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2) / p = W p := by
          intro p hp
          have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hpf3 d hc.1 hc.2 p hp
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
          simp only [hWdef]
          field_simp
        calc gfun d / (d : ℝ)
            = (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2)) / (d : ℝ) := by
                rw [hgf]
          _ = (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2)) /
                (∏ p ∈ d.primeFactors, (p : ℝ)) := by rw [hdeq]
          _ = ∏ p ∈ d.primeFactors,
                (((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2) / p) :=
                (Finset.prod_div_distrib (s := d.primeFactors)
                  (f := fun p => (2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2)
                  (g := fun p => (p : ℝ))).symm
          _ = ∏ p ∈ d.primeFactors, W p := Finset.prod_congr rfl hfac
      · rw [if_neg hc]
        have hz : gfun d = 0 := by simp only [gfun, if_neg hc]
        rw [hz, zero_div]
    rw [hite, ← Finset.sum_filter]
  rw [h1]
  -- the prime-factor sets of the odd squarefree `d ∈ [1,n]` are subsets of `S`
  have hsub : sf.image (fun d => d.primeFactors) ⊆ S.powerset := by
    intro t ht
    simp only [mem_image, hsf, mem_filter, mem_Icc] at ht
    obtain ⟨d, ⟨⟨hd1, hdn⟩, hsq, hodd⟩, rfl⟩ := ht
    rw [mem_powerset]
    intro p hp
    obtain ⟨hp3, hp1, hpdvd⟩ : 3 ≤ p ∧ Nat.Prime p ∧ p ∣ d :=
      ⟨hpf3 d hsq hodd p hp, (Nat.mem_primeFactors.mp hp).1, (Nat.mem_primeFactors.mp hp).2.1⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp3, (Nat.le_of_dvd (by omega) hpdvd).trans hdn⟩, hp1⟩
  have hinj : Set.InjOn (fun d => d.primeFactors) (sf : Set ℕ) := by
    intro d1 hd1 d2 hd2 heq
    simp only [Finset.mem_coe, hsf, mem_filter] at hd1 hd2
    have heq' : d1.primeFactors = d2.primeFactors := heq
    rw [← Nat.prod_primeFactors_of_squarefree hd1.2.1, heq',
      Nat.prod_primeFactors_of_squarefree hd2.2.1]
  have himg : ∑ d ∈ sf, ∏ p ∈ d.primeFactors, W p
      = ∑ T ∈ sf.image (fun d => d.primeFactors), ∏ p ∈ T, W p :=
    (Finset.sum_image (f := fun t => ∏ p ∈ t, W p) (s := sf)
      (g := fun d => d.primeFactors) hinj).symm
  rw [himg]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_).trans_eq ?_
  · intro T hT _
    exact Finset.prod_nonneg fun p hp => hWnonneg p (mem_powerset.mp hT hp)
  · exact (prod_one_add_eq_sum_powerset S W).symm

/-- A telescoping bound for `Σ 2/(p - 2)²` over an interval of integers. -/
private lemma sum_Icc_shift_inv_sq_aux (N : ℕ) (hN : 523 ≤ N) :
    ∑ p ∈ Icc 523 N, (2 : ℝ) / ((p : ℝ) - 2) ^ 2
      ≤ 1 / 520 + 1 / 521 - 1 / ((N : ℝ) - 2) - 1 / ((N : ℝ) - 1) := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    push_cast
    norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have hN0 : (523 : ℝ) ≤ N := by
      have : 523 ≤ N := by omega
      exact_mod_cast this
    have e1 : (N : ℝ) + 1 - 2 = (N : ℝ) - 1 := by ring
    have e2 : (N : ℝ) + 1 - 1 = (N : ℝ) := by ring
    rw [e1, e2]
    have hkey : (2 : ℝ) / ((N : ℝ) - 1) ^ 2 ≤ 1 / ((N : ℝ) - 2) - 1 / (N : ℝ) := by
      have h1 : (0 : ℝ) < (N : ℝ) - 2 := by linarith
      have h2 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
      have h3 : (0 : ℝ) < (N : ℝ) := by linarith
      have hl : (0 : ℝ) < ((N : ℝ) - 1) ^ 2 := by positivity
      have hr : (0 : ℝ) < ((N : ℝ) - 2) * (N : ℝ) := by positivity
      have e : 1 / ((N : ℝ) - 2) - 1 / (N : ℝ) = 2 / (((N : ℝ) - 2) * (N : ℝ)) := by
        field_simp
        ring
      rw [e, div_le_div_iff₀ hl hr]
      nlinarith
    linarith

/-- The tail `Σ 2/(p - 2)²` from `523` is at most `1/520 + 1/521`. -/
private lemma sum_Icc_shift_inv_sq_le (N : ℕ) :
    ∑ p ∈ Icc 523 N, (2 : ℝ) / ((p : ℝ) - 2) ^ 2 ≤ 1 / 520 + 1 / 521 := by
  rcases Nat.lt_or_ge N 523 with hN | hN
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity
  · have h := sum_Icc_shift_inv_sq_aux N hN
    have hN0 : (523 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 : (0 : ℝ) < (N : ℝ) - 2 := by linarith
    have h2 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have : 0 ≤ 1 / ((N : ℝ) - 2) + 1 / ((N : ℝ) - 1) := by positivity
    linarith

/-- `∏ (1 + g) ≤ exp (Σ g)` when `g ≥ 0` on the index set. -/
private lemma prod_one_add_le_exp_sum (s : Finset ℕ) (g : ℕ → ℝ) (h : ∀ i ∈ s, 0 ≤ g i) :
    ∏ i ∈ s, (1 + g i) ≤ Real.exp (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Real.exp_add]
    have hga : 0 ≤ g a := h a (Finset.mem_insert_self a s)
    have hpa : 1 + g a ≤ Real.exp (g a) := by linarith [Real.add_one_le_exp (g a)]
    have hpos : 0 < ∏ i ∈ s, (1 + g i) :=
      Finset.prod_pos fun i hi => by linarith [h i (Finset.mem_insert_of_mem hi)]
    have hih := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul hpa hih hpos.le (Real.exp_pos _).le

/-- A product of factors `1 + g ≥ 1` is at least `1`. -/
private lemma one_le_prod_one_add {s : Finset ℕ} {g : ℕ → ℝ} (h : ∀ p ∈ s, 0 ≤ g p) :
    1 ≤ ∏ p ∈ s, (1 + g p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : 1 ≤ 1 + g a := by linarith [h a (Finset.mem_insert_self a t)]
    have h2 : 1 ≤ ∏ p ∈ t, (1 + g p) := ih fun p hp => h p (Finset.mem_insert_of_mem hp)
    have h3 : (0 : ℝ) ≤ ∏ p ∈ t, (1 + g p) := by linarith
    have h4 : (0 : ℝ) ≤ 1 + g a := by linarith
    exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1) (mul_le_mul h1 h2 zero_le_one h4)

/-- Monotonicity of such a product in the index set. -/
private lemma prod_le_prod_one_add_of_subset {s₁ s₂ : Finset ℕ} (h : s₁ ⊆ s₂) {g : ℕ → ℝ}
    (hg : ∀ p ∈ s₂, 0 ≤ g p) : ∏ p ∈ s₁, (1 + g p) ≤ ∏ p ∈ s₂, (1 + g p) := by
  have hb : 0 ≤ ∏ p ∈ s₁, (1 + g p) := Finset.prod_nonneg fun p hp => by linarith [hg p (h hp)]
  have hone : 1 ≤ ∏ p ∈ s₂ \ s₁, (1 + g p) :=
    one_le_prod_one_add fun p hp => hg p (Finset.mem_sdiff.mp hp).1
  calc ∏ p ∈ s₁, (1 + g p)
      ≤ (∏ p ∈ s₂ \ s₁, (1 + g p)) * ∏ p ∈ s₁, (1 + g p) := le_mul_of_one_le_left hb hone
    _ = ∏ p ∈ s₂, (1 + g p) := Finset.prod_sdiff h

/-- LEAF. Numerical bound: `∏_{2 < p ≤ n} (1 + (2p - 3)/(p (p - 2)²)) ≤ 2.65` for every `n`.
The full product is `2.63985...`; a proof can bound the primes up to 100 exactly and the
tail by `∏_{k > 100} (1 + 2/(k - 2)²) ≤ exp (2/97)`. Python, run 20261025T2003Z-426;
Ramaré 1995 Section 3, p. 656 to 667 for products of this kind. Unit U-1526. -/
theorem prod_odd_primes_le (n : ℕ) :
    ∏ p ∈ (Icc 3 n).filter Nat.Prime,
        (1 + (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2)) ≤ 2.65 := by
  classical
  set g : ℕ → ℝ := fun p => (2 * (p : ℝ) - 3) / ((p : ℝ) * ((p : ℝ) - 2) ^ 2) with hg
  have hPL : (Icc 3 521).filter Nat.Prime = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521} := by
    decide
  have hheadlit : ∏ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521} : Finset ℕ), (1 + g p) ≤ 263847 / 100000 := by
    norm_num [hg]
  have hhead : ∏ p ∈ (Icc 3 521).filter Nat.Prime, (1 + g p) ≤ 263847 / 100000 := by
    rw [hPL]
    exact hheadlit
  have hgpos : ∀ p : ℕ, 3 ≤ p → 0 ≤ g p := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have hnum : 0 ≤ 2 * (p : ℝ) - 3 := by linarith
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 2) ^ 2 := by
      have h1 : (0 : ℝ) < (p : ℝ) := by linarith
      have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      positivity
    simp only [hg]
    exact div_nonneg hnum hden.le
  rcases Nat.lt_or_ge n 521 with hn | hn
  · have hsub : (Icc 3 n).filter Nat.Prime ⊆ (Icc 3 521).filter Nat.Prime := by
      intro p hp
      simp only [mem_filter, mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
    have hle := prod_le_prod_one_add_of_subset hsub
      (fun p hp => hgpos p (by simp only [mem_filter, mem_Icc] at hp; omega))
    linarith
  · have hsplit : Icc 3 n = Icc 3 521 ∪ Ioc 521 n := by
      ext k
      simp only [mem_union, mem_Icc, mem_Ioc]
      omega
    rw [hsplit, Finset.filter_union]
    rw [Finset.prod_union (by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [mem_filter, mem_Icc] at ha
      simp only [mem_filter, mem_Ioc] at hb
      omega)]
    have hnonneg : ∀ p ∈ (Ioc 521 n).filter Nat.Prime, 0 ≤ g p := by
      intro p hp
      simp only [mem_filter, mem_Ioc] at hp
      exact hgpos p (by omega)
    have htail_nn : 0 ≤ ∏ p ∈ (Ioc 521 n).filter Nat.Prime, (1 + g p) :=
      Finset.prod_nonneg fun p hp => by linarith [hnonneg p hp]
    have htail : ∏ p ∈ (Ioc 521 n).filter Nat.Prime, (1 + g p) ≤ (265 / 100) / (263847 / 100000) := by
      have hexp : ∏ p ∈ (Ioc 521 n).filter Nat.Prime, (1 + g p)
          ≤ Real.exp (∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p) :=
        prod_one_add_le_exp_sum _ g hnonneg
      have hsum_le : ∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p ≤ 1 / 520 + 1 / 521 := by
        have hpt : ∀ p ∈ (Ioc 521 n).filter Nat.Prime, g p ≤ 2 / ((p : ℝ) - 2) ^ 2 := by
          intro p hp
          simp only [mem_filter, mem_Ioc] at hp
          have hp3 : (3 : ℝ) ≤ p := by
            have : (3 : ℕ) ≤ p := by omega
            exact_mod_cast this
          have h1 : (0 : ℝ) < (p : ℝ) := by linarith
          have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
          have hsq : (0 : ℝ) < ((p : ℝ) - 2) ^ 2 := by positivity
          have hden : 0 < (p : ℝ) * ((p : ℝ) - 2) ^ 2 := by positivity
          simp only [hg]
          rw [div_le_div_iff₀ hden hsq]
          nlinarith
        refine (Finset.sum_le_sum hpt).trans ?_
        have hsub2 : (Ioc 521 n).filter Nat.Prime ⊆ Icc 523 n := by
          intro p hp
          simp only [mem_filter, mem_Ioc] at hp
          obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
          refine mem_Icc.mpr ⟨?_, hp2⟩
          have hne : p ≠ 522 := by
            rintro rfl
            norm_num at hpp
          omega
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub2
          fun k _ _ => by positivity).trans (sum_Icc_shift_inv_sq_le n)
      have hexp2 : Real.exp (∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p)
          ≤ 1 + (1 / 520 + 1 / 521) + (1 / 520 + 1 / 521) ^ 2 := by
        have h0 : (0 : ℝ) ≤ ∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p :=
          Finset.sum_nonneg hnonneg
        have hb := Real.exp_bound (x := ∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p) (n := 2)
          (by rw [abs_le]; constructor <;> linarith) (by norm_num)
        have h2 : |∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p| =
            ∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p := abs_of_nonneg h0
        rw [h2] at hb
        have hs : (∑ m ∈ Finset.range 2,
            (∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p) ^ m / (m.factorial : ℝ))
            = 1 + ∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p := by
          simp [Finset.sum_range_succ]
        rw [hs] at hb
        have h3 : (∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p) ^ 2 *
            ((↑(Nat.succ 2) : ℝ) / ((↑(Nat.factorial 2) : ℝ) * ↑(2 : ℕ)))
            = 3 / 4 * (∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p) ^ 2 := by
          have hc : ((↑(Nat.succ 2) : ℝ) / ((↑(Nat.factorial 2) : ℝ) * ↑(2 : ℕ))) = 3 / 4 := by
            norm_num
          rw [hc]
          ring
        rw [h3] at hb
        have h4 := (abs_le.mp hb).2
        have h5 : (∑ p ∈ (Ioc 521 n).filter Nat.Prime, g p) ^ 2
            ≤ (1 / 520 + 1 / 521) ^ 2 := by nlinarith
        nlinarith
      have hexp3 : (1 : ℝ) + (1 / 520 + 1 / 521) + (1 / 520 + 1 / 521) ^ 2
          ≤ (265 / 100) / (263847 / 100000) := by
        have ht : (1 / 520 + 1 / 521 : ℝ) = 1041 / 270920 := by norm_num
        rw [ht]
        norm_num
      exact hexp.trans (hexp2.trans hexp3)
    have hfin : (263847 / 100000) * ((265 / 100) / (263847 / 100000)) ≤ (2.65 : ℝ) := by
      have h : (0 : ℝ) < 263847 / 100000 := by norm_num
      rw [mul_comm, div_mul_cancel₀ _ h.ne']
      norm_num
    exact (mul_le_mul hhead htail htail_nn (by norm_num)).trans hfin

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
