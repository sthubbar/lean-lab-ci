/-
Ramaré 1995, P0008, unit U-1526, run 20261025T2003Z-426. DECOMPOSE file c of three.
The first moment `Σ_{N even in ]X, 2X]} rep(N)` from Chebyshev bounds, and the assembly of an
EFFECTIVE density theorem of Theorem 2 type.

Ramaré's Proposition 1, Section 5, p. 678, is a sharp first moment from explicit prime number
theorems in progressions. Here only the trivial first moment is used:
`Σ_{a < p + q ≤ b} log p log q ≥ Σ_{p ≤ a} log p (θ(b - p) - θ(a - p))`, with
`a = ⌊X⌋`, `b = ⌊2X⌋`, the upper bound `θ(x) ≤ log 4 · x` of Mathlib and the lower bound
`θ(x) ≥ 0.99 x` for `x ≥ exp 60`, which follows from Rosser-Schoenfeld 1962, Illinois J.
Math. 6, Thm 4 (3.16), `θ(x) > x (1 - 1/(2 log x))` for `x ≥ 563`. That lower bound is an
analytic input, kept here as the hypothesis `hRS`, never as a leaf.

Outcome: `theorem2_effective_of_RS`, at least `X / 10^8` even `N ∈ ]X, 2X]` are sums of two
primes for every `X ≥ exp 67`, CONDITIONAL ON `hRS`; `theorem2_explicit_of_sieve`, the same
with `0.3025 / (10.6 A²)` from any explicit Selberg constant `A`. Ramaré's `X/5` needs his
Propositions 1 to 4; `theorem2_of_moments` in file a records what they must give.

The short interval input of Theorem 1 itself, Ramaré-Saouter 2003 Theorem 3, belongs to the
RamareSaouter2003 folder and is not split here.

AI-written Lean code, Claude, 2026-10-25. Checked only by the Lean kernel.
Binary Goldbach is OPEN; this is a positive lower density of sums of two primes.
-/
import Mathlib
import LeanLab.Ramare1995.Decomp1526b

open Finset Real
open scoped Classical Chebyshev

noncomputable section
namespace LeanLab.Ramare1995.Decomp1526c
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9
open LeanLab.Ramare1995.Decomp1526a LeanLab.Ramare1995.Decomp1526b

/-- LEAF. Interchange: `Σ_{a < N ≤ b} rep N = Σ_{p ≤ b} log p (θ(b - p) - θ(a - p))`, with
natural subtraction; for `p ≥ a` the second term is `θ(0) = 0`. Definition of `rep`;
Ramaré 1995 Section 5, p. 678, the opening of the proof of Proposition 1. Unit U-1526. -/
theorem sum_rep_Ioc_eq (a b : ℕ) :
    ∑ N ∈ Ioc a b, rep N =
      ∑ p ∈ (range (b + 1)).filter Nat.Prime,
        Real.log p * (θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ)) := by
  sorry

theorem theta_sub_nonneg {a b : ℕ} (hab : a ≤ b) (p : ℕ) :
    0 ≤ θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ) :=
  sub_nonneg.mpr (Chebyshev.theta_mono (by exact_mod_cast Nat.sub_le_sub_right hab p))

/-- LEAF. Drop the primes `a < p ≤ b`, whose terms are `≥ 0` by `theta_sub_nonneg`:
`Σ_{a < N ≤ b} rep N ≥ Σ_{p ≤ a} log p (θ(b - p) - θ(a - p))` for `a ≤ b`. Uses
`sum_rep_Ioc_eq`. Unit U-1526. -/
theorem sum_rep_Ioc_ge_head {a b : ℕ} (hab : a ≤ b) :
    ∑ p ∈ (range (a + 1)).filter Nat.Prime,
        Real.log p * (θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ)) ≤ ∑ N ∈ Ioc a b, rep N := by
  rw [sum_rep_Ioc_eq]
  have h_sub : (range (a + 1)).filter Nat.Prime ⊆ (range (b + 1)).filter Nat.Prime := by
    intro p hp
    rw [mem_filter] at hp ⊢
    refine ⟨?_, hp.2⟩
    rw [mem_range] at hp ⊢
    linarith
  have h_theta_mono : ∀ p, 0 ≤ θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ) := by
    intro p
    apply sub_nonneg.mpr
    apply Chebyshev.theta_mono
    exact_mod_cast Nat.sub_le_sub_right hab p
  exact sum_le_sum_of_subset_of_nonneg h_sub (fun i _ _ => mul_nonneg (Real.log_natCast_nonneg i) (h_theta_mono i))

/-- LEAF. `Σ_{p ≤ a} log p = θ(a)`. Mathlib `Chebyshev.theta_eq_sum_primesLE_log` or the
definition of `θ`. Unit U-1526. -/
theorem sum_log_primes_range (a : ℕ) :
    ∑ p ∈ (range (a + 1)).filter Nat.Prime, Real.log p = θ (a : ℝ) := by
  rw [← Nat.primesLE_eq_filter_range]
  exact (Chebyshev.theta_eq_sum_primesLE_log a).symm

/-- `θ(⌊X⌋) = θ(X) ≥ 0.99 X` for `X ≥ exp 60`, from `hRS`. -/
theorem theta_floor_ge (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 60 ≤ X) : 0.99 * X ≤ θ ((⌊X⌋₊ : ℕ) : ℝ) := by
  rw [← Chebyshev.theta_eq_theta_coe_floor]
  exact hRS X hX

/-- `exp 67 ≥ 129`, enough for every numeric side condition below. -/
theorem exp67_ge_129 : (129 : ℝ) ≤ Real.exp 67 := by
  have h2 : (2 : ℝ) ^ 67 ≤ Real.exp 67 := by
    rw [show (67 : ℝ) = ((67 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (le_of_lt Real.exp_one_gt_two) 67
  have : (129 : ℝ) ≤ 2 ^ 67 := by norm_num
  linarith

/-- `exp 60 + 1 ≤ exp 67`. -/
theorem exp60_add_one_le : Real.exp 60 + 1 ≤ Real.exp 67 := by
  have h1 : (1 : ℝ) ≤ Real.exp 60 := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 60)
  have h7 : (2 : ℝ) ≤ Real.exp 7 := by
    have h : (7 : ℝ) + 1 ≤ Real.exp 7 := Real.add_one_le_exp 7
    linarith
  have hsplit : Real.exp 67 = Real.exp 60 * Real.exp 7 := by
    rw [← Real.exp_add]; norm_num
  nlinarith

theorem log4_le : Real.log 4 ≤ 1.3863 := by
  have h_le : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    rw [this, Real.log_pow, Nat.cast_two]
  rw [h_le]
  have h2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  linarith

/-- LEAF. Pointwise lower bound for `p ≤ ⌊X⌋`, `X ≥ exp 67`:
`θ(⌊2X⌋ - p) - θ(⌊X⌋ - p) ≥ 0.5937 X - 0.99`, from `θ(⌊2X⌋ - p) ≥ 0.99 (⌊2X⌋ - p)`
(here `⌊2X⌋ - p ≥ X - 1 ≥ exp 60`), `θ(y) ≤ log 4 · y < 1.3863 y`, Mathlib
`Chebyshev.theta_le_log4_mul_x`, and `0.99 ⌊2X⌋ - 1.3863 ⌊X⌋ ≥ 0.5937 X - 0.99`.
Rosser-Schoenfeld 1962 (3.16). Unit U-1526. -/
theorem inner_lower (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 67 ≤ X) {p : ℕ} (hp : p ≤ ⌊X⌋₊) :
    0.5937 * X - 0.99 ≤
      θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ) := by
  have hX0 : 0 < X := lt_of_lt_of_le (exp_pos 67) hX
  have haX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (le_of_lt hX0)
  have hb2X : 2 * X - 1 ≤ (⌊2 * X⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (2 * X)
    linarith
  have hab : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono (by linarith)
  have hpb : p ≤ ⌊2 * X⌋₊ := le_trans hp hab
  have hpR : (p : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hp
  have hexp : Real.exp 60 + 1 ≤ Real.exp 67 := exp60_add_one_le
  have hq : Real.exp 60 ≤ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpb]
    linarith
  have hr0 : (0 : ℝ) ≤ ((⌊X⌋₊ - p : ℕ) : ℝ) := by positivity
  have h1 := hRS ((⌊2 * X⌋₊ - p : ℕ) : ℝ) hq
  have h2 := Chebyshev.theta_le_log4_mul_x hr0
  have h3 : θ ((⌊X⌋₊ - p : ℕ) : ℝ) ≤ 1.3863 * ((⌊X⌋₊ - p : ℕ) : ℝ) :=
    le_trans h2 (mul_le_mul_of_nonneg_right log4_le hr0)
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  rw [Nat.cast_sub hpb] at h1
  rw [Nat.cast_sub hp] at h3
  rw [Nat.cast_sub hpb, Nat.cast_sub hp]
  nlinarith

/-- LEAF. Dyadic prime counting: `θ(2X) - θ(X) ≥ 0.59 X` for `X ≥ exp 60`, from `hRS` at
`2X` and `θ(X) ≤ log 4 · X`. The dyadic interval form of the input on primes in
`]X, 2X]`; Rosser-Schoenfeld 1962 (3.16). Unit U-1526. -/
theorem theta_dyadic_ge (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 60 ≤ X) : 0.59 * X ≤ θ (2 * X) - θ X := by
  have hX_pos : 0 ≤ X := le_trans (exp_pos 60).le hX
  have hX2 : exp 60 ≤ 2 * X := by linarith
  have h1 : 0.99 * (2 * X) ≤ θ (2 * X) := hRS (2 * X) hX2
  have h2 : θ X ≤ Real.log 4 * X := Chebyshev.theta_le_log4_mul_x hX_pos
  have h3 : Real.log 4 ≤ 1.3863 := by
    have h_le : Real.log 4 = 2 * Real.log 2 := by
      have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [this, Real.log_pow, Nat.cast_two]
    rw [h_le]
    have : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
    have : 2 * Real.log 2 ≤ 1.3862943616 := by linarith
    linarith
  have h4 : θ X ≤ 1.3863 * X := le_trans h2 (mul_le_mul_of_nonneg_right h3 hX_pos)
  linarith

/-- Extend the range of `rep`'s inner sum to `range (b+1)` when `N ≤ b`. -/
private lemma rep_eq_sum_range_filter {b N : ℕ} (hN : N ≤ b) :
    rep N = ∑ p ∈ (range (b + 1)).filter Nat.Prime,
      (if p ≤ N then (if (N - p).Prime then Real.log (p : ℝ) * Real.log ((N - p : ℕ) : ℝ) else 0)
        else 0) := by
  unfold rep
  have hset : ((range (b + 1)).filter Nat.Prime).filter (fun p => p ≤ N)
      = (range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_range]
    constructor
    · intro h
      exact ⟨by omega, h.1.2⟩
    · intro h
      exact ⟨⟨by omega, h.2⟩, by omega⟩
  have hcongr : (∑ p ∈ (range (b + 1)).filter Nat.Prime,
        (if p ≤ N then (if (N - p).Prime then Real.log (p : ℝ) * Real.log ((N - p : ℕ) : ℝ) else 0)
          else 0))
      = ∑ p ∈ (range (N + 1)).filter Nat.Prime,
          (if (N - p).Prime then Real.log (p : ℝ) * Real.log ((N - p : ℕ) : ℝ) else 0) := by
    have step := Finset.sum_filter (s := (range (b + 1)).filter Nat.Prime)
      (p := fun p => p ≤ N)
      (f := fun p : ℕ => if (N - p).Prime then
        Real.log (p : ℝ) * Real.log ((N - p : ℕ) : ℝ) else 0)
    rw [← step, hset]
  exact hcongr.symm

/-- For a prime `p ≤ b`, the contribution of the pairs `p + q = N ∈ ]a, b]` with `a ≤ b`
is `log p` times the mass of the primes in `]a - p, b - p]`. -/
private lemma sum_shift_rep {a b : ℕ} (hab : a ≤ b) {p : ℕ} (hpb : p ≤ b) :
    ∑ N ∈ (Ioc a b).filter (fun N => p ≤ N),
        (if (N - p).Prime then Real.log (p : ℝ) * Real.log ((N - p : ℕ) : ℝ) else 0)
      = Real.log (p : ℝ) * (θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ)) := by
  classical
  have hQsub : (range (a - p + 1)).filter Nat.Prime ⊆ (range (b - p + 1)).filter Nat.Prime := by
    intro q hq
    simp only [mem_filter, mem_range] at hq ⊢
    exact ⟨by omega, hq.2⟩
  have hdiff : θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ)
      = ∑ q ∈ (((range (b - p + 1)).filter Nat.Prime) \ ((range (a - p + 1)).filter Nat.Prime)),
          Real.log (q : ℝ) := by
    have hs := sum_sdiff (s₁ := (range (a - p + 1)).filter Nat.Prime)
      (s₂ := (range (b - p + 1)).filter Nat.Prime)
      (f := fun q : ℕ => Real.log (q : ℝ)) hQsub
    rw [← sum_log_primes_range (b - p), ← sum_log_primes_range (a - p)]
    linarith
  have hL : ∑ N ∈ ((Ioc a b).filter (fun N => p ≤ N)).filter (fun N => (N - p).Prime),
        Real.log (p : ℝ) * Real.log ((N - p : ℕ) : ℝ)
      = ∑ N ∈ (Ioc a b).filter (fun N => p ≤ N),
        (if (N - p).Prime then Real.log (p : ℝ) * Real.log ((N - p : ℕ) : ℝ) else 0) :=
    Finset.sum_filter (s := (Ioc a b).filter (fun N => p ≤ N))
      (p := fun N => (N - p).Prime)
      (f := fun N : ℕ => Real.log (p : ℝ) * Real.log ((N - p : ℕ) : ℝ))
  rw [← hL, hdiff, Finset.mul_sum]
  refine Finset.sum_bij (fun N _ => N - p) ?_ ?_ ?_ ?_
  · intro N hN
    obtain ⟨hN1, hprime⟩ := Finset.mem_filter.mp hN
    obtain ⟨hNIoc, hpN⟩ := Finset.mem_filter.mp hN1
    obtain ⟨haN, hNb⟩ := Finset.mem_Ioc.mp hNIoc
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime⟩
    · intro hmem
      obtain ⟨hr, hpr⟩ := Finset.mem_filter.mp hmem
      have hlt : N - p < a - p + 1 := Finset.mem_range.mp hr
      have h2p : 2 ≤ N - p := hpr.two_le
      omega
  · intro N1 hN1 N2 hN2 heq
    have hp1 : p ≤ N1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hN1).1).2
    have hp2 : p ≤ N2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hN2).1).2
    omega
  · intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqr, hqprime⟩ := Finset.mem_filter.mp hq1
    have hqb : q < b - p + 1 := Finset.mem_range.mp hqr
    have hqa : ¬ (q < a - p + 1) := by
      intro h
      exact hq2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hqprime⟩)
    have hq2' : 2 ≤ q := hqprime.two_le
    refine ⟨q + p, ?_, by omega⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩, ?_⟩
    simpa using hqprime
  · intro N hN
    rfl


/-- Corrected form of the interchange, with the missing hypothesis `a ≤ b`. -/
private theorem sum_rep_Ioc_eq_of_le {a b : ℕ} (hab : a ≤ b) :
    ∑ N ∈ Ioc a b, rep N =
      ∑ p ∈ (range (b + 1)).filter Nat.Prime,
        Real.log (p : ℝ) * (θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ)) := by
  classical
  have hstep : ∑ N ∈ Ioc a b, rep N
      = ∑ N ∈ Ioc a b, ∑ p ∈ (range (b + 1)).filter Nat.Prime,
          (if p ≤ N then (if (N - p).Prime then
            Real.log (p : ℝ) * Real.log ((N - p : ℕ) : ℝ) else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro N hN
    exact rep_eq_sum_range_filter (Finset.mem_Ioc.mp hN).2
  rw [hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : p ≤ b := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    omega
  rw [← Finset.sum_filter]
  exact sum_shift_rep hab hpb

/-- LEAF. **First moment over all of `]X, 2X]`**: `Σ_{⌊X⌋ < N ≤ ⌊2X⌋} rep N ≥ 0.58 X²` for
`X ≥ exp 67`: by `sum_rep_Ioc_ge_head`, `inner_lower`, `sum_log_primes_range` and
`theta_floor_ge`, the sum is `≥ θ(⌊X⌋)(0.5937 X - 0.99) ≥ 0.99 X (0.5937 X - 0.99)`.
Ramaré 1995 Proposition 1, p. 653 and Section 5, in a weak form. Unit U-1526. -/
theorem first_moment (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 67 ≤ X) : 0.58 * X ^ 2 ≤ ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, rep N := by
  have hX0 : 0 < X := lt_of_lt_of_le (exp_pos 67) hX
  have hX129 : (129 : ℝ) ≤ X := le_trans exp67_ge_129 hX
  have hab : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono (by linarith)
  rw [sum_rep_Ioc_eq_of_le hab]
  -- drop the primes above ⌊X⌋
  have hsub : (range (⌊X⌋₊ + 1)).filter Nat.Prime ⊆ (range (⌊2 * X⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hA : ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime,
        Real.log (p : ℝ) * (θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ))
      ≤ ∑ p ∈ (range (⌊2 * X⌋₊ + 1)).filter Nat.Prime,
        Real.log (p : ℝ) * (θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro p _ _
    exact mul_nonneg (Real.log_natCast_nonneg p) (theta_sub_nonneg hab p)
  -- pointwise lower bound
  have hB : ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime,
        Real.log (p : ℝ) * (0.5937 * X - 0.99)
      ≤ ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime,
        Real.log (p : ℝ) * (θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp1 : p ≤ ⌊X⌋₊ := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      omega
    exact mul_le_mul_of_nonneg_left (inner_lower hRS hX hp1) (Real.log_natCast_nonneg p)
  have hC : ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime,
        Real.log (p : ℝ) * (0.5937 * X - 0.99) = (0.5937 * X - 0.99) * θ (⌊X⌋₊ : ℝ) := by
    rw [← Finset.sum_mul, sum_log_primes_range, mul_comm]
  have hθ : 0.99 * X ≤ θ (⌊X⌋₊ : ℝ) :=
    theta_floor_ge hRS (le_trans (Real.exp_le_exp.mpr (by norm_num)) hX)
  have hpos : 0 ≤ 0.5937 * X - 0.99 := by nlinarith
  have hfin : 0.58 * X ^ 2 ≤ (0.5937 * X - 0.99) * θ (⌊X⌋₊ : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hθ hpos]
  linarith [hA, hB, hC]


/-- LEAF. **First moment over the even `N`**: `Σ_{N even in ]X, 2X]} rep N ≥ 0.55 X²` for
`X ≥ exp 67`: remove the odd `N` by `sum_rep_odd_le`, whose total
`2 log 2 · θ(2X) ≤ 4 log 2 log 4 · X` is below `0.03 X²`. Uses `first_moment`.
Unit U-1526. -/
theorem first_moment_even (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 67 ≤ X) : 0.55 * X ^ 2 ≤ ∑ N ∈ evenBlock X, rep N := by
  have hX0 : 0 < X := lt_of_lt_of_le (exp_pos 67) hX
  have hX129 : (129 : ℝ) ≤ X := le_trans exp67_ge_129 hX
  have hfm := first_moment hRS hX
  have hsplit : ∑ N ∈ evenBlock X, rep N
      + ∑ N ∈ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun N => ¬ Even N), rep N
      = ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, rep N := by
    rw [evenBlock]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hodd : ∑ N ∈ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun N => ¬ Even N), rep N ≤ 0.03 * X ^ 2 := by
    refine le_trans (sum_rep_odd_le ⌊X⌋₊ ⌊2 * X⌋₊) ?_
    have hb0 : (0 : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by positivity
    have hθb : θ (⌊2 * X⌋₊ : ℝ) ≤ Real.log 4 * (⌊2 * X⌋₊ : ℝ) :=
      Chebyshev.theta_le_log4_mul_x hb0
    have hb : (⌊2 * X⌋₊ : ℝ) ≤ 2 * X := Nat.floor_le (by positivity)
    have hl2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
    have hl4 : Real.log 4 ≤ 1.3863 := log4_le
    have hθ1 : θ (⌊2 * X⌋₊ : ℝ) ≤ 2.7726 * X := by nlinarith [hθb, hb, hl4]
    have hθ2 : 2 * Real.log 2 * θ (⌊2 * X⌋₊ : ℝ) ≤ 2 * Real.log 2 * (2.7726 * X) :=
      mul_le_mul_of_nonneg_left hθ1 (by positivity)
    have hθ3 : 2 * Real.log 2 * (2.7726 * X) ≤ 3.8437 * X := by
      have hp2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith [hl2, hp2.le]
    have hfen : 3.8437 * X ≤ 0.03 * X ^ 2 := by nlinarith [hX129]
    linarith [hθ2, hθ3, hfen]
  linarith [hfm, hodd, hsplit]


/-- **Effective Theorem 2 from any explicit Selberg constant**, assembly, zero sorry of its own,
CONDITIONAL ON `hRS` and on `hW`, `gcount N ≤ A h(N) N / (log N)²` for even `N ≥ exp 67`:
for `X ≥ exp 67`, at least `0.3025 / (10.6 A²) · X` even `N ∈ ]X, 2X]` are sums of two primes. -/
theorem theorem2_explicit_of_sieve (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x)
    {A : ℝ} (hA : 0 < A)
    (hW : ∀ N : ℕ, Even N → exp 67 ≤ N → (gcount N : ℝ) ≤ A * oddFac N * N / Real.log N ^ 2) :
    ∀ X : ℝ, exp 67 ≤ X →
      0.3025 / (10.6 * A ^ 2) * X ≤
        (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ) := by
  have h := density_of_moments 0.55 (10.6 * A ^ 2) (by norm_num) (by positivity)
    (fun X hX => first_moment_even hRS hX)
    (fun X hX => second_moment_of hA.le hW hX)
  intro X hX
  have := h X hX
  norm_num at this ⊢
  exact this

/-- **Effective Theorem 2**, assembly, zero sorry of its own, CONDITIONAL ON `hRS`, the
Rosser-Schoenfeld lower bound for `θ`: for every `X ≥ exp 67`, at least `X / 10^8` even
integers of `]X, 2X]` are sums of two primes. Uses the Selberg leaf `gcount_le_selberg`
through `second_moment`. Ramaré's Theorem 2 has `X / 5`. -/
theorem theorem2_effective_of_RS (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) :
    ∀ X : ℝ, exp 67 ≤ X →
      X / 10 ^ 8 ≤ (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ) := by
  have h := density_of_moments 0.55 6784000 (by norm_num) (by norm_num)
    (fun X hX => first_moment_even hRS hX) (fun X hX => second_moment hX)
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le (exp_pos 67) hX
  have := h X hX
  have hc : X / 10 ^ 8 ≤ 0.55 ^ 2 / 6784000 * X := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith

/-- **Theorem 2 type bound from a sharp Selberg constant**, assembly, zero sorry of its own,
CONDITIONAL ON `hRS` and on `gcount N ≤ 5.2 h(N) N / (log N)²` for even `N ≥ exp 67`;
`5.2 ≥ 7.8209 · 0.66017`, Wu 2004 Theorem 1, holds only for `N` large, not shown effective
from `exp 67`. Gives `X / 1000`. -/
theorem theorem2_of_sharp_sieve (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x)
    (hW : ∀ N : ℕ, Even N → exp 67 ≤ N →
      (gcount N : ℝ) ≤ 5.2 * oddFac N * N / Real.log N ^ 2) :
    ∀ X : ℝ, exp 67 ≤ X →
      X / 1000 ≤ (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ) := by
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le (exp_pos 67) hX
  have := theorem2_explicit_of_sieve hRS (by norm_num) hW X hX
  have hc : X / 1000 ≤ 0.3025 / (10.6 * 5.2 ^ 2) * X := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith

/-- Vacuity: the range `X ≥ exp 67` of the assemblies is not empty. -/
example : exp 67 ≤ exp 67 := le_rfl

/-- Vacuity for `hRS` at a small point: `θ` is positive from 2 on, Mathlib. -/
example : 0 < θ (2 : ℝ) := Chebyshev.theta_pos le_rfl

end LeanLab.Ramare1995.Decomp1526c
