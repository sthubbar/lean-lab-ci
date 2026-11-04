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
import LeanLab.ChebyshevExplicit.Psi30Upper
import LeanLab.Ramare1995.Decomp1526b

open Finset Real
open scoped Classical Chebyshev

noncomputable section
namespace LeanLab.Ramare1995.Decomp1526c
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9
open LeanLab.Ramare1995.Decomp1526a LeanLab.Ramare1995.Decomp1526b

/- LEAF. Interchange: `Σ_{a < N ≤ b} rep N = Σ_{p ≤ b} log p (θ(b - p) - θ(a - p))`, with
natural subtraction; for `p ≥ a` the second term is `θ(0) = 0`. Definition of `rep`;
Ramaré 1995 Section 5, p. 678, the opening of the proof of Proposition 1. Unit U-1526.
RETIRED by U-1614: the form for all `a b` is false at `a = 4, b = 2`,
`Decomp1526b.sum_rep_Ioc_eq_counterexample`. The repaired `sum_rep_Ioc_eq`, with `a ≤ b`, is proved
below after its helpers.
theorem sum_rep_Ioc_eq (a b : ℕ) : stated for all a b, RETIRED, no proof term -/

theorem theta_sub_nonneg {a b : ℕ} (hab : a ≤ b) (p : ℕ) :
    0 ≤ θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ) :=
  sub_nonneg.mpr (Chebyshev.theta_mono (by exact_mod_cast Nat.sub_le_sub_right hab p))

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

/-- Elementary exponential series bound for the error terms at exp 60. -/
theorem million_mul_sq_le_exp {L : ℝ} (hL : 60 ≤ L) :
    1000000 * L ^ 2 ≤ exp L := by
  have h0 : 0 ≤ L := by linarith
  have h6 : (60 : ℝ) ^ 6 ≤ L ^ 6 := by gcongr
  have h8 := Real.pow_div_factorial_le_exp L h0 8
  norm_num at h8
  have hprod := mul_le_mul_of_nonneg_right h6 (sq_nonneg L)
  have heq : L ^ 6 * L ^ 2 = L ^ 8 := by ring
  rw [heq] at hprod
  nlinarith


/-- At exp 60 the square of the logarithm is at most a millionth of x. -/
theorem log_sq_le_millionth {x : ℝ} (hx : exp 60 ≤ x) :
    log x ^ 2 ≤ x / 1000000 := by
  have hx0 : 0 < x := (exp_pos 60).trans_le hx
  have hL : 60 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have h := million_mul_sq_le_exp hL
  rw [Real.exp_log hx0] at h
  linarith


/-- Unconditional elementary theta lower bound in the range of the lab moment. -/
theorem theta_ge_nine_tenths {x : ℝ} (hx : exp 60 ≤ x) :
    0.9 * x ≤ θ x := by
  have he60 : (1000000 : ℝ) ≤ exp 60 := by
    have h := Real.pow_div_factorial_le_exp 60 (by norm_num : (0 : ℝ) ≤ 60) 6
    norm_num at h
    linarith
  have hxlarge : (1000000 : ℝ) ≤ x := he60.trans hx
  have hx0 : 0 < x := by linarith
  have hf : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hfl : x - 1 ≤ (⌊x⌋₊ : ℝ) := by have := Nat.lt_floor_add_one x; linarith
  have hfn : 30 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    norm_num only [Nat.cast_ofNat]
    linarith
  have hpsi := LeanLab.ChebyshevExplicit.psi_ge_09212 ⌊x⌋₊ hfn
  have hlog : log (⌊x⌋₊ : ℝ) ≤ log x := Real.log_le_log (by linarith) hf
  have hgap := Chebyshev.psi_sub_theta_le (x := x) (by linarith)
  rw [← Chebyshev.psi_eq_psi_coe_floor] at hpsi
  have hlog2 := log_sq_le_millionth hx
  have hs0 := sqrt_nonneg x
  have hs2 := sq_sqrt hx0.le
  have hlogsmall : log x ≤ sqrt x / 1000 := by
    by_contra h
    push Not at h
    nlinarith
  have hsx : sqrt x ≤ x := by nlinarith
  have hloglin : log x ≤ x / 1000 := by linarith
  have hgap2 : 2 * sqrt x * log x ≤ x / 500 := by
    have h := mul_le_mul_of_nonneg_left hlogsmall (show 0 ≤ 2 * sqrt x by positivity)
    nlinarith
  nlinarith


/-- A uniform upper bound for theta at natural arguments at most X.
The logarithmic error is evaluated at X so it also covers the small arguments. -/
theorem theta_nat_le_with_log_error {X : ℝ} {n : ℕ}
    (hn : (n : ℝ) ≤ X) :
    θ (n : ℝ) ≤ 1.1062 * n + 2 * log X ^ 2 + 160 := by
  have h := LeanLab.ChebyshevExplicit.theta_le_11062 n
  have hlog : log (n : ℝ) ^ 2 ≤ log X ^ 2 := by
    by_cases hzero : n = 0
    · simp [hzero, sq_nonneg]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
      have hl0 := Real.log_nonneg hn1
      have hl := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ)) hn
      exact pow_le_pow_left₀ hl0 hl 2
  linarith


/-- Unconditional pointwise convolution lower bound from Chebyshev's elementary
constants, in the range used for the weak first moment on p. 678. -/
theorem inner_lower_elementary {X : ℝ} (hX : exp 67 ≤ X) {p : ℕ}
    (hp : p ≤ ⌊X⌋₊) :
    0.69 * X ≤ θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ) := by
  have hX60 : exp 60 ≤ X := (Real.exp_le_exp.mpr (by norm_num)).trans hX
  have hnum := million_mul_sq_le_exp (L := 60) le_rfl
  norm_num at hnum
  have hXlarge : (1000000 : ℝ) ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have haX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
  have hb2X : 2 * X - 1 ≤ (⌊2 * X⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (2 * X)
    linarith
  have hab : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono (by linarith)
  have hpb : p ≤ ⌊2 * X⌋₊ := hp.trans hab
  have hpR : (p : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hp
  have hq : exp 60 ≤ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpb]
    linarith [exp60_add_one_le]
  have h1 := theta_ge_nine_tenths hq
  have hrX : ((⌊X⌋₊ - p : ℕ) : ℝ) ≤ X := by
    rw [Nat.cast_sub hp]
    have : (0 : ℝ) ≤ p := by positivity
    linarith
  have h2 := theta_nat_le_with_log_error hrX
  have hlog := log_sq_le_millionth hX60
  rw [Nat.cast_sub hpb] at h1
  rw [Nat.cast_sub hp] at h2
  have hp0 : (0 : ℝ) ≤ p := by positivity
  rw [Nat.cast_sub hpb, Nat.cast_sub hp]
  nlinarith

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

/-- The modulus one case of the prime pair interchange in equation 5.1 on p. 678.
The first prime is restricted to the lower endpoint. No analytic input is used. -/
theorem sum_rep_head_Ioc_eq {a b : ℕ} (hab : a ≤ b) :
    (∑ N ∈ Ioc a b, ∑ p ∈ (range (a + 1)).filter Nat.Prime,
      if (N - p).Prime then Real.log p * Real.log ((N - p : ℕ) : ℝ) else 0) =
      ∑ p ∈ (range (a + 1)).filter Nat.Prime,
        Real.log p * (θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ)) := by
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have hpa : p ≤ a := by
    have := mem_range.mp (mem_filter.mp hp).1
    omega
  have hfilter : (Ioc a b).filter (fun N => p ≤ N) = Ioc a b := by
    apply filter_eq_self.mpr
    intro N hN
    have := (mem_Ioc.mp hN).1
    omega
  rw [← hfilter]
  exact sum_shift_rep hab (hpa.trans hab)

/-- Prime pair interchange with the divisibility and coprimality filters of
Ramaré 1995 equation 5.1 p. 678. The endpoints are natural numbers.
The normalization by log of the upper endpoint is omitted on both sides. -/
theorem sum_prime_pairs_progression {a b : ℕ} (hab : a ≤ b) (d : ℕ) :
    (∑ N ∈ Ioc a b, ∑ p ∈ (range (a + 1)).filter Nat.Prime,
      if d ∣ N ∧ Nat.Coprime (p * (N - p)) d ∧ (N - p).Prime then
        Real.log p * Real.log ((N - p : ℕ) : ℝ) else 0) =
      ∑ p ∈ (range (a + 1)).filter Nat.Prime,
        Real.log p * ∑ q ∈ (Ioc (a - p) (b - p)).filter
          (fun q => d ∣ p + q ∧ Nat.Coprime (p * q) d ∧ q.Prime), Real.log q := by
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have hpa : p ≤ a := by
    have := mem_range.mp (mem_filter.mp hp).1
    omega
  rw [← sum_filter, mul_sum]
  refine sum_bij (fun N _ => N - p) ?_ ?_ ?_ ?_
  · intro N hN
    obtain ⟨hN, hd, hcop, hprime⟩ := mem_filter.mp hN
    obtain ⟨haN, hNb⟩ := mem_Ioc.mp hN
    have hpN : p ≤ N := by omega
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa only [Nat.add_sub_of_le hpN] using And.intro hd (And.intro hcop hprime)
  · intro N₁ hN₁ N₂ hN₂ heq
    have h₁ := (mem_Ioc.mp (mem_filter.mp hN₁).1).1
    have h₂ := (mem_Ioc.mp (mem_filter.mp hN₂).1).1
    omega
  · intro q hq
    obtain ⟨hq, hd, hcop, hprime⟩ := mem_filter.mp hq
    obtain ⟨haq, hqb⟩ := mem_Ioc.mp hq
    refine ⟨p + q, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩, by omega⟩
    simpa using And.intro hd (And.intro hcop hprime)
  · intro N hN
    rfl


/-- Equation 5.1 on p. 678 with natural endpoints, grouped over reduced residues.
Both sides omit the common normalization by the log of the upper endpoint. -/
theorem sum_prime_pairs_reduced_residues {a b d : ℕ} (hab : a ≤ b) (hd : 0 < d) :
    (∑ N ∈ Ioc a b, ∑ p ∈ (range (a + 1)).filter Nat.Prime,
      if d ∣ N ∧ Nat.Coprime (p * (N - p)) d ∧ (N - p).Prime then
        Real.log p * Real.log ((N - p : ℕ) : ℝ) else 0) =
      ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
        ∑ p ∈ ((range (a + 1)).filter Nat.Prime).filter (fun p => p % d = r),
          Real.log p * ∑ q ∈ (Ioc (a - p) (b - p)).filter
            (fun q => d ∣ r + q ∧ q.Prime), Real.log q := by
  have hcop (p q : ℕ) (hpq : d ∣ p + q) :
      Nat.Coprime (p * q) d ↔ Nat.Coprime p d := by
    rw [Nat.coprime_mul_iff_left]
    refine ⟨And.left, fun hp => ⟨hp, ?_⟩⟩
    apply Nat.coprime_of_dvd
    intro t ht htq htd
    have htp : t ∣ p := (Nat.dvd_add_iff_left htq).mpr (htd.trans hpq)
    exact Nat.not_coprime_of_dvd_of_dvd ht.one_lt htp htd hp
  rw [sum_prime_pairs_progression hab d]
  let S := (range (a + 1)).filter Nat.Prime
  let f := fun p : ℕ => Real.log p * ∑ q ∈ (Ioc (a - p) (b - p)).filter
    (fun q => d ∣ p + q ∧ q.Prime), Real.log q
  have hreduce :
      (∑ p ∈ S, Real.log p * ∑ q ∈ (Ioc (a - p) (b - p)).filter
        (fun q => d ∣ p + q ∧ Nat.Coprime (p * q) d ∧ q.Prime), Real.log q) =
        ∑ p ∈ S.filter (fun p => Nat.Coprime p d), f p := by
    rw [Finset.sum_filter (s := S) (p := fun p => Nat.Coprime p d) (f := f)]
    apply sum_congr rfl
    intro p hp
    by_cases hcp : Nat.Coprime p d
    · rw [ite_eq_left hcp]
      dsimp [f]
      congr 1
      apply congrArg (fun T : Finset ℕ => ∑ q ∈ T, Real.log q)
      ext q
      simp only [mem_filter]
      constructor
      · intro h
        exact ⟨h.1, h.2.1, h.2.2.2⟩
      · intro h
        exact ⟨h.1, h.2.1, (hcop p q h.2.1).mpr hcp, h.2.2⟩
    · rw [ite_eq_right hcp]
      have hzero : ∑ q ∈ (Ioc (a - p) (b - p)).filter
          (fun q => d ∣ p + q ∧ Nat.Coprime (p * q) d ∧ q.Prime), Real.log q = 0 := by
        apply sum_eq_zero
        intro q hq
        have h := (mem_filter.mp hq).2
        exact False.elim (hcp ((hcop p q h.1).mp h.2.1))
      rw [hzero, mul_zero]
  change (∑ p ∈ S, _) = _
  rw [hreduce]
  have hmap : ∀ p ∈ S.filter (fun p => Nat.Coprime p d),
      p % d ∈ (range d).filter (fun r => Nat.Coprime r d) := by
    intro p hp
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt p hd), ?_⟩
    exact (ZMod.coprime_mod_iff_coprime p d).mpr (mem_filter.mp hp).2
  rw [← sum_fiberwise_of_maps_to hmap f]
  apply sum_congr rfl
  intro r hr
  have hrlt : r < d := mem_range.mp (mem_filter.mp hr).1
  have hrcop : Nat.Coprime r d := (mem_filter.mp hr).2
  have hfilter : (S.filter (fun p => Nat.Coprime p d)).filter (fun p => p % d = r) =
      S.filter (fun p => p % d = r) := by
    ext p
    simp only [mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · intro h
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      apply (ZMod.coprime_mod_iff_coprime p d).mp
      rwa [h.2]
  rw [hfilter]
  apply sum_congr rfl
  intro p hp
  have hpr : p % d = r := (mem_filter.mp hp).2
  dsimp [f]
  congr 1
  apply congrArg (fun T : Finset ℕ => ∑ q ∈ T, Real.log q)
  ext q
  simp only [mem_filter]
  have hdiv : d ∣ p + q ↔ d ∣ r + q := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    rw [Nat.add_mod p q d, Nat.add_mod r q d, hpr, Nat.mod_eq_of_lt hrlt]
  rw [hdiv]


/-- Interchange: `Σ_{a < N ≤ b} rep N = Σ_{p ≤ b} log p (θ(b - p) - θ(a - p))`, for `a ≤ b`. Ramaré 1995
Section 5, p. 678. DECISION U-1614: `a ≤ b` added, the old form is false at `a = 4, b = 2`,
`Decomp1526b.sum_rep_Ioc_eq_counterexample`. PROVED. -/
theorem sum_rep_Ioc_eq {a b : ℕ} (hab : a ≤ b) :
    ∑ N ∈ Ioc a b, rep N =
      ∑ p ∈ (range (b + 1)).filter Nat.Prime,
        Real.log (p : ℝ) * (θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ)) :=
  sum_rep_Ioc_eq_of_le hab

/-- LEAF. Drop the primes `a < p ≤ b`, whose terms are `≥ 0` by `theta_sub_nonneg`:
`Σ_{a < N ≤ b} rep N ≥ Σ_{p ≤ a} log p (θ(b - p) - θ(a - p))` for `a ≤ b`. Uses
`sum_rep_Ioc_eq`. Unit U-1526. -/
theorem sum_rep_Ioc_ge_head {a b : ℕ} (hab : a ≤ b) :
    ∑ p ∈ (range (a + 1)).filter Nat.Prime,
        Real.log p * (θ ((b - p : ℕ) : ℝ) - θ ((a - p : ℕ) : ℝ)) ≤ ∑ N ∈ Ioc a b, rep N := by
  rw [sum_rep_Ioc_eq_of_le hab]
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

/-- LEAF. **First moment over all of `]X, 2X]`**: `Σ_{⌊X⌋ < N ≤ ⌊2X⌋} rep N ≥ 0.58 X²` for
`X ≥ exp 67`: by `sum_rep_Ioc_ge_head`, `inner_lower`, `sum_log_primes_range` and
`theta_floor_ge`, the sum is `≥ θ(⌊X⌋)(0.5937 X - 0.99) ≥ 0.99 X (0.5937 X - 0.99)`.
Ramaré 1995 Proposition 1, p. 653 and Section 5, in a weak form. Unit U-1526. -/
theorem first_moment (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 67 ≤ X) : 0.58 * X ^ 2 ≤ ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, rep N := by
  have hX0 : 0 < X := lt_of_lt_of_le (exp_pos 67) hX
  have hX129 : (129 : ℝ) ≤ X := le_trans exp67_ge_129 hX
  have hab : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono (by linarith)
  have hA := sum_rep_Ioc_ge_head hab
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


/-- Unconditional weak all integer first moment from elementary Chebyshev constants.
This is a lab auxiliary estimate for the route on Ramaré 1995 p. 678. -/
theorem first_moment_elementary {X : ℝ} (hX : exp 67 ≤ X) :
    0.58 * X ^ 2 ≤ ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, rep N := by
  have hX0 : 0 < X := (exp_pos 67).trans_le hX
  have hX60 : exp 60 ≤ X := (Real.exp_le_exp.mpr (by norm_num)).trans hX
  have hab : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono (by linarith)
  have htheta : 0.9 * X ≤ θ (⌊X⌋₊ : ℝ) := by
    rw [← Chebyshev.theta_eq_theta_coe_floor]
    exact theta_ge_nine_tenths hX60
  calc
    0.58 * X ^ 2 ≤ (0.69 * X) * (0.9 * X) := by nlinarith [sq_nonneg X]
    _ ≤ (0.69 * X) * θ (⌊X⌋₊ : ℝ) :=
      mul_le_mul_of_nonneg_left htheta (by positivity)
    _ = ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime, Real.log p * (0.69 * X) := by
      rw [← sum_mul, sum_log_primes_range, mul_comm]
    _ ≤ ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime,
        Real.log p * (θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hpa : p ≤ ⌊X⌋₊ := by
        have := mem_range.mp (mem_filter.mp hp).1
        omega
      exact mul_le_mul_of_nonneg_left (inner_lower_elementary hX hpa) (Real.log_natCast_nonneg p)
    _ ≤ ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, rep N := sum_rep_Ioc_ge_head hab


/-- The odd part of the first moment is at most 0.03 X squared at exp 67.
The proof uses only the exceptional prime 2 and Chebyshev's upper bound. -/
theorem odd_moment_le {X : ℝ} (hX : exp 67 ≤ X) :
    ∑ N ∈ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun N => ¬ Even N), rep N ≤ 0.03 * X ^ 2 := by
  have hX0 : 0 < X := (exp_pos 67).trans_le hX
  have hX129 : (129 : ℝ) ≤ X := exp67_ge_129.trans hX
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


/-- Unconditional weak even first moment for the lab's representation function.
This is not the singular series weighted Proposition 1 on p. 653. -/
theorem first_moment_even_elementary {X : ℝ} (hX : exp 67 ≤ X) :
    0.55 * X ^ 2 ≤ ∑ N ∈ evenBlock X, rep N := by
  have hsplit : ∑ N ∈ evenBlock X, rep N
      + ∑ N ∈ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun N => ¬ Even N), rep N
      = ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, rep N := by
    rw [evenBlock]
    exact sum_filter_add_sum_filter_not _ _ _
  linarith [first_moment_elementary hX, odd_moment_le hX]

/-- LEAF. **First moment over the even `N`**: `Σ_{N even in ]X, 2X]} rep N ≥ 0.55 X²` for
`X ≥ exp 67`: remove the odd `N` by `sum_rep_odd_le`, whose total
`2 log 2 · θ(2X) ≤ 4 log 2 log 4 · X` is below `0.03 X²`. Uses `first_moment`.
Unit U-1526. -/
theorem first_moment_even (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 67 ≤ X) : 0.55 * X ^ 2 ≤ ∑ N ∈ evenBlock X, rep N := by
  have hfm := first_moment hRS hX
  have hsplit : ∑ N ∈ evenBlock X, rep N
      + ∑ N ∈ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun N => ¬ Even N), rep N
      = ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, rep N := by
    rw [evenBlock]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hodd := odd_moment_le hX
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

/-- Unconditional weak explicit density bound from the elementary first moment
and the existing Selberg second moment. This gives X divided by 10^8 in the
range of Ramaré 1995 Theorem 2 p. 646, whose stronger bound is X divided by 5. -/
theorem theorem2_effective_elementary :
    ∀ X : ℝ, exp 67 ≤ X →
      X / 10 ^ 8 ≤ (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ) := by
  have h := density_of_moments 0.55 6784000 (by norm_num) (by norm_num)
    (fun X hX => first_moment_even_elementary hX) (fun X hX => second_moment hX)
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le (exp_pos 67) hX
  have := h X hX
  have hc : X / 10 ^ 8 ≤ 0.55 ^ 2 / 6784000 * X := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith


/-- Ramaré 1995 equation 2.8 p. 651. Here p is the paper's second prime.
The other prime is at least sqrt X and the second prime is at most X. -/
def paper_r2 (X : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime,
    if p ≤ N ∧ (N - p).Prime ∧ sqrt X ≤ ((N - p : ℕ) : ℝ) then Real.log p else 0


/-- The dyadic sum of the actual paper representation function can be interchanged.
This uses equation 2.8 p. 651, without an analytic prime distribution input. -/
theorem sum_paper_r2_eq {X : ℝ} (hX : 0 ≤ X) :
    (∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, paper_r2 X N) =
      ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime,
        ∑ q ∈ Ioc (⌊X⌋₊ - p) (⌊2 * X⌋₊ - p),
          if q.Prime ∧ sqrt X ≤ (q : ℝ) then Real.log p else 0 := by
  unfold paper_r2
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have hpa : p ≤ ⌊X⌋₊ := by
    have := mem_range.mp (mem_filter.mp hp).1
    omega
  have hab : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono (by linarith)
  have hpb : p ≤ ⌊2 * X⌋₊ := hpa.trans hab
  have hterm : (∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      if p ≤ N ∧ (N - p).Prime ∧ sqrt X ≤ ((N - p : ℕ) : ℝ) then Real.log p else 0) =
      ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        if (N - p).Prime ∧ sqrt X ≤ ((N - p : ℕ) : ℝ) then Real.log p else 0 := by
    apply sum_congr rfl
    intro N hN
    have hpN : p ≤ N := by have := (mem_Ioc.mp hN).1; omega
    simp only [hpN, true_and]
  rw [hterm]
  have hs : Ioc ⌊X⌋₊ ⌊2 * X⌋₊ =
      Ico (⌊X⌋₊ - p + 1 + p) (⌊2 * X⌋₊ - p + 1 + p) := by
    ext N
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hs]
  rw [sum_Ico_add_right_sub_eq (f := fun q : ℕ =>
    if q.Prime ∧ sqrt X ≤ (q : ℝ) then Real.log p else 0)
    (⌊X⌋₊ - p + 1) (⌊2 * X⌋₊ - p + 1) p]
  have ht : Ico (⌊X⌋₊ - p + 1) (⌊2 * X⌋₊ - p + 1) =
      Ioc (⌊X⌋₊ - p) (⌊2 * X⌋₊ - p) := by
    ext q
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [ht]

/-- The Chebyshev mass in a natural interval is its theta difference.
This is the interval notation used in the prime pair interchange on p. 678. -/
theorem theta_Ioc_eq {a b : ℕ} (hab : a ≤ b) :
    θ (b : ℝ) - θ (a : ℝ) = ∑ q ∈ (Ioc a b).filter Nat.Prime, Real.log q := by
  have h := sum_Ioc_consecutive (fun q : ℕ => if q.Prime then Real.log q else 0)
    (Nat.zero_le a) hab
  simp only [Chebyshev.theta, Nat.floor_natCast, sum_filter]
  linarith


/-- The contribution below sqrt X is bounded by theta of sqrt X.
This isolates the range removed in the paper representation function on p. 651. -/
theorem small_prime_interval_le {X : ℝ} (a b : ℕ) :
    ∑ q ∈ ((Ioc a b).filter Nat.Prime).filter (fun q : ℕ => (q : ℝ) < sqrt X), Real.log q ≤ θ (sqrt X) := by
  rw [Chebyshev.theta_eq_theta_coe_floor (sqrt X), ← sum_log_primes_range]
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨hq, hsmall⟩ := mem_filter.mp hq
    have hprime := (mem_filter.mp hq).2
    exact mem_filter.mpr ⟨mem_range.mpr (by
      have hle : q ≤ ⌊sqrt X⌋₊ := Nat.le_floor hsmall.le
      omega), hprime⟩
  · intro q _ _
    exact Real.log_natCast_nonneg q


/-- A shifted theta interval is controlled by the large prime count plus the
small prime mass. This is an elementary comparison with equation 2.8 p. 651. -/
theorem shifted_theta_le_paper_count {X : ℝ} (hX : exp 67 ≤ X) {p : ℕ}
    :
    θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ) ≤
      Real.log (2 * X) *
        (((Ioc (⌊X⌋₊ - p) (⌊2 * X⌋₊ - p)).filter Nat.Prime).filter
          (fun q : ℕ => sqrt X ≤ (q : ℝ))).card + θ (sqrt X) := by
  have hX0 : 0 < X := (exp_pos 67).trans_le hX
  have hab : ⌊X⌋₊ - p ≤ ⌊2 * X⌋₊ - p :=
    Nat.sub_le_sub_right (Nat.floor_mono (by linarith)) p
  rw [theta_Ioc_eq hab]
  let Q := (Ioc (⌊X⌋₊ - p) (⌊2 * X⌋₊ - p)).filter Nat.Prime
  have hsplit := sum_filter_add_sum_filter_not Q (fun q : ℕ => sqrt X ≤ (q : ℝ))
    (fun q : ℕ => Real.log q)
  have hsmall : ∑ q ∈ Q.filter (fun q : ℕ => ¬ sqrt X ≤ (q : ℝ)), Real.log q ≤ θ (sqrt X) := by
    simpa only [not_le] using small_prime_interval_le (X := X) (⌊X⌋₊ - p) (⌊2 * X⌋₊ - p)
  have hlarge : ∑ q ∈ Q.filter (fun q : ℕ => sqrt X ≤ (q : ℝ)), Real.log q ≤
      Real.log (2 * X) * (Q.filter (fun q : ℕ => sqrt X ≤ (q : ℝ))).card := by
    calc
      _ ≤ ∑ q ∈ Q.filter (fun q : ℕ => sqrt X ≤ (q : ℝ)), Real.log (2 * X) := by
        apply sum_le_sum
        intro q hq
        have hqm := mem_filter.mp (mem_filter.mp hq).1
        have hqprime := hqm.2
        have hqb := (mem_Ioc.mp hqm.1).2
        have hqR : (q : ℝ) ≤ 2 * X := by
          have hle : q ≤ ⌊2 * X⌋₊ := hqb.trans (Nat.sub_le _ _)
          have hcast : (q : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hle
          exact hcast.trans (Nat.floor_le (by positivity))
        exact Real.log_le_log (by exact_mod_cast hqprime.pos) hqR
      _ = _ := by simp [mul_comm]
  change (∑ q ∈ Q, Real.log q) ≤ _
  linarith


/-- A weak first moment for the actual representation function of equation 2.8.
It is unweighted by the inverse singular series and does not assert Proposition 1. -/
theorem paper_r2_first_moment {X : ℝ} (hX : exp 67 ≤ X) :
    0.55 * X ^ 2 / Real.log (2 * X) ≤
      ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, paper_r2 X N := by
  have hX0 : 0 < X := (exp_pos 67).trans_le hX
  have hX60 : exp 60 ≤ X := (Real.exp_le_exp.mpr (by norm_num)).trans hX
  have hnum := million_mul_sq_le_exp (L := 60) le_rfl
  norm_num at hnum
  have hXlarge : (1000000 : ℝ) ≤ X := by linarith
  have hlogpos : 0 < Real.log (2 * X) := Real.log_pos (by linarith)
  have hab : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono (by linarith)
  let P := (range (⌊X⌋₊ + 1)).filter Nat.Prime
  let C := fun p : ℕ =>
    (((Ioc (⌊X⌋₊ - p) (⌊2 * X⌋₊ - p)).filter Nat.Prime).filter
      (fun q : ℕ => sqrt X ≤ (q : ℝ))).card
  have hmass : (∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, paper_r2 X N) =
      ∑ p ∈ P, Real.log p * (C p : ℝ) := by
    rw [sum_paper_r2_eq hX0.le]
    apply sum_congr rfl
    intro p hp
    dsimp [C]
    rw [← Finset.sum_filter]
    simp only [filter_filter, sum_const, nsmul_eq_mul]
    ring
  have hhead : 0.58 * X ^ 2 ≤ ∑ p ∈ P, Real.log p *
      (θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ)) := by
    have htheta : 0.9 * X ≤ θ (⌊X⌋₊ : ℝ) := by
      rw [← Chebyshev.theta_eq_theta_coe_floor]
      exact theta_ge_nine_tenths hX60
    calc
      0.58 * X ^ 2 ≤ (0.69 * X) * (0.9 * X) := by nlinarith [sq_nonneg X]
      _ ≤ (0.69 * X) * θ (⌊X⌋₊ : ℝ) :=
        mul_le_mul_of_nonneg_left htheta (by positivity)
      _ = ∑ p ∈ P, Real.log p * (0.69 * X) := by
        dsimp [P]
        rw [← sum_mul, sum_log_primes_range, mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro p hp
        have hpa : p ≤ ⌊X⌋₊ := by
          have := mem_range.mp (mem_filter.mp hp).1
          omega
        exact mul_le_mul_of_nonneg_left (inner_lower_elementary hX hpa) (Real.log_natCast_nonneg p)
  have hupper : (∑ p ∈ P, Real.log p *
      (θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ))) ≤
      Real.log (2 * X) * (∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, paper_r2 X N) +
        θ (sqrt X) * θ (⌊X⌋₊ : ℝ) := by
    calc
      _ ≤ ∑ p ∈ P, Real.log p * (Real.log (2 * X) * (C p : ℝ) + θ (sqrt X)) := by
        apply sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left (shifted_theta_le_paper_count (p := p) hX)
          (Real.log_natCast_nonneg p)
      _ = _ := by
        rw [hmass, ← sum_log_primes_range ⌊X⌋₊]
        dsimp [P]
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro p hp
        ring
  have htail : θ (sqrt X) * θ (⌊X⌋₊ : ℝ) ≤ 0.03 * X ^ 2 := by
    have hs0 := sqrt_nonneg X
    have hs2 := sq_sqrt hX0.le
    have hslarge : 1000 ≤ sqrt X := by
      apply (Real.le_sqrt (by norm_num) hX0.le).mpr
      norm_num
      exact hXlarge
    have hssmall : sqrt X ≤ X / 1000 := by nlinarith
    have hthetaS : θ (sqrt X) ≤ 1.3863 * sqrt X :=
      (Chebyshev.theta_le_log4_mul_x hs0).trans (mul_le_mul_of_nonneg_right log4_le hs0)
    have hthetaX : θ (⌊X⌋₊ : ℝ) ≤ 1.3863 * X := by
      have htheta := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ (⌊X⌋₊ : ℝ) by positivity)
      have hf := Nat.floor_le hX0.le
      have := mul_le_mul_of_nonneg_right log4_le (show (0 : ℝ) ≤ (⌊X⌋₊ : ℝ) by positivity)
      nlinarith
    have hprod := mul_le_mul hthetaS hthetaX (Chebyshev.theta_nonneg _) (by positivity)
    have hsmallprod := mul_le_mul_of_nonneg_right hssmall hX0.le
    nlinarith
  apply (div_le_iff₀ hlogpos).mpr
  nlinarith

/-- Ramaré 1995 equation 5.1 p. 678, with its log of 2X normalization.
The residue condition is divisibility of the residue plus the second prime. -/
theorem equation51 {X : ℝ} (hX : exp 67 ≤ X) {d : ℕ} (hd : 0 < d) :
    (∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime,
      if d ∣ N ∧ Nat.Coprime (p * (N - p)) d ∧ (N - p).Prime then
        Real.log p * (Real.log ((N - p : ℕ) : ℝ) / Real.log (2 * X)) else 0) =
      ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
        ∑ p ∈ ((range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p => p % d = r),
          Real.log p * ∑ q ∈ (Ioc (⌊X⌋₊ - p) (⌊2 * X⌋₊ - p)).filter
            (fun q => d ∣ r + q ∧ q.Prime), Real.log q / Real.log (2 * X) := by
  have hX0 : 0 < X := (exp_pos 67).trans_le hX
  have hab : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono (by linarith)
  have h := congrArg (fun t : ℝ => t / Real.log (2 * X))
    (sum_prime_pairs_reduced_residues hab hd)
  simpa only [sum_div, ite_div, zero_div, mul_div_assoc] using h


/-- The actual paper representation count in equation 2.8 is nonnegative. -/
theorem paper_r2_nonneg (X : ℝ) (N : ℕ) : 0 ≤ paper_r2 X N := by
  unfold paper_r2
  apply sum_nonneg
  intro p hp
  split_ifs
  · exact Real.log_natCast_nonneg p
  · exact le_rfl


/-- Each term of equation 2.8 p. 651 is at most log X times a Goldbach pair. -/
theorem paper_r2_le_log_mul_gcount {X : ℝ} (hX : 1 ≤ X) (N : ℕ) :
    paper_r2 X N ≤ Real.log X * (gcount N : ℝ) := by
  let P := (range (⌊X⌋₊ + 1)).filter Nat.Prime
  let T := P.filter (fun p => p ≤ N ∧ (N - p).Prime ∧ sqrt X ≤ ((N - p : ℕ) : ℝ))
  have heq : paper_r2 X N = ∑ p ∈ T, Real.log p := by
    unfold paper_r2
    exact (sum_filter (s := P) (p := fun p =>
      p ≤ N ∧ (N - p).Prime ∧ sqrt X ≤ ((N - p : ℕ) : ℝ))
      (f := fun p : ℕ => Real.log p)).symm
  have hsub : T ⊆ (range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime) := by
    intro p hp
    obtain ⟨hpP, hpN, hq, _⟩ := mem_filter.mp hp
    have hpprime := (mem_filter.mp hpP).2
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hpprime, hq⟩
  have hcard : (T.card : ℝ) ≤ (gcount N : ℝ) := by
    exact_mod_cast card_le_card hsub
  rw [heq]
  calc
    _ ≤ ∑ p ∈ T, Real.log X := by
      apply sum_le_sum
      intro p hp
      have hpP := (mem_filter.mp hp).1
      have hpprime := (mem_filter.mp hpP).2
      have hpR : (p : ℝ) ≤ X := by
        have hpa : p ≤ ⌊X⌋₊ := by
          have := mem_range.mp (mem_filter.mp hpP).1
          omega
        exact (by exact_mod_cast hpa : (p : ℝ) ≤ (⌊X⌋₊ : ℝ)).trans
          (Nat.floor_le (by linarith))
      exact Real.log_le_log (by exact_mod_cast hpprime.pos) hpR
    _ = (T.card : ℝ) * Real.log X := by simp
    _ ≤ (gcount N : ℝ) * Real.log X :=
      mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hX)
    _ = _ := by ring


/-- A weak individual bound for the paper r2 on an even dyadic block.
It uses the already proved Selberg bound in file b, with no cited input. -/
theorem paper_r2_selberg {X : ℝ} (hX : exp 67 ≤ X) {N : ℕ}
    (hN : N ∈ evenBlock X) :
    paper_r2 X N ≤ 1600 * oddFac N * X / Real.log X := by
  have hX0 : 0 < X := (exp_pos 67).trans_le hX
  have hX129 : (129 : ℝ) ≤ X := exp67_ge_129.trans hX
  obtain ⟨hNI, hEven⟩ := mem_filter.mp hN
  obtain ⟨hNa, hNb⟩ := mem_Ioc.mp hNI
  have hNX : X < (N : ℝ) := Nat.lt_of_floor_lt hNa
  have hN2 : (N : ℝ) ≤ 2 * X :=
    (by exact_mod_cast hNb : (N : ℝ) ≤ (⌊2 * X⌋₊ : ℝ)).trans (Nat.floor_le (by positivity))
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogNX : Real.log X ≤ Real.log N := Real.log_le_log hX0 hNX.le
  have hodd := oddFac_one_le N
  have hratio : (N : ℝ) / Real.log N ^ 2 ≤ (2 * X) / Real.log X ^ 2 := by
    gcongr
  have hg := gcount_le_selberg hEven (hX.trans hNX.le)
  calc
    paper_r2 X N ≤ Real.log X * (gcount N : ℝ) := paper_r2_le_log_mul_gcount (by linarith) N
    _ ≤ Real.log X * (800 * oddFac N * N / Real.log N ^ 2) :=
      mul_le_mul_of_nonneg_left hg hlogX.le
    _ = (800 * oddFac N * Real.log X) * ((N : ℝ) / Real.log N ^ 2) := by ring
    _ ≤ (800 * oddFac N * Real.log X) * ((2 * X) / Real.log X ^ 2) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by field_simp; ring

/-- The lower cutoff sqrt X in equation 2.8 lets the auxiliary log weighted
representation count control the actual paper count. -/
theorem paper_r2_mul_log_le_rep {X : ℝ} (hX : 1 ≤ X) (N : ℕ) :
    (Real.log X / 2) * paper_r2 X N ≤ rep N := by
  have hX0 : 0 < X := by linarith
  let P := (range (⌊X⌋₊ + 1)).filter Nat.Prime
  let T := P.filter (fun p => p ≤ N ∧ (N - p).Prime ∧ sqrt X ≤ ((N - p : ℕ) : ℝ))
  have heq : paper_r2 X N = ∑ p ∈ T, Real.log p := by
    unfold paper_r2
    exact (sum_filter (s := P) (p := fun p =>
      p ≤ N ∧ (N - p).Prime ∧ sqrt X ≤ ((N - p : ℕ) : ℝ))
      (f := fun p : ℕ => Real.log p)).symm
  rw [heq, mul_sum]
  calc
    _ ≤ ∑ p ∈ T, (if (N - p).Prime then Real.log p * Real.log ((N - p : ℕ) : ℝ) else 0) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpP, hpN, hq, hlarge⟩ := mem_filter.mp hp
      rw [ite_eq_left hq]
      have hlog : Real.log X / 2 ≤ Real.log ((N - p : ℕ) : ℝ) := by
        rw [← Real.log_sqrt hX0.le]
        exact Real.log_le_log (Real.sqrt_pos.mpr hX0) hlarge
      nlinarith [mul_le_mul_of_nonneg_right hlog (Real.log_natCast_nonneg p)]
    _ ≤ rep N := by
      unfold rep
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpP, hpN, _, _⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), (mem_filter.mp hpP).2⟩
      · intro p hp hpT
        split_ifs
        · exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
        · exact le_rfl


/-- A weak even first moment for the actual paper representation function.
This retains the cutoff in equation 2.8 but omits the inverse singular series. -/
theorem paper_r2_even_first_moment {X : ℝ} (hX : exp 67 ≤ X) :
    0.2 * X ^ 2 / Real.log X ≤ ∑ N ∈ evenBlock X, paper_r2 X N := by
  have hX0 : 0 < X := (exp_pos 67).trans_le hX
  have hX129 : (129 : ℝ) ≤ X := exp67_ge_129.trans hX
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog2X : 0 < Real.log (2 * X) := Real.log_pos (by linarith)
  have hlogratio : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ X)
    linarith
  have hA := (div_le_iff₀ hlog2X).mp (paper_r2_first_moment hX)
  have hAnonneg : 0 ≤ ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, paper_r2 X N :=
    sum_nonneg (fun N _ => paper_r2_nonneg X N)
  have hAlog := mul_le_mul_of_nonneg_left hlogratio hAnonneg
  have hodd : (Real.log X / 2) *
      (∑ N ∈ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun N => ¬ Even N), paper_r2 X N) ≤ 0.03 * X ^ 2 := by
    calc
      _ = ∑ N ∈ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun N => ¬ Even N),
          (Real.log X / 2) * paper_r2 X N := by rw [mul_sum]
      _ ≤ ∑ N ∈ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun N => ¬ Even N), rep N :=
        sum_le_sum (fun N _ => paper_r2_mul_log_le_rep (by linarith) N)
      _ ≤ _ := odd_moment_le hX
  have hsplit : (∑ N ∈ evenBlock X, paper_r2 X N) +
      (∑ N ∈ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun N => ¬ Even N), paper_r2 X N) =
      ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, paper_r2 X N := by
    unfold evenBlock
    exact sum_filter_add_sum_filter_not _ _ _
  apply (div_le_iff₀ hlogX).mpr
  nlinarith [sq_nonneg X]

/-- Weak first moment with the inverse local factor of equation 2.7 p. 650.
Cauchy Schwarz and the elementary moments suffice for this small coefficient. -/
theorem paper_r2_local_weight_first_moment_strong {X : ℝ} (hX : exp 67 ≤ X) :
    0.000002 * X ^ 2 / Real.log X ≤
      ∑ N ∈ evenBlock X, paper_r2 X N / oddFac N := by
  have hX0 : 0 < X := (exp_pos 67).trans_le hX
  have hX129 : (129 : ℝ) ≤ X := exp67_ge_129.trans hX
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  let T := X ^ 2 / Real.log X
  let W := ∑ N ∈ evenBlock X, paper_r2 X N / oddFac N
  have hT : 0 < T := by dsimp [T]; positivity
  have hW : 0 ≤ W := by
    apply sum_nonneg
    intro N hN
    exact div_nonneg (paper_r2_nonneg X N) (by linarith [oddFac_one_le N])
  have hG : (∑ N ∈ evenBlock X, paper_r2 X N * oddFac N) ≤ 4240 * T := by
    calc
      _ ≤ ∑ N ∈ evenBlock X, (1600 * oddFac N * X / Real.log X) * oddFac N := by
        apply sum_le_sum
        intro N hN
        exact mul_le_mul_of_nonneg_right (paper_r2_selberg hX hN)
          (by linarith [oddFac_one_le N])
      _ = (1600 * X / Real.log X) * ∑ N ∈ evenBlock X, oddFac N ^ 2 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro N hN
        ring
      _ ≤ (1600 * X / Real.log X) * (2.65 * X) :=
        mul_le_mul_of_nonneg_left (sum_evenBlock_oddFac_sq_le hX0.le) (by positivity)
      _ = _ := by dsimp [T]; ring
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (evenBlock X)
    (r := fun N => paper_r2 X N)
    (f := fun N => paper_r2 X N / oddFac N)
    (g := fun N => paper_r2 X N * oddFac N)
    (fun N _ => div_nonneg (paper_r2_nonneg X N) (by linarith [oddFac_one_le N]))
    (fun N _ => mul_nonneg (paper_r2_nonneg X N) (by linarith [oddFac_one_le N]))
    (fun N _ => by
      have hh : oddFac N ≠ 0 := by linarith [oddFac_one_le N]
      apply le_of_eq
      field_simp)
  have hcs' : (∑ N ∈ evenBlock X, paper_r2 X N) ^ 2 ≤ W * (4240 * T) :=
    hcs.trans (mul_le_mul_of_nonneg_left hG hW)
  have hE : 0.2 * T ≤ ∑ N ∈ evenBlock X, paper_r2 X N := by
    dsimp [T]
    convert paper_r2_even_first_moment hX using 1; ring
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 0.2 * T) hE 2
  have hmain : 0.04 * T ^ 2 ≤ (4240 * W) * T := by nlinarith
  have hquot : 0.04 * T ≤ 4240 * W :=
    (mul_le_mul_iff_right₀ hT).mp (by nlinarith [hmain])
  change 0.000002 * X ^ 2 / Real.log X ≤ W
  calc
    _ = 0.000002 * T := by dsimp [T]; ring
    _ ≤ W := by nlinarith



/-- Weak first moment with the inverse local factor of equation 2.7 p. 650.
Cauchy Schwarz and the elementary moments suffice for this small coefficient. -/
theorem paper_r2_local_weight_first_moment {X : ℝ} (hX : exp 67 ≤ X) :
    0.000001 * X ^ 2 / Real.log X ≤
      ∑ N ∈ evenBlock X, paper_r2 X N / oddFac N := by
  have hX0 : 0 < X := (exp_pos 67).trans_le hX
  have hX129 : (129 : ℝ) ≤ X := exp67_ge_129.trans hX
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  let T := X ^ 2 / Real.log X
  let W := ∑ N ∈ evenBlock X, paper_r2 X N / oddFac N
  have hT : 0 < T := by dsimp [T]; positivity
  have hW : 0 ≤ W := by
    apply sum_nonneg
    intro N hN
    exact div_nonneg (paper_r2_nonneg X N) (by linarith [oddFac_one_le N])
  have hG : (∑ N ∈ evenBlock X, paper_r2 X N * oddFac N) ≤ 4240 * T := by
    calc
      _ ≤ ∑ N ∈ evenBlock X, (1600 * oddFac N * X / Real.log X) * oddFac N := by
        apply sum_le_sum
        intro N hN
        exact mul_le_mul_of_nonneg_right (paper_r2_selberg hX hN)
          (by linarith [oddFac_one_le N])
      _ = (1600 * X / Real.log X) * ∑ N ∈ evenBlock X, oddFac N ^ 2 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro N hN
        ring
      _ ≤ (1600 * X / Real.log X) * (2.65 * X) :=
        mul_le_mul_of_nonneg_left (sum_evenBlock_oddFac_sq_le hX0.le) (by positivity)
      _ = _ := by dsimp [T]; ring
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (evenBlock X)
    (r := fun N => paper_r2 X N)
    (f := fun N => paper_r2 X N / oddFac N)
    (g := fun N => paper_r2 X N * oddFac N)
    (fun N _ => div_nonneg (paper_r2_nonneg X N) (by linarith [oddFac_one_le N]))
    (fun N _ => mul_nonneg (paper_r2_nonneg X N) (by linarith [oddFac_one_le N]))
    (fun N _ => by
      have hh : oddFac N ≠ 0 := by linarith [oddFac_one_le N]
      apply le_of_eq
      field_simp)
  have hcs' : (∑ N ∈ evenBlock X, paper_r2 X N) ^ 2 ≤ W * (4240 * T) :=
    hcs.trans (mul_le_mul_of_nonneg_left hG hW)
  have hE : 0.2 * T ≤ ∑ N ∈ evenBlock X, paper_r2 X N := by
    dsimp [T]
    convert paper_r2_even_first_moment hX using 1; ring
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 0.2 * T) hE 2
  have hmain : 0.04 * T ^ 2 ≤ (4240 * W) * T := by nlinarith
  have hquot : 0.04 * T ≤ 4240 * W :=
    (mul_le_mul_iff_right₀ hT).mp (by nlinarith [hmain])
  change 0.000001 * X ^ 2 / Real.log X ≤ W
  calc
    _ = 0.000001 * T := by dsimp [T]; ring
    _ ≤ W := by nlinarith


/-- The literal interval sum in Ramaré 1995 equation 2.14 p. 652.
The singular series is twice the twin prime constant times the odd local factor.
The normalization S2 is given on p. 647 and used on p. 678. -/
def paper_R (X : ℝ) : ℝ :=
  ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, paper_r2 X N / (2 * LeanLab.ChenExplicit.twinC * oddFac N)


/-- A weak auxiliary version of Proposition 1 p. 653, with coefficient 0.000001
in place of 0.478. No cited input is used. -/
theorem paper_R_weak {X : ℝ} (hX : exp 67 ≤ X) :
    0.000001 * X ^ 2 / Real.log X ≤ paper_R X := by
  have hCpos := LeanLab.ChenExplicit.twinC_pos
  have hC1 : LeanLab.ChenExplicit.twinC ≤ 1 := by
    unfold LeanLab.ChenExplicit.twinC
    apply LeanLab.ChenExplicit.twinC_multipliable.tprod_le_of_prod_le
    intro s
    apply Finset.prod_le_one₀
    · intro p hp
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (show 3 ≤ (p : ℕ) from p.2.2)
      have hden : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
      have hdiv : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
        rw [div_le_one hden]
        nlinarith
      linarith
    · intro p hp
      exact sub_le_self _ (by positivity)
  have hlocal := paper_r2_local_weight_first_moment_strong hX
  have hcompare : (∑ N ∈ evenBlock X, paper_r2 X N / oddFac N) ≤ 2 * paper_R X := by
    calc
      _ ≤ ∑ N ∈ evenBlock X,
          2 * (paper_r2 X N / (2 * LeanLab.ChenExplicit.twinC * oddFac N)) := by
        apply sum_le_sum
        intro N hN
        have hh : 0 < oddFac N := by linarith [oddFac_one_le N]
        have hr := paper_r2_nonneg X N
        have hden : 0 < 2 * LeanLab.ChenExplicit.twinC * oddFac N := by positivity
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hden).mpr
        have hmul := mul_le_mul_of_nonneg_left hC1 (mul_nonneg hr hh.le)
        field_simp [hh.ne']
        nlinarith
      _ = 2 * ∑ N ∈ evenBlock X,
          paper_r2 X N / (2 * LeanLab.ChenExplicit.twinC * oddFac N) := by rw [mul_sum]
      _ ≤ 2 * paper_R X := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        unfold paper_R evenBlock
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro N hN hNE
        exact div_nonneg (paper_r2_nonneg X N)
          (mul_nonneg (mul_nonneg (by norm_num) hCpos.le)
            (by linarith [oddFac_one_le N]))
  have heq : 0.000002 * X ^ 2 / Real.log X =
      2 * (0.000001 * X ^ 2 / Real.log X) := by ring
  rw [heq] at hlocal
  linarith

/-- CITED. Ramaré 1995 Proposition 1 p. 653, in the literal interval notation
of equation 2.14 p. 652 and with S2 equal to twice the Euler product,
as on p. 647 and p. 678.
This definition asserts no proof. Claude statement review is required before merge. -/
def proposition1 : Prop :=
  ∀ X : ℝ, exp 67 ≤ X → 0.478 * X ^ 2 / Real.log X ≤ paper_R X


/-- The scalar closing budget of Section 5, pp. 678 to 679.
Applications to the paper still require the four analytic range estimates. -/
theorem proposition1_numeric_budget {T R M L U V : ℝ} (hT : 0 ≤ T)
    (hM : 0.4921 * T ≤ M) (hL : L ≤ 0.01288 * T)
    (hU : U ≤ 0.0002691 * T) (hV : V ≤ 0.000505 * T)
    (hR : M - L - U - V ≤ R) : 0.478 * T ≤ R := by
  linarith


/-- The elementary coefficient proved here does not imply the paper coefficient.
This is a scalar countermodel to that inference, not a counterexample to the paper. -/
theorem weak_coefficient_insufficient :
    ∃ c : ℝ, 0.000001 ≤ c ∧ ¬ 0.478 ≤ c := by
  exact ⟨0.000001, by norm_num, by norm_num⟩

/-- Vacuity: the range `X ≥ exp 67` of the assemblies is not empty. -/
example : exp 67 ≤ exp 67 := le_rfl

/-- Vacuity for `hRS` at a small point: `θ` is positive from 2 on, Mathlib. -/
example : 0 < θ (2 : ℝ) := Chebyshev.theta_pos le_rfl

end LeanLab.Ramare1995.Decomp1526c
