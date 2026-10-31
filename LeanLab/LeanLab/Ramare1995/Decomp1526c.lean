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

/-- LEAF. Pointwise lower bound for `p ≤ ⌊X⌋`, `X ≥ exp 67`:
`θ(⌊2X⌋ - p) - θ(⌊X⌋ - p) ≥ 0.5937 X - 0.99`, from `θ(⌊2X⌋ - p) ≥ 0.99 (⌊2X⌋ - p)`
(here `⌊2X⌋ - p ≥ X - 1 ≥ exp 60`), `θ(y) ≤ log 4 · y < 1.3863 y`, Mathlib
`Chebyshev.theta_le_log4_mul_x`, and `0.99 ⌊2X⌋ - 1.3863 ⌊X⌋ ≥ 0.5937 X - 0.99`.
Rosser-Schoenfeld 1962 (3.16). Unit U-1526. -/
theorem inner_lower (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 67 ≤ X) {p : ℕ} (hp : p ≤ ⌊X⌋₊) :
    0.5937 * X - 0.99 ≤
      θ ((⌊2 * X⌋₊ - p : ℕ) : ℝ) - θ ((⌊X⌋₊ - p : ℕ) : ℝ) := by
  sorry

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

/-- LEAF. **First moment over all of `]X, 2X]`**: `Σ_{⌊X⌋ < N ≤ ⌊2X⌋} rep N ≥ 0.58 X²` for
`X ≥ exp 67`: by `sum_rep_Ioc_ge_head`, `inner_lower`, `sum_log_primes_range` and
`theta_floor_ge`, the sum is `≥ θ(⌊X⌋)(0.5937 X - 0.99) ≥ 0.99 X (0.5937 X - 0.99)`.
Ramaré 1995 Proposition 1, p. 653 and Section 5, in a weak form. Unit U-1526. -/
theorem first_moment (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 67 ≤ X) : 0.58 * X ^ 2 ≤ ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, rep N := by
  sorry

/-- LEAF. **First moment over the even `N`**: `Σ_{N even in ]X, 2X]} rep N ≥ 0.55 X²` for
`X ≥ exp 67`: remove the odd `N` by `sum_rep_odd_le`, whose total
`2 log 2 · θ(2X) ≤ 4 log 2 log 4 · X` is below `0.03 X²`. Uses `first_moment`.
Unit U-1526. -/
theorem first_moment_even (hRS : ∀ x : ℝ, exp 60 ≤ x → 0.99 * x ≤ θ x) {X : ℝ}
    (hX : exp 67 ≤ X) : 0.55 * X ^ 2 ≤ ∑ N ∈ evenBlock X, rep N := by
  sorry

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
