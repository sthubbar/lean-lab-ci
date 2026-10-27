/-
AI-written Lean code, Claude, 2026-10-25, run 20261025T2003Z-426, unit U-1528, DECOMPOSE.
P0020 P. J. Campbell 2026, A Sharper Explicit Result for the Sum of Two Almost Primes,
arXiv 2608.09488 v1. The explicit prime estimates of Section 4 rest on Rosser-Schoenfeld 1962,
Illinois J. Math. 6, Theorems 5 to 7, p. 70. This file splits the elementary part of that
material, Mertens' first theorem with explicit constants, into leaves, following the
Rosser-Schoenfeld style elementary argument: log n! by Legendre's formula.

Already in Mathlib, not restated: `Chebyshev.theta_le_log4_mul_x` (θ x ≤ x log 4),
`Nat.factorization_factorial_le_div_pred` (v_p(n!) ≤ n/(p - 1)), `log_add_one_le_harmonic`,
`ArithmeticFunction.vonMangoldt_sum`, `Chebyshev.psi_le`.
Already in the lab, not restated: `AlmostPrimes.RSLogSum.sum_log_div_lt_log`
(Σ_{p ≤ n} log p/p < log n for n ≥ 1000), `PNTSieve.Mertens.C_ge`, `C_le` (constant 7),
`PNTSieve.Mertens.sum_log_div_pred_le` (Σ log p/(p(p - 1)) ≤ 6), `log_factorial_ge`.
The lab modules are not imported (none is built in this checkout); the one helper re-proved
here, `log_factorial_ge'`, is proved, not a leaf.

Leaves: 11. Assemblies, proved from the leaves with no sorry of their own:
`mertens1_upper_nat`, `mertens1_lower_nat`, `mertens1_abs` (|Σ_{p ≤ x} log p/p - log x| ≤ 2 for
x ≥ 1), `vonMangoldt_mertens_nat`.
Known mathematics. Goldbach is open.
-/
import Mathlib

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.AlmostPrimes.Decomp1528a

/-! ### Legendre's formula, the two halves -/

/-- LEAF. Legendre upper half: for every natural n,
log n! ≤ n Σ_{p ≤ n} log p / p + n Σ_{p ≤ n} log p / (p (p - 1)).
Proof: log n! = Σ_{p ≤ n} v_p(n!) log p and v_p(n!) ≤ n/(p - 1) = n/p + n/(p(p - 1)).
Rosser-Schoenfeld 1962, Section 3, p. 70 style; Ingham, The Distribution of Prime Numbers,
Thm 7. Unit U-1528. -/
theorem log_factorial_le_sum (n : ℕ) :
    log (n.factorial : ℝ) ≤
      (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p +
        (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  sorry

/-- LEAF. Legendre lower half: for every natural n,
n Σ_{p ≤ n} log p / p - θ(n) ≤ log n!.
Proof: v_p(n!) ≥ ⌊n/p⌋ ≥ n/p - 1, summed against log p. Ingham, Thm 7. Unit U-1528. -/
theorem sum_sub_theta_le_log_factorial (n : ℕ) :
    (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p - θ n ≤ log (n.factorial : ℝ) := by
  sorry

/-! ### The constant Σ_p log p/(p(p - 1)) = 0.75536... -/

/-- LEAF. Head of the prime sum: Σ_{p ≤ 1000} log p / (p (p - 1)) ≤ 0.7545.
Python value 0.754375. Kernel check with rational bounds for log p. Rosser-Schoenfeld 1962,
(2.11) and p. 70, the constant E = -γ - Σ_p log p/(p(p - 1)). Unit U-1528. -/
theorem sum_log_div_pp1_head :
    ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.7545 := by
  sorry

/-- LEAF. Tail over all integers: for every n, Σ_{1000 < m ≤ n} log m / (m (m - 1)) ≤ 0.009.
Python value of the full tail 0.007908; g(1000) = 0.0089078. Proof: log m/(m(m - 1)) ≤ g(m - 1) - g(m) with
g(t) = (log t + 2)/t for t ≥ 1000, telescoping. Rosser-Schoenfeld 1962, p. 70 style. Unit U-1528. -/
theorem sum_log_div_pp1_tail (n : ℕ) :
    ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 0.009 := by
  sorry

/-- LEAF. Prime tail inside the integer tail: for every n,
Σ_{p ≤ n} log p/(p(p - 1)) ≤ Σ_{p ≤ 1000} log p/(p(p - 1)) + Σ_{1000 < m ≤ n} log m/(m(m - 1)),
because every term is nonnegative. Unit U-1528. -/
theorem sum_log_div_pp1_split (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) +
        ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
  sorry

/-- Σ_{p ≤ n} log p / (p (p - 1)) ≤ 0.7635 for every n, from the three leaves above. -/
theorem sum_log_div_pp1_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.7635 := by
  have h1 := sum_log_div_pp1_split n
  have h2 := sum_log_div_pp1_head
  have h3 := sum_log_div_pp1_tail n
  linarith

/-! ### log n! against n log n -/

/-- `n log n - n ≤ log n!`, the same statement as the lab's `PNTSieve.Mertens.log_factorial_ge`,
re-proved here so this file imports only Mathlib. PROVED. -/
theorem log_factorial_ge' (n : ℕ) : (n : ℝ) * log n - n ≤ log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn : (0 : ℝ) < n := by exact_mod_cast h
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hb : (n : ℝ) ^ n / n.factorial ≤ exp n := by
    have := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn.le n
    simpa using this
  have hb' : (n : ℝ) ^ n ≤ exp n * n.factorial := by
    rwa [div_le_iff₀ hf] at hb
  have hl := Real.log_le_log (by positivity) hb'
  rw [Real.log_mul (exp_pos _).ne' hf.ne', Real.log_exp, Real.log_pow] at hl
  linarith

/-- `log n! ≤ n log n`, from `n! ≤ n^n`. PROVED. -/
theorem log_factorial_le (n : ℕ) : log (n.factorial : ℝ) ≤ (n : ℝ) * log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc log (n.factorial : ℝ) ≤ log ((n : ℝ) ^ n) := Real.log_le_log hf h1
    _ = (n : ℝ) * log n := by rw [Real.log_pow]

/-! ### Mertens' first theorem, explicit -/

/-- **Mertens' first theorem, upper half, explicit**: Σ_{p ≤ n} log p/p ≤ log n + log 4 for n ≥ 1.
Assembly from `sum_sub_theta_le_log_factorial`, `log_factorial_le` and Mathlib's
`theta_le_log4_mul_x`. -/
theorem mertens1_upper_nat (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, log p / p ≤ log n + log 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := sum_sub_theta_le_log_factorial n
  have h2 := log_factorial_le n
  have h3 := theta_le_log4_mul_x (x := (n : ℝ)) hn'.le
  have h4 : (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p ≤ (n : ℝ) * (log n + log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left h4 hn'

/-- **Mertens' first theorem, lower half, explicit**: log n - 1.7635 ≤ Σ_{p ≤ n} log p/p for
n ≥ 1. Assembly from `log_factorial_le_sum`, `sum_log_div_pp1_le`, `log_factorial_ge'`. -/
theorem mertens1_lower_nat (n : ℕ) (hn : 1 ≤ n) :
    log n - 1.7635 ≤ ∑ p ∈ Nat.primesLE n, log p / p := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := log_factorial_le_sum n
  have h2 := sum_log_div_pp1_le n
  have h3 := log_factorial_ge' n
  have h4 : (n : ℝ) * (log n - 1.7635) ≤ (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left h4 hn'

/-- LEAF. Small range of the real form: for 1 ≤ x < 5,
|Σ_{p ≤ ⌊x⌋} log p / p - log x| ≤ 2. The sums are 0, log 2/2, log 2/2 + log 3/3 and log x < log 5.
Python: worst value 0.897 near x = 5. Unit U-1528. -/
theorem mertens1_small {x : ℝ} (hx : 1 ≤ x) (hx5 : x < 5) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 2 := by
  sorry

/-- LEAF. Floor step: for x ≥ 5, log x ≤ log ⌊x⌋ + 0.2, since x < ⌊x⌋ + 1 and
log(1 + 1/5) = 0.1823 < 0.2. Unit U-1528. -/
theorem log_le_log_floor_add {x : ℝ} (hx : 5 ≤ x) : log x ≤ log (⌊x⌋₊ : ℝ) + 0.2 := by
  sorry

/-- **Mertens' first theorem, explicit, real form**: for every real x ≥ 1,
|Σ_{p ≤ x} log p / p - log x| ≤ 2. Assembly from the leaves of this file and Mathlib.
Python: the true deviation lies in [-1.3323, 0] up to 2·10^6, Rosser-Schoenfeld (3.21), (3.24). -/
theorem mertens1_abs {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 2 := by
  rcases lt_or_ge x 5 with h5 | h5
  · exact mertens1_small hx h5
  have hn1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hf0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hn1
  have hlog : log (⌊x⌋₊ : ℝ) ≤ log x := Real.log_le_log hf0 hfx
  have hU := mertens1_upper_nat ⌊x⌋₊ hn1
  have hL := mertens1_lower_nat ⌊x⌋₊ hn1
  have hS := log_le_log_floor_add h5
  have h4 : log (4 : ℝ) < 2 := by
    have he := Real.exp_one_gt_d9
    have h2 : exp (2 : ℝ) = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
    rw [Real.log_lt_iff_lt_exp (by norm_num), h2]; nlinarith
  rw [abs_le]; constructor <;> linarith

/-! ### The von Mangoldt form -/

/-- LEAF. Chebyshev's identity: for every natural n,
log n! = Σ_{1 ≤ m ≤ n} Λ(m) ⌊n/m⌋. Proof: log k = Σ_{m ∣ k} Λ(m) (Mathlib `vonMangoldt_sum`)
summed over k ≤ n, then swap. Ingham, Thm 7 proof; Montgomery-Vaughan, Multiplicative Number
Theory I, Section 2.2. Unit U-1528. -/
theorem log_factorial_eq_vonMangoldt (n : ℕ) :
    log (n.factorial : ℝ) =
      ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m * ((n / m : ℕ) : ℝ) := by
  sorry

/-- LEAF. Upper half for Λ: for n ≥ 1, n Σ_{m ≤ n} Λ(m)/m ≤ log n! + ψ(n), from
n/m ≤ ⌊n/m⌋ + 1 and `log_factorial_eq_vonMangoldt`. Montgomery-Vaughan I, Section 2.2.
Unit U-1528. -/
theorem vonMangoldt_sum_le (n : ℕ) :
    (n : ℝ) * ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m ≤
      log (n.factorial : ℝ) + ψ n := by
  sorry

/-- LEAF. Lower half for Λ: for every n, log n! ≤ n Σ_{m ≤ n} Λ(m)/m, from ⌊n/m⌋ ≤ n/m and
`log_factorial_eq_vonMangoldt`. Montgomery-Vaughan I, Section 2.2. Unit U-1528. -/
theorem log_factorial_le_vonMangoldt_sum (n : ℕ) :
    log (n.factorial : ℝ) ≤ (n : ℝ) * ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m := by
  sorry

/-- LEAF. Numeric step: for every real t ≥ 1, log 4 + 2 log t / √t ≤ 3; the maximum of
log t/√t is 2/e at t = e², and log 4 + 4/e = 2.858. Unit U-1528. -/
theorem log4_add_le_three {t : ℝ} (ht : 1 ≤ t) : log 4 + 2 * log t / √t ≤ 3 := by
  sorry

/-- **Mertens' first theorem for Λ, explicit**: for n ≥ 1,
log n - 1 ≤ Σ_{m ≤ n} Λ(m)/m ≤ log n + 3. Python: the true deviation lies in [-0.627, 0] up to
2·10^5. Assembly from the leaves, `log_factorial_ge'`, `log_factorial_le` and Mathlib `psi_le`. -/
theorem vonMangoldt_mertens_nat (n : ℕ) (hn : 1 ≤ n) :
    log n - 1 ≤ ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m ∧
      ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m ≤ log n + 3 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set S := ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m with hSdef
  constructor
  · have h1 := log_factorial_le_vonMangoldt_sum n
    have h2 := log_factorial_ge' n
    have h4 : (n : ℝ) * (log n - 1) ≤ (n : ℝ) * S := by nlinarith
    exact le_of_mul_le_mul_left h4 hn'
  · have h1 := vonMangoldt_sum_le n
    have h2 := log_factorial_le n
    have h3 := psi_le hn1
    have h5 := log4_add_le_three hn1
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
    have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
    have h6 : 2 * √(n : ℝ) * log n = (n : ℝ) * (2 * log n / √(n : ℝ)) := by
      field_simp
      rw [Real.sq_sqrt hn'.le]; ring
    have h4 : (n : ℝ) * S ≤ (n : ℝ) * (log n + 3) := by
      have : (n : ℝ) * (log 4 + 2 * log n / √(n : ℝ)) ≤ (n : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left h5 hn'.le
      nlinarith
    exact le_of_mul_le_mul_left h4 hn'

/-! ### Vacuity instances -/

/-- The hypotheses of `mertens1_abs` hold at x = 7. -/
example : (1 : ℝ) ≤ 7 := by norm_num

/-- The hypotheses of `mertens1_small` hold at x = 2. -/
example : (1 : ℝ) ≤ 2 ∧ (2 : ℝ) < 5 := by norm_num

/-- `log_le_log_floor_add` at x = 5: its hypothesis holds. -/
example : (5 : ℝ) ≤ 5 := le_rfl

end LeanLab.AlmostPrimes.Decomp1528a
