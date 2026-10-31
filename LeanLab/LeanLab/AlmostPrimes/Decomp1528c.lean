/-
AI-written Lean code, Claude, 2026-10-25, run 20261025T2003Z-426, unit U-1528, DECOMPOSE.
P0020 P. J. Campbell 2026, arXiv 2608.09488 v1. Chebyshev-type lower bounds for θ and π with
stated constants, by the binomial coefficient method, and a finite-range piece of the π bound
the lab's Case 2 row 209 uses, Dusart 2010, π(x) ≤ x/(log x - 1.1) for x ≥ 60184, carried in
the lab as the cited `CampbellTailU6836.DusartPi11Body` and `Thm5.DusartPi11` (not restated).

Already in Mathlib, not restated: `Chebyshev.theta_le_log4_mul_x` (θ(x) ≤ 2x log 2),
`Chebyshev.theta_ge`, `theta_ge'` (θ n ≥ n log 2 - log(n+1) - 2√n log n),
`Chebyshev.theta_le_pi_mul_log'`, `pi_le_log4_mul_div`, `pi_ge`.
Already in the lab, not restated: `ChebyshevExplicit.Psi30.psi_ge_09212`
(ψ n ≥ 0.9212 n - 5 log n, n ≥ 30), `ChebyshevExplicit.Psi30Upper.theta_le_11062`,
`Common.PsiTheta.Bound.psi_sub_theta_le_explicit`, `ChebyshevExplicit.PiUpperLarge`.

Leaves: 7. Assemblies: `theta_ge_half` (θ(x) ≥ x/2 for x ≥ 11) and `pi_ge_half`
(π(x) ≥ x/(2 log x) for x ≥ 11), from the leaves and Mathlib only.
Known mathematics. Goldbach is open.
-/
import Mathlib
import LeanLab.Common.PsiTheta.Discharge1315

-- AI wrote these proof bodies. OpenAI Codex task175, 2026-10-29.

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.AlmostPrimes.Decomp1528c

/-! ### θ(x) ≥ x/2 for x ≥ 11 -/

/-- A natural power certificate gives the half theta bound on a closed integer interval.
Elementary logarithm bridge for the finite leaves below. -/
theorem theta_ge_half_of_primorial (n m N : ℕ)
    (h : 2 ^ (3 * (N + 1)) ≤ primorial m ^ 4) (hm : m ≤ n) (hN : n ≤ N) :
    ((n : ℝ) + 1) / 2 ≤ θ n := by
  have hbase : ((N : ℝ) + 1) / 2 ≤ θ m := by
    have hP : 0 < (primorial m : ℝ) := by exact_mod_cast primorial_pos m
    have hR : (2 : ℝ) ^ (3 * (N + 1)) ≤ (primorial m : ℝ) ^ 4 := by exact_mod_cast h
    have hl := Real.log_le_log (by positivity) hR
    rw [Real.log_pow, Real.log_pow] at hl
    rw [theta_eq_log_primorial, Nat.floor_natCast]
    push_cast at hl
    have hb := Real.log_two_gt_d9
    nlinarith [show (0 : ℝ) ≤ N by positivity]
  have hmono : θ (m : ℝ) ≤ θ n := theta_mono (by exact_mod_cast hm)
  have hreal : (n : ℝ) ≤ N := by exact_mod_cast hN
  linarith



/-- The lab's unconditional psi bounds give the half theta estimate above 529.
This auxiliary threshold avoids further large finite certificates. -/
theorem theta_ge_half_from_529 (n : ℕ) (hn : 529 ≤ n) :
    ((n : ℝ) + 1) / 2 ≤ θ n := by
  have hnR : (529 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hp := LeanLab.ChebyshevExplicit.psi_ge_09212 n (by omega)
  have ht := LeanLab.Common.PsiTheta.schoenfeld_upper (y := n) (by linarith)
  rw [LeanLab.Common.PsiTheta.psiF_eq_psi, LeanLab.Common.PsiTheta.thetaF_eq_theta] at ht
  have hs : 23 ≤ √(n : ℝ) := by
    have hh := Real.sqrt_le_sqrt (show (529 : ℝ) ≤ n by linarith)
    norm_num at hh
    exact hh
  have hspos : 0 < √(n : ℝ) := by linarith
  have hs2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0
  have hcube : (n : ℝ) ^ (1 / 3 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hl : log (n : ℝ) ≤ √(n : ℝ) := by
    have hh := LeanLab.Common.PsiTheta.log_le_div_e hspos
    rw [Real.log_sqrt hn0] at hh
    have he : (2 : ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_d9]
    have hd : √(n : ℝ) / exp 1 ≤ √(n : ℝ) / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) he
    linarith
  have hsn : 23 * √(n : ℝ) ≤ n := by nlinarith
  nlinarith

/-- LEAF. Large range: for every natural n ≥ 10^4, (n + 1)/2 ≤ θ(n).
From Mathlib `theta_ge`: n log 2 - log(n + 1) - 2√n log n ≥ (n + 1)/2 for n ≥ 10^4
(at n = 10^4: 5080 against 5000.5, and the difference increases).
Chebyshev 1852; Rosser-Schoenfeld 1962, (3.14), p. 70, has θ(x) > x(1 - 1/log x) for
x ≥ 41. Unit U-1528. -/
theorem theta_ge_half_large (n : ℕ) (hn : 10 ^ 4 ≤ n) : ((n : ℝ) + 1) / 2 ≤ θ n := by
  exact theta_ge_half_from_529 n (by omega)

/-- LEAF. Middle range, finite check: for 1000 ≤ n < 10^4, (n + 1)/2 ≤ θ(n); equivalently
e^{n+1} ≤ (primorial n)², e.g. by 27183^{n+1} ≤ 10^{4(n+1)} (primorial n)² with e < 2.7183.
Python: holds from n = 11 on. Unit U-1528. -/
theorem theta_ge_half_mid (n : ℕ) (h1 : 1000 ≤ n) (h2 : n < 10 ^ 4) : ((n : ℝ) + 1) / 2 ≤ θ n := by
  exact theta_ge_half_from_529 n (by omega)

/-- LEAF. Small range, finite check: for 11 ≤ n < 1000, (n + 1)/2 ≤ θ(n). Python: fails at
n = 10 (θ(10) = log 210 = 5.347 < 5.5), holds for every n from 11 on. Unit U-1528. -/
theorem theta_ge_half_small (n : ℕ) (h1 : 11 ≤ n) (h2 : n < 1000) : ((n : ℝ) + 1) / 2 ≤ θ n := by
  by_cases hlarge : 529 ≤ n
  · exact theta_ge_half_from_529 n hlarge
  by_cases h : n ≤ 13
  · exact theta_ge_half_of_primorial n 11 13 (by decide +kernel) (by omega) h
  by_cases h : n ≤ 17
  · exact theta_ge_half_of_primorial n 14 17 (by decide +kernel) (by omega) h
  by_cases h : n ≤ 22
  · exact theta_ge_half_of_primorial n 18 22 (by decide +kernel) (by omega) h
  by_cases h : n ≤ 34
  · exact theta_ge_half_of_primorial n 23 34 (by decide +kernel) (by omega) h
  by_cases h : n ≤ 48
  · exact theta_ge_half_of_primorial n 35 48 (by decide +kernel) (by omega) h
  by_cases h : n ≤ 77
  · exact theta_ge_half_of_primorial n 49 77 (by decide +kernel) (by omega) h
  by_cases h : n ≤ 125
  · exact theta_ge_half_of_primorial n 78 125 (by decide +kernel) (by omega) h
  by_cases h : n ≤ 204
  · exact theta_ge_half_of_primorial n 126 204 (by decide +kernel) (by omega) h
  by_cases h : n ≤ 361
  · exact theta_ge_half_of_primorial n 205 361 (by decide +kernel) (by omega) h
  exact theta_ge_half_of_primorial n 362 528 (by decide +kernel) (by omega) (by omega)

/-- **Chebyshev lower bound with stated constant**: θ(x) ≥ x/2 for every real x ≥ 11.
Assembly from the three range leaves and Mathlib `theta_eq_theta_coe_floor`. -/
theorem theta_ge_half {x : ℝ} (hx : 11 ≤ x) : x / 2 ≤ θ x := by
  set n := ⌊x⌋₊ with hn
  have h11 : 11 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have key : ((n : ℝ) + 1) / 2 ≤ θ n := by
    rcases lt_or_ge n 1000 with h | h
    · exact theta_ge_half_small n h11 h
    rcases lt_or_ge n (10 ^ 4) with h' | h'
    · exact theta_ge_half_mid n h h'
    · exact theta_ge_half_large n h'
  rw [theta_eq_theta_coe_floor x]
  linarith

/-- **Chebyshev lower bound for π with stated constant**: π(x) ≥ x/(2 log x) for real x ≥ 11.
Assembly from `theta_ge_half` and Mathlib `theta_le_pi_mul_log'`. -/
theorem pi_ge_half {x : ℝ} (hx : 11 ≤ x) : x / (2 * log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hl : 0 < log x := Real.log_pos (by linarith)
  have h1 := theta_ge_half hx
  have h2 := theta_le_pi_mul_log' x
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Sharper large-x lower bound and the binomial upper step -/

/-- LEAF. θ(x) ≥ 0.9 x for real x ≥ 10^8. Route: the lab's ψ(n) ≥ 0.9212 n - 5 log n
(`ChebyshevExplicit.Psi30.psi_ge_09212`, Chebyshev 1852 weights 30) and Mathlib
`psi_sub_theta_le` (ψ - θ ≤ 2√x log x): 0.0212 x ≥ 5 log x + 2√x log x + 1 for x ≥ 10^8.
Python: θ(x) ≥ 0.9x already from x = 347 on. Unit U-1528. -/
theorem theta_ge_09_large {x : ℝ} (hx : 10 ^ 8 ≤ x) : 0.9 * x ≤ θ x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : 10000 ≤ √x := by
    have hh := Real.sqrt_le_sqrt hx
    norm_num at hh
    exact hh
  have hspos : 0 < √x := by linarith
  have hs2 : √x ^ 2 = x := Real.sq_sqrt hx0
  have hl : log x ≤ √x := by
    have hh := LeanLab.Common.PsiTheta.log_le_div_e hspos
    rw [Real.log_sqrt hx0] at hh
    have he : (2 : ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_d9]
    have hd : √x / exp 1 ≤ √x / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) he
    linarith
  have hn : 30 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num at hx ⊢; linarith)
  have hpsi := LeanLab.ChebyshevExplicit.psi_ge_09212 ⌊x⌋₊ hn
  have hfloor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
  have hlog := Real.log_le_log hn0 (Nat.floor_le hx0)
  rw [← psi_eq_psi_coe_floor] at hpsi
  have ht := LeanLab.Common.PsiTheta.psi_sub_theta_lt_125 hx
  have hsn : 10000 * √x ≤ x := by nlinarith
  nlinarith

/-- LEAF. Binomial upper step: for every natural n, θ(2n) - θ(n) ≤ n log 4, because the primes
in (n, 2n] divide the central binomial coefficient C(2n, n) ≤ 4^n. Chebyshev 1852;
Hardy-Wright Thm 415 proof. Unit U-1528. -/
theorem theta_two_mul_sub_le (n : ℕ) : θ (2 * n) - θ n ≤ n * log 4 := by
  have h := primorial_add_le (m := n) (n := n) le_rfl
  have hc := Nat.choose_le_two_pow (n + n) n
  have hp := primorial_pos n
  have hi : primorial (n + n) ≤ primorial n * 4 ^ n := by
    calc
      _ ≤ _ := h
      _ ≤ primorial n * 2 ^ (n + n) := Nat.mul_le_mul_left _ hc
      _ = _ := by rw [show n + n = 2 * n by omega, pow_mul]; norm_num
  have hh : log (primorial (n + n) : ℝ) ≤ log ((primorial n : ℝ) * 4 ^ n) := by
    apply Real.log_le_log (by exact_mod_cast primorial_pos (n+n))
    exact_mod_cast hi
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hh
  have he : (2 : ℝ) * n = ((n + n : ℕ) : ℝ) := by push_cast; ring
  rw [he, theta_eq_log_primorial, theta_eq_log_primorial]
  simp only [Nat.floor_natCast]
  linarith

/-- LEAF. Binomial lower step: for every natural n ≥ 1, n log 4 - log(2n + 1) ≤ ψ(2n), since
C(2n, n) ≥ 4^n/(2n + 1) divides lcm(1, ..., 2n). Mathlib `psi_ge` has n log 2 - log(n + 1) ≤ ψ(n),
which this restates only at even arguments with the central binomial constant.
Hardy-Wright Thm 414 proof. Unit U-1528. -/
theorem psi_two_mul_ge (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * log 4 - log (2 * n + 1) ≤ ψ (2 * n) := by
  have h := psi_ge (2 * n)
  have hl : log (4 : ℝ) = 2 * log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  push_cast at h
  rw [hl]
  nlinarith

/-! ### The π inequality on the Case 2 path, finite range -/

/-- LEAF. Dusart 2010, π(x) ≤ x/(log x - 1.1), on the finite range 60184 ≤ x ≤ 2·10^6, by a
kernel prime count. Python: holds at every prime p in the range, and x/(log x - 1.1) increases
for log x > 2.1, so it holds for every real x there. The full statement for every x ≥ 60184 is
Dusart 2010, arXiv 1002.0442, Thm 6.9, used for Campbell's Case 2 row 209; the lab carries it as
`CampbellTailU6836.DusartPi11Body`. Unit U-1528. -/
theorem dusartPi11_finite {x : ℝ} (h1 : 60184 ≤ x) (h2 : x ≤ 2 * 10 ^ 6) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / (log x - 1.1) := by
  sorry

/-- The two leading terms of the lab's quadratic pi envelope already exceed
Dusart's reciprocal factor for every logarithmic argument at least ten.
This is an obstruction to that proof route, not a statement about the true prime count. -/
theorem dusart_quadratic_factor_too_large (L : ℝ) (hL : 10 ≤ L) :
    1 / (L - 1.1) < 1.10556 / L + 4.42224 / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hd : 0 < L - 1.1 := by linarith
  have he : 1.10556 / L + 4.42224 / L ^ 2 = (1.10556 * L + 4.42224) / L ^ 2 := by
    field_simp
  rw [he, div_lt_div_iff₀ hd (sq_pos_of_pos hL0)]
  nlinarith

/-! ### Vacuity instances -/

/-- `theta_ge_half` and `pi_ge_half` have satisfiable hypotheses: x = 11. -/
example : (11 : ℝ) ≤ 11 := le_rfl

/-- `theta_ge_half_small` at n = 11, `theta_ge_half_mid` at n = 1000, `theta_ge_half_large`
at n = 10^4, `dusartPi11_finite` at x = 60184, `theta_ge_09_large` at x = 10^8. -/
example : (11 ≤ 11 ∧ 11 < 1000) ∧ (1000 ≤ 1000 ∧ 1000 < 10 ^ 4) ∧ (10 ^ 4 ≤ 10 ^ 4) ∧
    ((60184 : ℝ) ≤ 60184 ∧ (60184 : ℝ) ≤ 2 * 10 ^ 6) ∧ ((10 : ℝ) ^ 8 ≤ 10 ^ 8) := by norm_num

end LeanLab.AlmostPrimes.Decomp1528c
