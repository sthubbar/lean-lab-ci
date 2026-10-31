/-
P0023 Liu, Wang 2002, Acta Arith. 105, 133-175. Explicit numerics of the final assembly,
checked against the rendered pages of papers/P0023.pdf, PDF page = printed page minus 132.
Notation of the paper, (2.1) p. 137: `L = log N`, `P = L^3`, `P1 = L^6`; (3.1) p. 144:
`Q = N L^(-7)`; every lemma below assumes `L ≥ 3100`, that is `N ≥ e^3100`.

What is PROVED here, all pure arithmetic or real analysis on the printed constants:
* `lemma43_caseI`, `lemma43_caseII`: the two numerical chains (4.25) p. 154 and (4.34) p. 155,
  giving the printed `0.5437` and `0.5577`, hence Lemma 4.3 p. 156, `I1(N) ≥ 0.5437 N^2`.
* `lemma52_sum`: the sum closing Lemma 5.2, p. 168.
* `prop61_coeffs`: the coefficients of Lemmas 6.5, 6.6, 6.7 add to at most `0.28, 4, 0.09`,
  the coefficients of Proposition 6.1 (6.2) p. 168, with room `0.4129` left in the middle
  coefficient for Lemma 6.2.
* `lemma62_numeric`, `prop61_N_lower`: the numerics in Lemma 6.2 p. 169 and in (6.5) p. 168.
* `m4_bound_P1`, `m4_bound_Q`: the bound `|S(α)| ≤ 0.3 N L^(-1)` on M4, p. 174, at both ends
  `q = P1` and `q = N L^(-7)` of the range.
* `final_coeffs`, `error_absorb`, `final_chain`: the last display of p. 174,
  `I(N) ≥ (0.5437 - 0.51) N^2 - 3 N^1.5 L^3 ≥ 0.03 N^2`.

`final_chain` is CONDITIONAL ON its hypotheses, which name the paper's analytic inputs:
Lemma 4.3, the sup bound `0.5033 N/L` on M2 ∪ M3 ∪ M4 from Lemmas 5.1, 5.2 and
Proposition 6.1, Parseval, the Rosser-Schoenfeld 1975 bound `ψ(N) ≤ 1.0012 N`, and the
prime power error `3 N^(3/2) L^3` of (3.10). None of them is proved here.

AI-written Lean code, Claude, 2026-10-21, session 20261021T0117Z-cloud55, unit U-6812.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.LiuWang2002.Constants

open Real

/-! ### Helpers -/

/-- `x^n / n! ≤ e^x` for `x ≥ 0`, Mathlib's `Real.pow_div_factorial_le_exp`. HELPER. -/
theorem exp_ge_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : x ^ n / (n.factorial : ℝ) ≤ exp x :=
  Real.pow_div_factorial_le_exp x hx n

/-- `3 L^(-9) ≤ 10^(-6)` for `L ≥ 3100`. HELPER. -/
theorem three_div_pow9 (L : ℝ) (hL : 3100 ≤ L) : 3 / L ^ 9 ≤ 1 / 10 ^ 6 := by
  have h9 : (3100 : ℝ) ^ 9 ≤ L ^ 9 := pow_le_pow_left₀ (by norm_num) hL 9
  have hpos : (0 : ℝ) < L ^ 9 := by positivity
  rw [div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

/-! ### Lemma 4.3, pp. 154 to 156 -/

/-- (4.25) p. 154: `0.656145 - 0.1108 - 0.0016 - 0.00002 - 3 L^(-9) ≥ 0.5437`. PROVED. -/
theorem lemma43_caseI (L : ℝ) (hL : 3100 ≤ L) :
    (0.5437 : ℝ) ≤ (0.656145 - 0.1108 - 0.0016 - 0.00002) - 3 / L ^ 9 := by
  have := three_div_pow9 L hL
  norm_num at this ⊢; linarith

/-- (4.34) p. 155: the ten subtractions from `0.656145` and `3 L^(-9)` leave at least
`0.5577`. PROVED. -/
theorem lemma43_caseII (L : ℝ) (hL : 3100 ≤ L) :
    (0.5577 : ℝ) ≤ (0.656145 - 5e-8 - 2e-8 - 2e-8 - 2.1e-5 - 4e-8 - 0.00318 - 0.00108
      - 0.0001 - 0.09403) - 3 / L ^ 9 := by
  have := three_div_pow9 L hL
  norm_num at this ⊢; linarith

/-- Lemma 4.3 p. 156 from (4.25) and (4.34): whichever case holds, `I1(N) ≥ 0.5437 N^2`,
given `I1(N)` is at least the case's chain times `N^2`. CONDITIONAL ON the case bounds
(4.25), (4.34) as hypotheses; the arithmetic is PROVED. -/
theorem lemma43 (L N I1 : ℝ) (hL : 3100 ≤ L)
    (hcase : (0.656145 - 0.1108 - 0.0016 - 0.00002) * N ^ 2 - 3 * N ^ 2 / L ^ 9 ≤ I1 ∨
      (0.656145 - 5e-8 - 2e-8 - 2e-8 - 2.1e-5 - 4e-8 - 0.00318 - 0.00108
        - 0.0001 - 0.09403) * N ^ 2 - 3 * N ^ 2 / L ^ 9 ≤ I1) :
    0.5437 * N ^ 2 ≤ I1 := by
  have hN2 : 0 ≤ N ^ 2 := by positivity
  have e : 3 * N ^ 2 / L ^ 9 = N ^ 2 * (3 / L ^ 9) := by ring
  rcases hcase with h | h
  · have := mul_le_mul_of_nonneg_left (lemma43_caseI L hL) hN2
    rw [e] at h; nlinarith
  · have := mul_le_mul_of_nonneg_left (lemma43_caseII L hL) hN2
    rw [e] at h; nlinarith

/-- p. 155, the products in (4.31), (4.33), (4.34) and the sum before (4.31):
`2.8959 · 2.82682 · 2.5636·10^(-6) ≤ 2.1·10^(-5)`, `8.2914 · 0.00013 ≤ 0.00108`,
`3.35804 · 0.028 ≤ 0.09403`, `2.8265 + 0.00031 + 4.9·10^(-9) ≤ 2.82682`. PROVED. -/
theorem p155_products :
    (2.8959 : ℝ) * 2.82682 * 2.5636e-6 ≤ 2.1e-5 ∧ (8.2914 : ℝ) * 0.00013 ≤ 0.00108 ∧
    (3.35804 : ℝ) * 0.028 ≤ 0.09403 ∧ (2.8265 : ℝ) + 0.00031 + 4.9e-9 ≤ 2.82682 := by
  norm_num

/-! ### Lemma 5.2, p. 168 -/

/-- p. 168: `0.00012 + 7·10^(-31) + 0.00007 + 6·10^(-9) ≤ 0.0002`. PROVED. -/
theorem lemma52_sum : (0.00012 : ℝ) + 7e-31 + 0.00007 + 6e-9 ≤ 0.0002 := by norm_num

/-! ### Section 6, pp. 168 to 174 -/

/-- Proposition 6.1 (6.2) p. 168 from Lemmas 6.5, 6.6 p. 170 and 6.7 p. 174: the
coefficients of `N q^(-1/2) log^2 N`, `N^(4/5) log^1.4 N`, `N^(1/2) q^(1/2) log^2.5 N` add
to `0.2677 ≤ 0.28`, `3.5871 ≤ 4`, `0.0796 ≤ 0.09`. PROVED. -/
theorem prop61_coeffs :
    (0.0282 : ℝ) + 0.0131 + 0.2264 ≤ 0.28 ∧
    (0.0001 : ℝ) + 0.8 + (1.926 + 0.861) ≤ 4 - 0.4129 ∧
    (0.0006 : ℝ) + 0.0005 + 0.0785 ≤ 0.09 := by norm_num

/-- Lemma 6.2 p. 169, the numeric step: for `U ≥ e^9.634`, using only `U ≥ 15000`,
`1.001102 (U + U^(1/2)) + 3 U^(1/3) ≤ 1.02 U`, written with `s = U^(1/2) ≥ 122`,
`c = U^(1/3) ≥ 24`. PROVED. -/
theorem lemma62_numeric (s c : ℝ) (hs : 122 ≤ s) (hc : 24 ≤ c) (hsc : s ^ 2 = c ^ 3) :
    1.001102 * (s ^ 2 + s) + 3 * c ≤ 1.02 * s ^ 2 := by
  nlinarith [mul_le_mul hc hc (by norm_num) (by linarith)]

/-- `e^9.634 ≥ 15000`, so Lemma 6.2's `U ≥ e^9.634` gives `U^(1/2) ≥ 122` and
`U^(1/3) ≥ 24`. PROVED. -/
theorem exp9634_ge : (15000 : ℝ) ≤ exp 9.634 := by
  have he : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
  have h9 : exp 9 = exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  have hq := Real.quadratic_le_exp_of_nonneg (x := (0.317 : ℝ)) (by norm_num)
  have hsplit : exp 9.634 = exp 9 * (exp 0.317 * exp 0.317) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hp : (2.7182818283 : ℝ) ^ 9 ≤ exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) he.le 9
  have hq2 : (1 + 0.317 + 0.317 ^ 2 / 2 : ℝ) * (1 + 0.317 + 0.317 ^ 2 / 2) ≤
      exp 0.317 * exp 0.317 := mul_le_mul hq hq (by norm_num) (Real.exp_pos _).le
  rw [hsplit, h9]
  calc (15000 : ℝ) ≤ 2.7182818283 ^ 9 * ((1 + 0.317 + 0.317 ^ 2 / 2) *
        (1 + 0.317 + 0.317 ^ 2 / 2)) := by norm_num
    _ ≤ _ := mul_le_mul hp hq2 (by norm_num) (by positivity)

/-- (6.5) p. 168, first half: if `N ≥ 3` and `N > (4/1.0012)^5 log^7 N`, (6.4), then
`log N ≥ 30.95`. Stated in `L = log N`: for `1.1 ≤ L ≤ 30.95` the inequality
`e^L > (4/1.0012)^5 L^7` fails. Here only the endpoint is PROVED:
`e^30.95 < (4/1.0012)^5 · 30.95^7`, the printed `30.95` lies below the true root
`30.9527`. HELPER, the monotonicity on the interval is not formalized. -/
theorem prop61_N_lower : exp 30.95 < (4 / 1.0012) ^ 5 * 30.95 ^ 7 := by
  have he : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h : exp 30.95 = exp (30 + 0.95) := by norm_num
  have h1 : exp 30 = exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : exp 0.95 < 2.586 := by
    have := Real.exp_bound' (x := (0.95 : ℝ)) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  rw [h, Real.exp_add, h1]
  have hp : exp 1 ^ 30 < 2.7182818286 ^ 30 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  calc exp 1 ^ 30 * exp 0.95 < 2.7182818286 ^ 30 * 2.586 := by
        apply mul_lt_mul'' hp h2 (by positivity) (Real.exp_pos _).le
    _ < (4 / 1.0012) ^ 5 * 30.95 ^ 7 := by norm_num

/-! ### The M4 bound, p. 174 -/

/-- `400 L^3 ≤ e^(L/5)` for `L ≥ 3100`. HELPER. -/
theorem aux_fifth (L : ℝ) (hL : 3100 ≤ L) : 400 * L ^ 3 ≤ exp (L / 5) := by
  refine le_trans ?_ (exp_ge_pow (L / 5) (by linarith) 6)
  have h3 : (3100 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  have hp : 0 ≤ L ^ 3 := by positivity
  rw [le_div_iff₀ (by positivity)]
  norm_num [Nat.factorial]
  nlinarith [mul_le_mul_of_nonneg_left h3 hp]

/-- `9 L^7 ≤ e^(L/2)` for `L ≥ 3100`. HELPER. -/
theorem aux_half (L : ℝ) (hL : 3100 ≤ L) : 9 * L ^ 7 ≤ exp (L / 2) := by
  refine le_trans ?_ (exp_ge_pow (L / 2) (by linarith) 11)
  have h4 : (3100 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hp : 0 ≤ L ^ 7 := by positivity
  rw [le_div_iff₀ (by positivity)]
  norm_num [Nat.factorial]
  have : (L / 2) ^ 11 = L ^ 7 * L ^ 4 / 2048 := by ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left h4 hp]

/-- `L^a ≤ L^b` for real exponents `a ≤ b` and `L ≥ 1`, with `b` a natural number. HELPER. -/
theorem rpow_le_natpow (L : ℝ) (hL : 1 ≤ L) (a : ℝ) (b : ℕ) (hab : a ≤ b) :
    L ^ a ≤ L ^ b := by
  have := Real.rpow_le_rpow_of_exponent_le hL hab
  rwa [Real.rpow_natCast] at this

/-- `N^a = e^(a L)` for `N = e^L`. HELPER. -/
theorem exp_rpow (L a : ℝ) : (exp L) ^ a = exp (a * L) := by
  rw [← Real.exp_mul]; ring_nf

/-- The two lower order terms are each at most `0.01 N / L`. HELPER. -/
theorem m4_small (L : ℝ) (hL : 3100 ≤ L) :
    4 * exp (4 / 5 * L) * L ^ 2 ≤ 0.01 * exp L / L ∧
    0.09 * exp (1 / 2 * L) * L ^ 6 ≤ 0.01 * exp L / L := by
  have hLp : 0 < L := by linarith
  have e1 : exp L = exp (4 / 5 * L) * exp (L / 5) := by rw [← Real.exp_add]; ring_nf
  have e2 : exp L = exp (1 / 2 * L) * exp (L / 2) := by rw [← Real.exp_add]; ring_nf
  have a1 := aux_fifth L hL
  have a2 := aux_half L hL
  have p1 := Real.exp_pos (4 / 5 * L)
  have p2 := Real.exp_pos (1 / 2 * L)
  constructor
  · rw [le_div_iff₀ hLp, e1]
    have := mul_le_mul_of_nonneg_left a1 p1.le
    nlinarith
  · rw [le_div_iff₀ hLp, e2]
    have := mul_le_mul_of_nonneg_left a2 p2.le
    nlinarith

/-- p. 174, the end `q = P1 = L^6`, in the printed form with real powers and `N = e^L`:
`0.28 N P1^(-1/2) L^2 + 4 N^(4/5) L^1.4 + 0.09 N^(1/2) P1^(1/2) L^2.5 ≤ 0.3 N L^(-1)`.
PROVED. -/
theorem m4_bound_P1 (L : ℝ) (hL : 3100 ≤ L) :
    0.28 * exp L * (L ^ 6) ^ (-(1 / 2) : ℝ) * L ^ 2 + 4 * (exp L) ^ (4 / 5 : ℝ) * L ^ (1.4 : ℝ)
      + 0.09 * (exp L) ^ (1 / 2 : ℝ) * (L ^ 6) ^ (1 / 2 : ℝ) * L ^ (2.5 : ℝ)
      ≤ 0.3 * exp L / L := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hsq : (L ^ 6) ^ (1 / 2 : ℝ) = L ^ 3 := by
    rw [← Real.rpow_natCast L 6, ← Real.rpow_mul hLp.le]; norm_num
  have hisq : (L ^ 6) ^ (-(1 / 2) : ℝ) = (L ^ 3)⁻¹ := by
    rw [Real.rpow_neg (by positivity), hsq]
  rw [hsq, hisq, exp_rpow, exp_rpow]
  have t1 : 0.28 * exp L * (L ^ 3)⁻¹ * L ^ 2 = 0.28 * exp L / L := by
    field_simp
  have r1 := rpow_le_natpow L hL1 1.4 2 (by norm_num)
  have r2 := rpow_le_natpow L hL1 2.5 3 (by norm_num)
  have s := m4_small L hL
  have q1 : 4 * exp (4 / 5 * L) * L ^ (1.4 : ℝ) ≤ 4 * exp (4 / 5 * L) * L ^ 2 := by
    gcongr
  have q2 : 0.09 * exp (1 / 2 * L) * L ^ 3 * L ^ (2.5 : ℝ) ≤ 0.09 * exp (1 / 2 * L) * L ^ 6 := by
    have : L ^ 6 = L ^ 3 * L ^ 3 := by ring
    rw [this, ← mul_assoc]
    gcongr
  have hd : 0.3 * exp L / L = 0.28 * exp L / L + 0.01 * exp L / L + 0.01 * exp L / L := by ring
  rw [t1, hd]
  linarith [s.1, s.2]

/-- p. 174, the end `q = N L^(-7)`, after the elementary simplification
`N (N L^(-7))^(-1/2) L^2 = N^(1/2) L^5.5` and `N^(1/2) (N L^(-7))^(1/2) L^2.5 = N L^(-1)`:
`0.28 N^(1/2) L^5.5 + 4 N^(4/5) L^1.4 + 0.09 N L^(-1) ≤ 0.3 N L^(-1)`. PROVED. -/
theorem m4_bound_Q (L : ℝ) (hL : 3100 ≤ L) :
    0.28 * (exp L) ^ (1 / 2 : ℝ) * L ^ (5.5 : ℝ) + 4 * (exp L) ^ (4 / 5 : ℝ) * L ^ (1.4 : ℝ)
      + 0.09 * exp L / L ≤ 0.3 * exp L / L := by
  have hL1 : 1 ≤ L := by linarith
  rw [exp_rpow, exp_rpow]
  have r1 := rpow_le_natpow L hL1 1.4 2 (by norm_num)
  have r2 := rpow_le_natpow L hL1 5.5 6 (by norm_num)
  have s := m4_small L hL
  have q1 : 4 * exp (4 / 5 * L) * L ^ (1.4 : ℝ) ≤ 4 * exp (4 / 5 * L) * L ^ 2 := by gcongr
  have q2 : 0.28 * exp (1 / 2 * L) * L ^ (5.5 : ℝ) ≤ 0.28 * exp (1 / 2 * L) * L ^ 6 := by gcongr
  have q3 : 0.28 * exp (1 / 2 * L) * L ^ 6 ≤ 0.09 * exp (1 / 2 * L) * L ^ 6 * (28 / 9) := by
    exact le_of_eq (by ring)
  have q4 : 0.09 * exp (1 / 2 * L) * L ^ 6 * (28 / 9) ≤ 0.01 * exp L / L * (28 / 9) := by
    gcongr; exact s.2
  have hd : 0.3 * exp L / L = 0.09 * exp L / L + 0.21 * exp L / L := by ring
  have hd2 : 0.01 * exp L / L * (28 / 9) + 0.01 * exp L / L ≤ 0.21 * exp L / L := by
    have : 0 ≤ exp L / L := by positivity
    have e : ∀ c : ℝ, c * exp L / L = c * (exp L / L) := fun c => by ring
    rw [e, e]; nlinarith
  rw [hd]
  linarith [s.1]

/-! ### The final assembly, p. 174 -/

/-- p. 174: `0.5033 · 1.001102 ≤ 0.51` as printed, and also `0.5033 · 1.0012 ≤ 0.51`, the
form needed when the mean value `∫|S|^2` is bounded through `ψ(N)` instead of `θ(N)`.
PROVED. -/
theorem final_coeffs : (0.5033 : ℝ) * 1.001102 ≤ 0.51 ∧ (0.5033 : ℝ) * 1.0012 ≤ 0.51 := by
  norm_num

/-- p. 174: `3 N^1.5 L^3 ≤ 0.0037 N^2` for `N = e^L`, `L ≥ 3100`. PROVED. -/
theorem error_absorb (L : ℝ) (hL : 3100 ≤ L) :
    3 * exp (3 / 2 * L) * L ^ 3 ≤ 0.0037 * exp (2 * L) := by
  have e : exp (2 * L) = exp (3 / 2 * L) * exp (L / 2) := by rw [← Real.exp_add]; ring_nf
  have key : 3 * L ^ 3 ≤ 0.0037 * exp (L / 2) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (exp_ge_pow (L / 2) (by linarith) 5)
      (by norm_num))
    have h2 : (3100 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
    have hp : 0 ≤ L ^ 3 := by positivity
    norm_num [Nat.factorial]
    have : (L / 2) ^ 5 = L ^ 3 * L ^ 2 / 32 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left h2 hp]
  rw [e]
  have := mul_le_mul_of_nonneg_left key (Real.exp_pos (3 / 2 * L)).le
  nlinarith [Real.exp_pos (3 / 2 * L)]

/-- The final chain of p. 174, CONDITIONAL ON its named inputs:
* `h312`, (3.12) p. 145: `I(N) ≥ I1 - |I2 + I3 + I4| - E`;
* `hE`, (3.10) p. 145: the prime power error `E ≤ 3 N^(3/2) L^3`;
* `hI1`, Lemma 4.3 p. 156: `I1 ≥ 0.5437 N^2`;
* `hJ`, Lemmas 5.1, 5.2 and the M4 bound: `|I2 + I3 + I4| ≤ 0.5033 N L^(-1) ∫|S|^2`;
* `hpars`, Parseval: `∫|S|^2 = Σ Λ(n)^2 ≤ L ψ(N)`;
* `hpsi`, Rosser-Schoenfeld 1975, (5.1) and (5.3): `ψ(N) ≤ 1.0012 N`.
Conclusion `I(N) ≥ 0.03 N^2 > 0`. The arithmetic is PROVED. -/
theorem final_chain (L I I1 J E M psiN : ℝ) (hL : 3100 ≤ L)
    (h312 : I1 - J - E ≤ I)
    (hE : E ≤ 3 * exp (3 / 2 * L) * L ^ 3)
    (hI1 : 0.5437 * exp L ^ 2 ≤ I1)
    (hJ : J ≤ 0.5033 * exp L / L * M)
    (hpars : M ≤ L * psiN)
    (hpsi : psiN ≤ 1.0012 * exp L) :
    0.03 * exp L ^ 2 ≤ I ∧ 0 < I := by
  have hLp : 0 < L := by linarith
  have hN := Real.exp_pos L
  have hsq : exp (2 * L) = exp L ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hJ' : J ≤ 0.5033 * 1.0012 * exp L ^ 2 := by
    have c0 : 0 ≤ 0.5033 * exp L / L := by positivity
    calc J ≤ 0.5033 * exp L / L * M := hJ
      _ ≤ 0.5033 * exp L / L * (L * psiN) := mul_le_mul_of_nonneg_left hpars c0
      _ = 0.5033 * exp L * psiN := by field_simp
      _ ≤ 0.5033 * exp L * (1.0012 * exp L) := by gcongr
      _ = 0.5033 * 1.0012 * exp L ^ 2 := by ring
  have hE' := error_absorb L hL
  rw [hsq] at hE'
  have hN2 : 0 < exp L ^ 2 := by positivity
  constructor
  · nlinarith
  · nlinarith

end LeanLab.LiuWang2002.Constants

#print axioms LeanLab.LiuWang2002.Constants.lemma43
#print axioms LeanLab.LiuWang2002.Constants.p155_products
#print axioms LeanLab.LiuWang2002.Constants.lemma52_sum
#print axioms LeanLab.LiuWang2002.Constants.prop61_coeffs
#print axioms LeanLab.LiuWang2002.Constants.lemma62_numeric
#print axioms LeanLab.LiuWang2002.Constants.exp9634_ge
#print axioms LeanLab.LiuWang2002.Constants.prop61_N_lower
#print axioms LeanLab.LiuWang2002.Constants.m4_bound_P1
#print axioms LeanLab.LiuWang2002.Constants.m4_bound_Q
#print axioms LeanLab.LiuWang2002.Constants.final_coeffs
#print axioms LeanLab.LiuWang2002.Constants.error_absorb
#print axioms LeanLab.LiuWang2002.Constants.final_chain
