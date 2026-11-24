/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, page 3 and page 13.
SPLIT of sifted_count_lower_v3 from SPLIT_sieve_positive_v3.lean, ROUTE BURST S98 burst-20261122.
Page 13: Theorem 4.2 gives S(A, P(z)) > 38 U_N N / log^2 N if k1 < Kδ(x1) and
S(A, P(z)) > 5 U_N N / log^2 N if k1 ≥ Kδ(x1), z = N^(1/40), all even N ≥ exp(exp 7.9).
Page 3: U_N = 2 e^(-γ) prod_{p>2} (1 - 1/(p-1)^2) prod_{p>2, p | N} (p-1)/(p-2), and each
factor (p-1)/(p-2) is at least 1, so U_N ≥ 2 e^(-γ) C_2 with C_2 the twin prime constant.
The final constant: 5 * 2 * 0.56145 * 0.66016 = 3.70646 > 3.7, proved below by linarith.
AI wrote this Lean code.
-/
import LeanLab.JohnstonStarichkova.SPLIT_sieve_positive_v3

namespace LeanLab.JohnstonStarichkova
open LeanLab.AlmostPrimes

/-
Numerics: e^(-γ) = 0.5614594836 with γ = 0.5772156649, margin 9.5e-6 over 0.56145.
-/
/-- LEAF: P0019 v3 page 3 constant in U_N: e^(-γ) > 0.56145, γ the Euler constant
0.5772156649, so e^(-γ) = 0.56145948. Needs γ < 0.577217, sharper than the Mathlib
bound γ < 2/3, via an Euler Maclaurin bound on H_n - log n, then an exp lower
bound. Class HARD. -/
theorem exp_neg_euler_gt : (0.56145 : ℝ) < Real.exp (-Real.eulerMascheroniConstant) := by
  sorry

/-
Numerics: C_2 = 0.6601618158; partial product over 2 < p < 10^4 is about 0.66017,
tail factor prod_{p ≥ 10^4} (1 - 1/(p-1)^2) ≥ 1 - 1.1e-5. Margin 1.8e-6 over 0.66016.
-/
/-- LEAF: P0019 v3 page 3, the twin prime constant inside U_N:
C_2 = prod over primes p > 2 of (1 - 1/(p-1)^2) = 0.66016181... exceeds 0.66016.
Finite partial product plus an explicit tail bound. Class HARD. -/
theorem twin_prime_const_gt :
    (0.66016 : ℝ) < ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2) := by
  sorry

/-
Numerics: at N = exp(exp 7.9), log N ≈ 2697.3; the bound 5 U N / log^2 N with
U = 2 e^(-γ) C_2 ≈ 0.74131 is about 5.1e-7 N, positive and huge.
-/
/-- LEAF: P0019 v3 page 13, proof of Theorem 1.3: Theorem 4.2 with (4.6), u0 = 400,
δ = 1.3, α = 0.25, M = 40 gives S(A, P(z)) > 5 U_N N / log^2 N in both cases on k1,
z = N^(1/40), even N ≥ exp(exp 7.9); with U_N ≥ 2 e^(-γ) C_2 from page 3 and S
counting primes p < N, p ∤ N, every prime q | N - p having q^40 ≥ N. Class HARD. -/
theorem sifted_count_lower_UN (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    5 * (2 * Real.exp (-Real.eulerMascheroniConstant) *
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)) *
        (N : ℝ) / Real.log N ^ 2 <
      (({p : ℕ | p.Prime ∧ p < N ∧ ¬ p ∣ N ∧
        ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40} : Set ℕ).ncard : ℝ) := by
  sorry

theorem sifted_count_lower_v3_split (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    3.7 * (N : ℝ) / Real.log N ^ 2 <
      (({p : ℕ | p.Prime ∧ p < N ∧ ¬ p ∣ N ∧
        ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40} : Set ℕ).ncard : ℝ) := by
  refine lt_trans ?_ (sifted_count_lower_UN N hN hX)
  have he := exp_neg_euler_gt
  have hc := twin_prime_const_gt
  set E := Real.exp (-Real.eulerMascheroniConstant)
  set C := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hX
  have hN1 : (1 : ℝ) < N := by
    refine lt_of_lt_of_le ?_ hX
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (Real.exp_pos _)
  have hL : 0 < Real.log N := Real.log_pos hN1
  have hEC : (0.56145 : ℝ) * 0.66016 < E * C := by
    have : (0.56145 : ℝ) * 0.66016 < E * 0.66016 := by nlinarith
    have h2 : E * 0.66016 < E * C := by
      have : 0 < E := Real.exp_pos _
      nlinarith
    linarith
  have hk : (3.7 : ℝ) < 5 * (2 * E * C) := by nlinarith
  have hpos : 0 < (N : ℝ) / Real.log N ^ 2 := by positivity
  have := mul_lt_mul_of_pos_right hk hpos
  calc 3.7 * (N : ℝ) / Real.log N ^ 2 = 3.7 * ((N : ℝ) / Real.log N ^ 2) := by ring
    _ < 5 * (2 * E * C) * ((N : ℝ) / Real.log N ^ 2) := this
    _ = 5 * (2 * E * C) * (N : ℝ) / Real.log N ^ 2 := by ring

end LeanLab.JohnstonStarichkova
