/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, page 4 list of definitions and page 13.
SPLIT of the LEAF sifted_count_lower_UN of SPLIT_sifted_count_lower_v3.lean, burst-20261122
session S153. Page 13 gives S(A, P(z)) > 5 U_N N / log^2 N with the full
U_N = 2 e^(-γ) prod_{p>2} (1 - 1/(p-1)^2) prod_{p>2, p | N} (p-1)/(p-2) of page 4, checked on the PDF.
The LEAF keeps that cited page 13 bound with the full U_N; the step to 2 e^(-γ) C_2 is PROVED here,
each factor (p-1)/(p-2) being at least 1.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.JohnstonStarichkova.SPLIT_twin_prime_const_gt

namespace LeanLab.JohnstonStarichkova

/-- LEAF: P0019 v3 page 13, proof of Theorem 1.3: Theorem 4.2 with (4.6), u0 = 400, δ = 1.3,
α = 0.25, M = 40 gives S(A, P(z)) > 5 U_N N / log^2 N in both cases on k1, z = N^(1/40), even N at
least exp(exp 7.9), with U_N the full page 4 constant 2 e^(-γ) C_2 prod_{p>2, p | N} (p-1)/(p-2);
S counts primes p < N, p ∤ N, with every prime q | N - p having q^40 ≥ N. Class HARD. -/
theorem sifted_count_lower_UN_full (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    5 * (2 * Real.exp (-Real.eulerMascheroniConstant) *
        (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)) *
        ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
        (N : ℝ) / Real.log N ^ 2 <
      (({p : ℕ | p.Prime ∧ p < N ∧ ¬ p ∣ N ∧
        ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40} : Set ℕ).ncard : ℝ) := by
  sorry

/-- P0019 v3 page 4: the factor of U_N over the odd primes dividing N is at least 1. -/
theorem UN_extra_factor_ge_one (N : ℕ) :
    1 ≤ ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  apply Finset.one_le_prod₀
  intro p hp
  have h2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The LEAF sifted_count_lower_UN, same statement, PROVED from sifted_count_lower_UN_full and
the page 4 bound U_N ≥ 2 e^(-γ) C_2. CONDITIONAL ON sifted_count_lower_UN_full. -/
theorem sifted_count_lower_UN_split (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    5 * (2 * Real.exp (-Real.eulerMascheroniConstant) *
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)) *
        (N : ℝ) / Real.log N ^ 2 <
      (({p : ℕ | p.Prime ∧ p < N ∧ ¬ p ∣ N ∧
        ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40} : Set ℕ).ncard : ℝ) := by
  refine lt_of_le_of_lt ?_ (sifted_count_lower_UN_full N hN hX)
  set E := Real.exp (-Real.eulerMascheroniConstant)
  set C := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)
  set F := ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  have hF := UN_extra_factor_ge_one N
  have hE : 0 < E := Real.exp_pos _
  have hC : 0 < C := lt_trans (by norm_num) twin_prime_const_gt_split
  have hNpos : (0 : ℝ) ≤ N := N.cast_nonneg
  have hq : 0 ≤ (N : ℝ) / Real.log N ^ 2 := by positivity
  have hk : 5 * (2 * E * C) ≤ 5 * (2 * E * C * F) := by nlinarith [mul_pos hE hC]
  calc 5 * (2 * E * C) * (N : ℝ) / Real.log N ^ 2 = 5 * (2 * E * C) * ((N : ℝ) / Real.log N ^ 2) := by ring
    _ ≤ 5 * (2 * E * C * F) * ((N : ℝ) / Real.log N ^ 2) := mul_le_mul_of_nonneg_right hk hq
    _ = 5 * (2 * E * C * F) * (N : ℝ) / Real.log N ^ 2 := by ring

example : type_of% @sifted_count_lower_UN_split = type_of% @sifted_count_lower_UN := rfl

end LeanLab.JohnstonStarichkova
