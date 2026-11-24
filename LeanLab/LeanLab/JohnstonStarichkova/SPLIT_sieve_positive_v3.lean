/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, pages 3 to 4 and 13.
SPLIT of sieve_positive_v3 from SPLIT_sieveRange_of_thm42.lean, ROUTE BURST S98 burst-20261122.
Page 3: A = {N - p : p ≤ N, p ∤ N}, P(z) = product of primes p < z with p ∤ N, and
U_N = 2 e^(-γ) prod_{p>2} (1 - 1/(p-1)^2) prod_{p>2, p | N} (p-1)/(p-2).
An element N - p of A coprime to P(z) has no prime factor q < z at all: q | N would
force q | p, so q = p, contradicting p ∤ N. Hence S(A, P(z)) is the count used below.
Page 13 displays S(A, P(z)) > 38 U_N N / log^2 N or > 5 U_N N / log^2 N, so in both
cases S > 5 U_N N / log^2 N, and U_N ≥ 2 e^(-γ) C_2 = 2 * 0.561459 * 0.660161 > 0.7413,
so 5 U_N > 3.7. The reduction from the count to the parent statement is proved here.
AI wrote this Lean code.
-/
import LeanLab.JohnstonStarichkova.SPLIT_sieveRange_of_thm42

namespace LeanLab.JohnstonStarichkova
open LeanLab.AlmostPrimes

/-
Numerics: at N = exp(exp 7.9), log N = exp 7.9 ≈ 2697.3, so the bound
3.7 N / log^2 N ≈ 5.1e-7 N is astronomically large and positive. The constant
3.7 comes from 5 * 0.7413 = 3.7065, with C_2 = 0.6601618 and e^(-γ) = 0.5614594.
-/
/-- LEAF: P0019 v3 page 13, proof of Theorem 1.3: Theorem 4.2 with (4.6) and
u0 = 400, δ = 1.3, α = 0.25, M = 40 gives S(A, P(z)) > 5 U_N N / log^2 N in both
cases k1 < Kδ(x1) and k1 ≥ Kδ(x1), z = N^(1/40), every even N ≥ exp(exp 7.9); with
U_N > 0.7413 this is the count of primes p < N, p ∤ N, all prime factors q of N - p
having q ≥ z, exceeding 3.7 N / log^2 N. Class HARD. -/
theorem sifted_count_lower_v3 (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    3.7 * (N : ℝ) / Real.log N ^ 2 <
      (({p : ℕ | p.Prime ∧ p < N ∧ ¬ p ∣ N ∧
        ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40} : Set ℕ).ncard : ℝ) := by
  sorry

theorem sieve_positive_v3_split (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    ∃ p : ℕ, p.Prime ∧ p < N ∧ ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40 := by
  have h := sifted_count_lower_v3 N hN hX
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hX
  have hpos : 0 ≤ 3.7 * (N : ℝ) / Real.log N ^ 2 := by positivity
  have hne : ({p : ℕ | p.Prime ∧ p < N ∧ ¬ p ∣ N ∧
        ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40} : Set ℕ).ncard ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
    linarith
  obtain ⟨p, hp⟩ := Set.nonempty_of_ncard_ne_zero hne
  exact ⟨p, hp.1, hp.2.1, hp.2.2.2⟩

end LeanLab.JohnstonStarichkova
