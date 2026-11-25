/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, pages 3, 4 and 13.
Wiring, burst-20261122 session S153, second step. With the constants PROVED and the U_N step PROVED,
sieve_positive_v3, the page 13 sieve positivity for even N at least exp(exp 7.9), is reduced to the
single cited LEAF sifted_count_lower_UN_full, the page 13 Theorem 4.2 bound.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.JohnstonStarichkova.WiringS153
import LeanLab.JohnstonStarichkova.SPLIT_sifted_count_lower_UN

namespace LeanLab.JohnstonStarichkova
open LeanLab.AlmostPrimes

/-- P0019 v3 page 13: S(A, P(z)) > 3.7 N / log^2 N. CONDITIONAL ON sifted_count_lower_UN_full. -/
theorem sifted_count_lower_v3_wired2 (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    3.7 * (N : ℝ) / Real.log N ^ 2 <
      (({p : ℕ | p.Prime ∧ p < N ∧ ¬ p ∣ N ∧
        ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40} : Set ℕ).ncard : ℝ) := by
  refine lt_trans ?_ (sifted_count_lower_UN_split N hN hX)
  have he := exp_neg_euler_gt_split
  have hc := twin_prime_const_gt_split
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


/-- P0019 v3 page 13: the sieve positivity, exact statement of sieve_positive_v3.
CONDITIONAL ON sifted_count_lower_UN_full alone. -/
theorem sieve_positive_v3_wired (N : ℕ) (hN : Even N) (hX : Real.exp (Real.exp 7.9) ≤ N) :
    ∃ p : ℕ, p.Prime ∧ p < N ∧ ∀ q : ℕ, q.Prime → q ∣ N - p → N ≤ q ^ 40 := by
  have h := sifted_count_lower_v3_wired2 N hN hX
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

example : type_of% @sieve_positive_v3_wired = type_of% @sieve_positive_v3 := rfl

end LeanLab.JohnstonStarichkova
