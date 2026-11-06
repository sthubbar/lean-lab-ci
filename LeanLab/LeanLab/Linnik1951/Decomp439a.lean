/-
P0093 page 168 equations 10.5 and 10.6. Clean supplies for the sealed split.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Rate439
import LeanLab.Linnik1951.Reciprocal439
import LeanLab.Linnik1951.Decomp376a

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 168 equations 10.5 and 10.6. Exact sealed
prime_product_series_tail357 statement. Smooth Euler sums and the absolute
coefficient tail give the uniform rate without any uniform bound on the full product. -/
theorem prime_product_series_tail_proved439 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |(∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
            (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) -
          (∑' q : ℕ, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  obtain ⟨C, hC, hc⟩ := absolute_tail_uniform_scale439
  refine ⟨C, hC, 0, ?_⟩
  intro N hN n hn hnN hev
  have hN1 : 1 ≤ N := by omega
  have hQ : 1 ≤ ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ := Nat.floor_pos.mpr
    (Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num))
  simp_rw [ramanujan_weight_eq_gm439 n _ (by omega)]
  exact (finite_product_absolute_error439 n _ (by omega) hQ).trans
    (hc N hN1 n (by omega) hnN)

/-- P0093 page 168 equations 10.5 and 10.6. Exact sealed
truncated_sum_euler_error357 statement. Insert the complete series between
the modulus cutoff and the prime cutoff. Both error estimates are proved. -/
theorem truncated_sum_euler_error_proved439 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n -
          (∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
            (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2))| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  obtain ⟨C1, hC1, N1, h1⟩ := singular_tail_decomposed376
  obtain ⟨C2, hC2, N2, h2⟩ := prime_product_series_tail_proved439
  refine ⟨C1 + C2, by positivity, max N1 N2, ?_⟩
  intro N hN n hn hnN hev
  have hb1 := h1 N (lt_of_le_of_lt (le_max_left _ _) hN) n hn hnN hev
  have hb2 := h2 N (lt_of_le_of_lt (le_max_right _ _) hN) n hn hnN hev
  rw [(singular_series_has_sum_proved439 n hn).tsum_eq, abs_sub_comm] at hb2
  exact (abs_sub_le (truncatedSingular357 N n) (singularSeries111 n) _).trans
    (by simpa only [add_mul] using add_le_add hb1 hb2)

end LeanLab.Linnik1951
