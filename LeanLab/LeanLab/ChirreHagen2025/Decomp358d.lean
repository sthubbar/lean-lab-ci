import LeanLab.ChirreHagen2025.Decomp391b
import LeanLab.ChirreHagen2025.Decomp272c

/-!
P0075 page 3 first bound after equation 2.1.
Johnston, Ramare and Trudgian 2023 Lemma 10 pages 3 to 4.
https://arxiv.org/abs/2303.13785
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp358d
open ArithmeticFunction

/-- LEAF. Johnston, Ramare and Trudgian 2023 page 4 proof of Lemma 10.
The extension below ten to the fifth is a finite computation. P0075 page 3
needs only integer endpoints at least 73. No complex estimate occurs here. -/
theorem mangoldt_small_range (m : ℕ) (hm : 73 ≤ m) (hmtop : m < 100000) :
    (∑ n ∈ Finset.Icc 1 m, vonMangoldt n / (n : ℝ)) ≤
      Real.log (m : ℝ) - Real.eulerMascheroniConstant +
        1.3 / Real.log (m : ℝ) ^ 2 := by
  sorry

/-- LEAF. Johnston, Ramare and Trudgian 2023 page 4 proof of Lemma 10,
first display. Lemma 9 with Lemmas 6 and 7 gives 0.67 above ten to the fifth.
Only the upper half of the source's absolute error estimate is needed. -/
theorem mangoldt_large_range (m : ℕ) (hm : 100000 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m, vonMangoldt n / (n : ℝ)) ≤
      Real.log (m : ℝ) - Real.eulerMascheroniConstant +
        0.67 / Real.log (m : ℝ) ^ 2 := by
  exact Decomp391b.mangoldt_large_range m hm

/-- P0075 page 3 first bound after equation 2.1, the triangle inequality.
This elementary part does not use the cited real Mangoldt estimate. -/
theorem mangoldt_complex_sum_le (s : ℂ) (hs : 1 ≤ s.re) (m : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 m, (vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ ≤
      ∑ n ∈ Finset.Icc 1 m, vonMangoldt n / (n : ℝ) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt_nonneg), ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  apply div_le_div_of_nonneg_left vonMangoldt_nonneg hn0
  simpa using Real.rpow_le_rpow_of_exponent_le hn1 hs

/-- P0075 page 3. Exact target statement from Decomp272c.
CONDITIONAL ON the separate finite and analytic parts of the cited Lemma 10. -/
theorem finite_mangoldt_bound (σ t : ℝ) (hσ : 1 < σ) (hσtop : σ < 2)
    (ht : 100 ≤ |t|) (N : ℕ) (hN : 74 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 (N - 1),
      (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * Complex.I)‖ ≤
      Real.log ((N : ℝ) - 1) - Real.eulerMascheroniConstant +
        1.3 / Real.log ((N : ℝ) - 1) ^ 2 := by
  have heq : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    exact_mod_cast (Nat.cast_sub (show 1 ≤ N by omega) : ((N - 1 : ℕ) : ℝ) = _)
  apply (mangoldt_complex_sum_le ((σ : ℂ) + t * Complex.I)
    (by simpa using hσ.le) (N - 1)).trans
  rw [← heq]
  by_cases hsmall : N - 1 < 100000
  · exact mangoldt_small_range (N - 1) (by omega) hsmall
  · apply (mangoldt_large_range (N - 1) (by omega)).trans
    gcongr
    norm_num

end LeanLab.ChirreHagen2025.Decomp358d
