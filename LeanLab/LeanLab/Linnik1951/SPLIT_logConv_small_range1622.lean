/-
Split unit of LeanLab/Linnik1951/SPLIT_log_convolution_estimate1622. This file adds leaves
for the finite range leaf logConv_small_range1622 of that file, plus the assembly theorem
logConv_small_range1622_split. No statement of the parent file is changed; no definition is
added.
AI wrote the Lean code. Binary Goldbach is open.

Route. Write L for log n, A(n) for n / L^2 and W(n) for 1 / sqrt(log n). The range is
2 <= n <= 1000, so the whole claim is elementary: the two constants log 2 and log 1000
control it. Every summand of logConvolution1622 n is at most 1 / (log 2)^2 and at least
1 / L^2, because 2 <= m <= n - 2 puts both log m and log (n - m) between log 2 and L. So the
sum lies between (n - 3) / L^2 and (n - 3) / (log 2)^2, and the index set has n - 3 elements
by Nat.card_Icc. Subtracting A(n) leaves the sum inside
[-3 / L^2, n / (log 2)^2 - A(n)], and the two scale leaves compare those two numbers with
500 * A(n) * W(n) using log n <= 7 and log 2 >= 0.69 over the finite range. n equal to 2 and
n equal to 3 have an empty index set and are carried by one leaf with the same constant 500.
-/
import LeanLab.Linnik1951.SPLIT_log_convolution_estimate1622

namespace LeanLab.Linnik1951

/-- LEAF. The empty end of the range: for 2 <= n <= 3 the index set 2 <= m <= n - 2 is empty,
so the convolution is zero and the claim holds with constant 500. This is the step that keeps
n equal to 2 and n equal to 3 out of the index count n - 3, which needs n at least 4. -/
theorem logConv_small_initial1622 (n : ℕ) (hn : 2 ≤ n) (hn3 : n ≤ 3) :
    |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
      500 * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  sorry

/-- LEAF. Termwise upper bound: for an index m of the convolution sum,
1 / (log m * log (n - m)) is at most 1 / (log 2)^2, because the two indices are at least 2 and
give both logarithms at least log 2 while their product stays positive. This is the step that
turns the index count into an upper bound for the whole sum. -/
theorem logConv_small_term_upper1622 (n m : ℕ) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) ≤ 1 / Real.log 2 ^ 2 := by
  sorry

/-- LEAF. Termwise lower bound: for 2 <= n and an index m of the convolution sum,
1 / (log m * log (n - m)) is at least 1 / (log n)^2, because both indices are at most n and
make both logarithms positive and at most log n. This is the step that turns the index count
into a lower bound for the whole sum. -/
theorem logConv_small_term_lower1622 (n : ℕ) (hn : 2 ≤ n) (m : ℕ)
    (hm : m ∈ Finset.Icc 2 (n - 2)) :
    1 / Real.log (n : ℝ) ^ 2 ≤ 1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
  sorry

/-- LEAF. Scale comparison, upper side: for 4 <= n <= 1000 the crude upper bound n / (log 2)^2
of the convolution overshoots the main term n / (log n)^2 by at most 500 times the main term
times 1 / sqrt (log n). Only the two constants log n <= 7 and log 2 >= 0.69 are used, and no
property of the convolution. -/
theorem logConv_small_scale_upper1622 (n : ℕ) (hn : 4 ≤ n) (hn1000 : n ≤ 1000) :
    (n : ℝ) * (1 / Real.log 2 ^ 2) - (n : ℝ) / Real.log n ^ 2 ≤
      500 * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  sorry

/-- LEAF. Scale comparison, lower side: for 4 <= n <= 1000 the loss 3 / (log n)^2 by which the
index count n - 3 falls short of n is at most 500 times the main term times
1 / sqrt (log n). This is the step that closes the absolute value from below, and it uses no
property of the convolution. -/
theorem logConv_small_scale_lower1622 (n : ℕ) (hn : 4 ≤ n) (hn1000 : n ≤ 1000) :
    -(500 * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n))) ≤
      -(3 / Real.log n ^ 2) := by
  sorry

/-- The target statement of the parent file, assembled from the five leaves above with no
remaining gap: constant 500, the empty end 2 <= n <= 3, and for 4 <= n <= 1000 the sum
sandwiched between (n - 3) / (log n)^2 and (n - 3) / (log 2)^2, which the two scale leaves
compare with 500 times the main term times 1 / sqrt (log n). -/
theorem logConv_small_range1622_split :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → n ≤ 1000 →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  refine ⟨500, by norm_num, ?_⟩
  intro n hn hn1000
  rcases lt_or_ge 3 n with h3lt | hn3
  · have hn4 : 4 ≤ n := by omega
    have hcpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hc2 : 0 < 1 / Real.log 2 ^ 2 :=
      div_pos one_pos (pow_pos hcpos 2)
    have hcard : ((Finset.Icc 2 (n - 2)).card : ℝ) = (n : ℝ) - 3 := by
      have h1 : (Finset.Icc 2 (n - 2)).card = n - 3 := by
        rw [Nat.card_Icc]
        omega
      rw [h1, Nat.cast_sub (show 3 ≤ n by omega)]
      norm_num
    have hupper_sum : logConvolution1622 n ≤
        (n : ℝ) * (1 / Real.log 2 ^ 2) := by
      have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
          1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) ≤ 1 / Real.log 2 ^ 2 :=
        fun m hm => logConv_small_term_upper1622 n m hm
      have h := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at h
      have hcast : ((Finset.Icc 2 (n - 2)).card : ℝ) ≤ (n : ℝ) := by
        rw [hcard]
        have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
        linarith
      have hstep := mul_le_mul_of_nonneg_right hcast (le_of_lt hc2)
      have hfold : logConvolution1622 n ≤
          ((Finset.Icc 2 (n - 2)).card : ℝ) * (1 / Real.log 2 ^ 2) := by
        simpa [logConvolution1622] using h
      linarith [hfold, hstep]
    have hlower_sum : ((n : ℝ) - 3) * (1 / Real.log (n : ℝ) ^ 2) ≤
        logConvolution1622 n := by
      have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
          1 / Real.log (n : ℝ) ^ 2 ≤
            1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) :=
        fun m hm => logConv_small_term_lower1622 n hn m hm
      have h := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at h
      rw [hcard] at h
      simpa [logConvolution1622] using h
    have hkey : ((n : ℝ) - 3) * (1 / Real.log (n : ℝ) ^ 2) =
        (n : ℝ) / Real.log (n : ℝ) ^ 2 - 3 / Real.log (n : ℝ) ^ 2 := by
      ring
    have hylow : -(3 / Real.log (n : ℝ) ^ 2) ≤
        logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
      linarith [hlower_sum, hkey]
    have hyhigh : logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤
        500 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
          (1 / Real.sqrt (Real.log (n : ℝ))) := by
      have hscale := logConv_small_scale_upper1622 n hn4 hn1000
      linarith [hupper_sum, hscale]
    have hlow := logConv_small_scale_lower1622 n hn4 hn1000
    rw [abs_le]
    constructor
    · linarith [hylow, hlow]
    · linarith [hyhigh]
  · exact logConv_small_initial1622 n hn hn3

end LeanLab.Linnik1951
