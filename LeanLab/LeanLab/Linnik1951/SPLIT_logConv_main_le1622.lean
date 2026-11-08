/-
Split unit of LeanLab/Linnik1951/SPLIT_log_convolution_estimate1622. This file adds leaves for
the elementary main term estimate logConv_main_le1622 of that file, plus the assembly theorem
logConv_main_le1622_split. No statement of the parent file is changed; no definition is added.
AI wrote the Lean code. Binary Goldbach is open.

Route. Write A(n) for n / (log n)^2 and L for log n. Every summand of logConvolution1622 n with
2 <= m <= n - 2 is at least 1 / L^2, because 2 <= m <= n - 2 makes both log m and log (n - m)
positive and at most L. The index set 2 <= m <= n - 2 has n - 3 elements, so it carries
(n - 3) / L^2 by itself. For n at least 16 the logarithm of n is at least 4 log 2, so the single
summand at m = 2, namely 1 / (log 2 * log (n - 2)), already covers the three units of 1 / L^2
by which n - 3 falls short of n. The two pieces give n / L^2 = A(n). Below 16 the claim is a
finite range statement and is carried by one leaf.
-/
import LeanLab.Linnik1951.SPLIT_log_convolution_estimate1622

namespace LeanLab.Linnik1951

/-- LEAF. The finite range: for 4 <= n <= 16 the main term estimate holds outright, checked case
by case, with no asymptotic content and no use of the sum beyond its first few summands. This is
the step that covers the n which the termwise argument below does not reach. -/
theorem logConv_main_small_range1622 (n : ℕ) (hn : 4 ≤ n) (hn16 : n ≤ 16) :
    (n : ℝ) / Real.log n ^ 2 ≤ logConvolution1622 n := by
  sorry

/-- LEAF. Termwise lower bound: for 4 <= n and 2 <= m <= n - 2 the summand
1 / (log m * log (n - m)) is at least 1 / (log n)^2, since the two indices put both logarithms
positive and both at most log n. This is the step that turns a count of the index set into a
lower bound for the whole sum. -/
theorem logConv_main_term_lower1622 (n m : ℕ) (hn : 4 ≤ n) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    1 / Real.log (n : ℝ) ^ 2 ≤ 1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
  sorry

/-- LEAF. Endpoint surplus: for n at least 16 the logarithm of n is at least 4 log 2, so the
single summand at m = 2, namely 1 / (log 2 * log (n - 2)), is at least 4 / (log n)^2. This is
the step that pays the three units of 1 / (log n)^2 by which the index count falls short of n. -/
theorem logConv_main_endpoint1622 (n : ℕ) (hn : 16 ≤ n) :
    4 / Real.log (n : ℝ) ^ 2 ≤ 1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) := by
  sorry

/-- The target statement of the parent file, assembled from the three leaves above with no
remaining gap: the finite range 4 <= n <= 16, and the half line 16 <= n where the index count
supplies n - 3 of the n summands and the summand at m = 2 supplies the rest. -/
theorem logConv_main_le1622_split (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) / Real.log n ^ 2 ≤ logConvolution1622 n := by
  rcases le_total n 16 with hn16 | h16
  · exact logConv_main_small_range1622 n hn hn16
  ·
    have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
        (1 : ℝ) / Real.log (n : ℝ) ^ 2 ≤
          1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) :=
      fun m hm => logConv_main_term_lower1622 n m hn hm
    have hnonneg : ∀ m ∈ Finset.Icc 2 (n - 2), 0 ≤
        1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) - 1 / Real.log (n : ℝ) ^ 2 :=
      fun m hm => sub_nonneg.mpr (hterm m hm)
    have hmem : 2 ∈ Finset.Icc 2 (n - 2) := by
      rw [Finset.mem_Icc]
      omega
    have hsingle : 1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) -
          1 / Real.log (n : ℝ) ^ 2 ≤
        ∑ m ∈ Finset.Icc 2 (n - 2),
          (1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) - 1 / Real.log (n : ℝ) ^ 2) :=
      Finset.single_le_sum hnonneg hmem
    have hsum : ∑ m ∈ Finset.Icc 2 (n - 2),
          (1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) - 1 / Real.log (n : ℝ) ^ 2)
        = logConvolution1622 n -
            ((Finset.Icc 2 (n - 2)).card : ℝ) * (1 / Real.log (n : ℝ) ^ 2) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      simp only [logConvolution1622]
    have hcard : ((Finset.Icc 2 (n - 2)).card : ℝ) = (n : ℝ) - 3 := by
      have h1 : (Finset.Icc 2 (n - 2)).card = n - 3 := by
        rw [Nat.card_Icc]
        omega
      rw [h1, Nat.cast_sub (show 3 ≤ n by omega)]
      norm_num
    have hkey : ((n : ℝ) - 3) * (1 / Real.log (n : ℝ) ^ 2)
        = ((n : ℝ) - 4) * (1 / Real.log (n : ℝ) ^ 2) + 1 / Real.log (n : ℝ) ^ 2 := by
      ring
    have hstep : 1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) +
          ((n : ℝ) - 4) * (1 / Real.log (n : ℝ) ^ 2) ≤ logConvolution1622 n := by
      have h := hsingle
      rw [hsum, hcard, hkey] at h
      linarith
    have hend : 4 * (1 / Real.log (n : ℝ) ^ 2) ≤
        1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) := by
      rw [mul_one_div]
      exact logConv_main_endpoint1622 n h16
    calc (n : ℝ) / Real.log (n : ℝ) ^ 2
        = (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) := (mul_one_div _ _).symm
      _ = 4 * (1 / Real.log (n : ℝ) ^ 2) + ((n : ℝ) - 4) * (1 / Real.log (n : ℝ) ^ 2) := by
          ring
      _ ≤ 1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) +
            ((n : ℝ) - 4) * (1 / Real.log (n : ℝ) ^ 2) := by
          linarith
      _ ≤ logConvolution1622 n := hstep

end LeanLab.Linnik1951
