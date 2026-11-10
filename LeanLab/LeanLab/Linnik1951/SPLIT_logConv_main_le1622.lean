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
  exact logConv_main_le1622 n hn

/-- LEAF. Termwise lower bound: for 4 <= n and 2 <= m <= n - 2 the summand
1 / (log m * log (n - m)) is at least 1 / (log n)^2, since the two indices put both logarithms
positive and both at most log n. This is the step that turns a count of the index set into a
lower bound for the whole sum. -/
theorem logConv_main_term_lower1622 (n m : ℕ) (hn : 4 ≤ n) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    1 / Real.log (n : ℝ) ^ 2 ≤ 1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
  have hm1 : 2 ≤ m := by exact (Finset.mem_Icc.mp hm).1
  have hm2 : m ≤ n - 2 := by exact (Finset.mem_Icc.mp hm).2
  have H1 : 2 ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm1
  have H2 : 2 ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - m by omega)
  have H3 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show m ≤ n by omega)
  have H4 : ((n - m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show n - m ≤ n by omega)
  have H1_pos : 0 < (m : ℝ) := by linarith
  have H2_pos : 0 < ((n - m : ℕ) : ℝ) := by linarith
  have H5 : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by apply Real.log_le_log H1_pos H3
  have H6 : Real.log ((n - m : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by apply Real.log_le_log H2_pos H4
  have H7 : 0 < Real.log (m : ℝ) := by apply Real.log_pos; linarith
  have H8 : 0 < Real.log ((n - m : ℕ) : ℝ) := by apply Real.log_pos; linarith
  have H9 : Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  have H10 : 0 < Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) := by positivity
  exact one_div_le_one_div_of_le H10 H9

/-- LEAF. Endpoint surplus: for n at least 16 the logarithm of n is at least 4 log 2, so the
single summand at m = 2, namely 1 / (log 2 * log (n - 2)), is at least 4 / (log n)^2. This is
the step that pays the three units of 1 / (log n)^2 by which the index count falls short of n. -/
theorem logConv_main_endpoint1622 (n : ℕ) (hn : 16 ≤ n) :
    4 / Real.log (n : ℝ) ^ 2 ≤ 1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) := by
  have h1 : 2 ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 2 by omega)
  have h2 : ((n - 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show n - 2 ≤ n by omega)
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h1_pos : 0 < ((n - 2 : ℕ) : ℝ) := by linarith
  have H1 : Real.log ((n - 2 : ℕ) : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log h1_pos h2
  have H2 : 4 * Real.log 2 ≤ Real.log (n : ℝ) := by
    calc
      4 * Real.log 2 = (4:ℝ) * Real.log 2 := by norm_cast
      _ = Real.log (2 ^ (4:ℝ)) := by
        exact (Real.log_rpow (show (0:ℝ) < 2 by norm_num) (4:ℝ)).symm
      _ = Real.log 16 := by norm_num
      _ ≤ Real.log (n : ℝ) := by
        apply Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have H3 : 0 < Real.log 2 := by apply Real.log_pos; norm_num
  have H4 : 0 < Real.log ((n - 2 : ℕ) : ℝ) := by apply Real.log_pos; linarith
  have H5 : Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ) ≤ (Real.log (n : ℝ) / 4) * Real.log (n : ℝ) := by
    nlinarith
  have H6 : (Real.log (n : ℝ) / 4) * Real.log (n : ℝ) = Real.log (n : ℝ) ^ 2 / 4 := by ring
  have H7 : Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ) ≤ Real.log (n : ℝ) ^ 2 / 4 := by linarith
  have H8 : 0 < Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ) := by positivity
  have H9 := one_div_le_one_div_of_le H8 H7
  calc
    4 / Real.log (n : ℝ) ^ 2 = 1 / (Real.log (n : ℝ) ^ 2 / 4) := by ring
    _ ≤ 1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) := H9

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
