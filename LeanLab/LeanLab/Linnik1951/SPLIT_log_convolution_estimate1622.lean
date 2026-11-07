/-
Split unit of U-1622. This file adds leaves for the elementary convolution estimate
log_convolution_estimate1622 of Linnik1951/SPLIT1622_major.lean, plus the assembly
theorem log_convolution_estimate1622_split. No statement of the parent file is
changed; no definition is added.
AI wrote the Lean code. Binary Goldbach is open.

Route. Write A(n) for n / (log n)^2 and L(n) for the convolution
logConvolution1622 n, a sum over 2 <= m <= n-2. For n at most 10^3 the claim is a
finite range statement, carried by one leaf. For n at least 10^3 the sum dominates
A(n) and exceeds it only by O(n / (log n)^3), which is A(n) times 1/log n. There
log n is at least one, so 1/log n is at most 1/sqrt(log n), which is the relative
weight of the target. The two ranges cover every n at least 2 and give one pair of
constants.
-/
import LeanLab.Linnik1951.SPLIT1622_major

namespace LeanLab.Linnik1951

/-- LEAF. Well-definedness of the summand: every index of the convolution sum has
both logarithms positive, so the summand is defined and no factor vanishes. This is
the step that lets the two one-sided leaves divide by log m and log (n - m). -/
theorem logConv_denominator_pos1622 (n m : ℕ) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    0 < Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) := by
  sorry

/-- LEAF. Scale control, main term is dominated: from n equal to 4 upwards the
convolution sum is at least n / (log n)^2. The sum has about n terms each of size
about 1 / (log n)^2, and this leaf asserts only the one-sided floor, with no error
term. It is the step that removes the absolute value in the large range. -/
theorem logConv_main_le1622 (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) / Real.log n ^ 2 ≤ logConvolution1622 n := by
  sorry

/-- LEAF. Scale control, second order excess: from n equal to 10^3 upwards the
excess of the convolution over n / (log n)^2 is bounded by a constant times
n / (log n)^3, that is by the main term times 1 / log n. One-sided only, and no
absolute value. -/
theorem logConv_excess1622 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1000 ≤ n →
      logConvolution1622 n - (n : ℝ) / Real.log n ^ 2 ≤
        C * ((n : ℝ) / Real.log n ^ 3) := by
  sorry

/-- LEAF. The finite range: for 2 <= n <= 10^3 the whole claim of the target holds
with one constant, in absolute value and with the relative weight 1/sqrt(log n).
Finitely many cases and no asymptotic content. -/
theorem logConv_small_range1622 :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → n ≤ 1000 →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  sorry

/-- LEAF. The power identity that turns the excess into the relative weight:
n / (log n)^3 is n / (log n)^2 times 1 / log n, for every n at least 2, where the
logarithm does not vanish. -/
theorem logConv_log_cube_split1622 (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) / Real.log n ^ 3 = ((n : ℝ) / Real.log n ^ 2) * (1 / Real.log n) := by
  sorry

/-- LEAF. The logarithmic weight comparison: for n at least 10^3 the logarithm is at
least one, so 1 / log n is at most 1 / sqrt(log n). This is what converts the
second order excess into the exact weight of the target. -/
theorem logConv_recip_log_le_sqrt1622 (n : ℕ) (hn : 1000 ≤ n) :
    1 / Real.log n ≤ 1 / Real.sqrt (Real.log n) := by
  sorry

/-- The target statement of the parent file, assembled from the leaves above with no
remaining gap: one constant covering the finite range 2 <= n <= 10^3 and the half
line 10^3 <= n. -/
theorem log_convolution_estimate1622_split :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤ B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  obtain ⟨C, hCpos, hC⟩ := logConv_excess1622
  obtain ⟨B1, hB1pos, hB1⟩ := logConv_small_range1622
  refine ⟨max B1 C, lt_of_lt_of_le hB1pos (le_max_left B1 C), ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hsqrtpos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlogpos
  have hA : 0 ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 :=
    div_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  have hS : 0 ≤ 1 / Real.sqrt (Real.log (n : ℝ)) :=
    div_nonneg zero_le_one hsqrtpos.le
  have hX : 0 ≤ ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) :=
    mul_nonneg hA hS
  rcases le_total n 1000 with hsmall | hlarge
  · have h := hB1 n hn hsmall
    calc
      |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
          ≤ B1 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := h
      _ ≤ max B1 C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ hS
            exact mul_le_mul_of_nonneg_right (le_max_left B1 C) hA
  · have h1000 : 1000 ≤ n := hlarge
    have h4 : 4 ≤ n := by omega
    have hmain : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ logConvolution1622 n :=
      logConv_main_le1622 n h4
    have hexc : logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤
        C * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hC n h1000
    have habs : |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
        = logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 :=
      abs_of_nonneg (by linarith)
    have hid : (n : ℝ) / Real.log (n : ℝ) ^ 3 =
        ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.log (n : ℝ)) :=
      logConv_log_cube_split1622 n hn
    have hrec : 1 / Real.log (n : ℝ) ≤ 1 / Real.sqrt (Real.log (n : ℝ)) :=
      logConv_recip_log_le_sqrt1622 n h1000
    calc
      |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
          = logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 := habs
      _ ≤ C * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hexc
      _ = C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.log (n : ℝ))) := by
            rw [hid]
      _ ≤ C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCpos.le
            exact mul_le_mul_of_nonneg_left hrec hA
      _ ≤ max B1 C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_right ?_ hX
            exact le_max_right B1 C
      _ = max B1 C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by ring

end LeanLab.Linnik1951
