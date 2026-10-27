import LeanLab.RieselVaughan1983.Stieltjes1LogBounds

/-!
Fixed denominator rounding for the enclosure of equation 2.2 on page 46.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.StieltjesCert

open Finset

/-- Round the logarithm down before division, then round its summand down. -/
def lowerTerm (m : ℕ) : ℤ :=
  ⌊(⌊logLower m * 1000000000⌋ : ℚ) / m⌋

/-- Round the logarithm up before division, then round its summand up. -/
def upperTerm (m : ℕ) : ℤ :=
  ⌈(⌈logUpper m * 1000000000⌉ : ℚ) / m⌉

def lowerSum (a b : ℕ) : ℤ := ∑ m ∈ Ico a b, lowerTerm m

def upperSum (a b : ℕ) : ℤ := ∑ m ∈ Ico a b, upperTerm m

lemma rounded_log_bounds (m : ℕ) (hm : 1 ≤ m) :
    (⌊logLower m * 1000000000⌋ : ℝ) / 1000000000 ≤ Real.log m ∧
      Real.log m ≤ (⌈logUpper m * 1000000000⌉ : ℝ) / 1000000000 := by
  obtain ⟨hl, hu⟩ := log_bounds m hm
  have hlf : (⌊logLower m * 1000000000⌋ : ℚ) ≤ logLower m * 1000000000 :=
    Int.floor_le _
  have huc : logUpper m * 1000000000 ≤ (⌈logUpper m * 1000000000⌉ : ℚ) :=
    Int.le_ceil _
  have hlf' : (⌊logLower m * 1000000000⌋ : ℝ) ≤ (logLower m : ℝ) * 1000000000 := by
    exact_mod_cast hlf
  have huc' : (logUpper m : ℝ) * 1000000000 ≤ (⌈logUpper m * 1000000000⌉ : ℝ) := by
    exact_mod_cast huc
  constructor <;> linarith

lemma rounded_term_bounds (m : ℕ) (hm : 1 ≤ m) :
    (lowerTerm m : ℝ) / 1000000000 ≤ Real.log m / m ∧
      Real.log m / m ≤ (upperTerm m : ℝ) / 1000000000 := by
  obtain ⟨hl, hu⟩ := rounded_log_bounds m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlf : (lowerTerm m : ℚ) ≤ (⌊logLower m * 1000000000⌋ : ℚ) / m :=
    Int.floor_le _
  have huc : (⌈logUpper m * 1000000000⌉ : ℚ) / m ≤ (upperTerm m : ℚ) :=
    Int.le_ceil _
  have hlf' : (lowerTerm m : ℝ) ≤ (⌊logLower m * 1000000000⌋ : ℝ) / m := by
    exact_mod_cast hlf
  have huc' : (⌈logUpper m * 1000000000⌉ : ℝ) / m ≤ (upperTerm m : ℝ) := by
    exact_mod_cast huc
  constructor
  · calc (lowerTerm m : ℝ) / 1000000000 ≤
          ((⌊logLower m * 1000000000⌋ : ℝ) / m) / 1000000000 := by gcongr
      _ = ((⌊logLower m * 1000000000⌋ : ℝ) / 1000000000) / m := by ring
      _ ≤ Real.log m / m := div_le_div_of_nonneg_right hl hm0.le
  · calc Real.log m / m ≤
          ((⌈logUpper m * 1000000000⌉ : ℝ) / 1000000000) / m :=
            div_le_div_of_nonneg_right hu hm0.le
      _ = ((⌈logUpper m * 1000000000⌉ : ℝ) / m) / 1000000000 := by ring
      _ ≤ (upperTerm m : ℝ) / 1000000000 := by gcongr

lemma rounded_sum_bounds (n : ℕ) :
    (lowerSum 1 (n + 1) : ℝ) / 1000000000 ≤
        ∑ m ∈ Icc 1 n, Real.log m / m ∧
      (∑ m ∈ Icc 1 n, Real.log m / m) ≤
        (upperSum 1 (n + 1) : ℝ) / 1000000000 := by
  have he : Ico 1 (n + 1) = Icc 1 n := by ext m; simp
  simp only [lowerSum, upperSum, Int.cast_sum, sum_div, he]
  constructor
  · exact sum_le_sum fun m hm => (rounded_term_bounds m (mem_Icc.mp hm).1).1
  · exact sum_le_sum fun m hm => (rounded_term_bounds m (mem_Icc.mp hm).1).2

lemma lowerSum_split (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    lowerSum a c = lowerSum a b + lowerSum b c := by
  exact (sum_Ico_consecutive lowerTerm hab hbc).symm

lemma upperSum_split (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    upperSum a c = upperSum a b + upperSum b c := by
  exact (sum_Ico_consecutive upperTerm hab hbc).symm

end LeanLab.RieselVaughan1983.StieltjesCert

#print axioms LeanLab.RieselVaughan1983.StieltjesCert.rounded_log_bounds
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.rounded_term_bounds
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.rounded_sum_bounds
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.lowerSum_split
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.upperSum_split
