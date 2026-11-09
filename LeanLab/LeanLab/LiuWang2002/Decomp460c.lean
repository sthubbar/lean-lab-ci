import LeanLab.LiuWang2002.Decomp368b

/-!
Strictly smaller subranges of the remaining primorial certificates.
Source Schoenfeld page 356, display 5.1 star, derived integer bounds.
The assemblies are CONDITIONAL ON their named open subranges.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task460

/-- LEAF. Page 356, display 5.1 star, derived integer certificate
strictly above 16000000 through 24000000. This is a proper subrange. -/
theorem primorial_c5_lower (n : ℕ) (hn : 16000000 < n) (hn' : n ≤ 24000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Page 356, display 5.1 star, derived integer certificate
strictly above 24000000 through 32000000. This is a proper subrange. -/
theorem primorial_c5_upper (n : ℕ) (hn : 24000000 < n) (hn' : n ≤ 32000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- Exact supply for Task368.primorial_c5. CONDITIONAL ON the two
proper subranges. Source page 356, display 5.1 star. -/
theorem primorial_c5 (n : ℕ) (hn : 16000000 < n) (hn' : n ≤ 32000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 24000000
  · exact primorial_c5_lower n hn hm
  · exact primorial_c5_upper n (by omega) hn'

/-- LEAF. Page 356, display 5.1 star, derived integer certificate
strictly above 32000000 through 66000000. This is a proper subrange. -/
theorem primorial_c6_lower (n : ℕ) (hn : 32000000 < n) (hn' : n ≤ 66000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Page 356, display 5.1 star, derived integer certificate
strictly above 66000000 through 100000000. This is a proper subrange. -/
theorem primorial_c6_upper (n : ℕ) (hn : 66000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- Exact supply for Task368.primorial_c6. CONDITIONAL ON the two
proper subranges. Source page 356, display 5.1 star. -/
theorem primorial_c6 (n : ℕ) (hn : 32000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 66000000
  · exact primorial_c6_lower n hn hm
  · exact primorial_c6_upper n (by omega) hn'

end LeanLab.LiuWang2002.Task460
#print axioms LeanLab.LiuWang2002.Task460.primorial_c5_lower
#print axioms LeanLab.LiuWang2002.Task460.primorial_c5_upper
#print axioms LeanLab.LiuWang2002.Task460.primorial_c5
#print axioms LeanLab.LiuWang2002.Task460.primorial_c6_lower
#print axioms LeanLab.LiuWang2002.Task460.primorial_c6_upper
#print axioms LeanLab.LiuWang2002.Task460.primorial_c6
