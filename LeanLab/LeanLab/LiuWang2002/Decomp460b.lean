import LeanLab.LiuWang2002.Decomp368b

/-!
Strictly smaller subranges of the remaining primorial certificates.
Source Schoenfeld page 356, display 5.1 star, derived integer bounds.
The assemblies are CONDITIONAL ON their named open subranges.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task460

/-- LEAF. Page 356, display 5.1 star, derived integer certificate
strictly above 4000000 through 6000000. This is a proper subrange. -/
theorem primorial_c3_lower (n : ℕ) (hn : 4000000 < n) (hn' : n ≤ 6000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Page 356, display 5.1 star, derived integer certificate
strictly above 6000000 through 8000000. This is a proper subrange. -/
theorem primorial_c3_upper (n : ℕ) (hn : 6000000 < n) (hn' : n ≤ 8000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- Exact supply for Task368.primorial_c3. CONDITIONAL ON the two
proper subranges. Source page 356, display 5.1 star. -/
theorem primorial_c3 (n : ℕ) (hn : 4000000 < n) (hn' : n ≤ 8000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 6000000
  · exact primorial_c3_lower n hn hm
  · exact primorial_c3_upper n (by omega) hn'

/-- LEAF. Page 356, display 5.1 star, derived integer certificate
strictly above 8000000 through 12000000. This is a proper subrange. -/
theorem primorial_c4_lower (n : ℕ) (hn : 8000000 < n) (hn' : n ≤ 12000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Page 356, display 5.1 star, derived integer certificate
strictly above 12000000 through 16000000. This is a proper subrange. -/
theorem primorial_c4_upper (n : ℕ) (hn : 12000000 < n) (hn' : n ≤ 16000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- Exact supply for Task368.primorial_c4. CONDITIONAL ON the two
proper subranges. Source page 356, display 5.1 star. -/
theorem primorial_c4 (n : ℕ) (hn : 8000000 < n) (hn' : n ≤ 16000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 12000000
  · exact primorial_c4_lower n hn hm
  · exact primorial_c4_upper n (by omega) hn'

end LeanLab.LiuWang2002.Task460
#print axioms LeanLab.LiuWang2002.Task460.primorial_c3_lower
#print axioms LeanLab.LiuWang2002.Task460.primorial_c3_upper
#print axioms LeanLab.LiuWang2002.Task460.primorial_c3
#print axioms LeanLab.LiuWang2002.Task460.primorial_c4_lower
#print axioms LeanLab.LiuWang2002.Task460.primorial_c4_upper
#print axioms LeanLab.LiuWang2002.Task460.primorial_c4
