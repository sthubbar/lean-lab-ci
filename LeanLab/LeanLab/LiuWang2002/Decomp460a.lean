import LeanLab.LiuWang2002.CheckData460_18

/-!
Exact supply for the second proper primorial range.
Source Schoenfeld page 356, display 5.1 star, derived integer certificates.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task460

/-- The completed proper prefix of the c2 range. Derived integer
certificate for page 356, display 5.1 star. -/
theorem primorial_c2_prefix (n : ℕ) (hn : 2000000 < n) (hn' : n ≤ 2311296) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact range460_18 n hn hn'

/-- LEAF. Page 356, display 5.1 star, derived integer certificate
strictly above 2311296 through 4000000. This is a proper subrange. -/
theorem primorial_c2_tail (n : ℕ) (hn : 2311296 < n) (hn' : n ≤ 4000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- Exact supply for Task368.primorial_c2. CONDITIONAL ON primorial_c2_tail.
Source page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c2 (n : ℕ) (hn : 2000000 < n) (hn' : n ≤ 4000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hp : n ≤ 2311296
  · exact primorial_c2_prefix n hn hp
  · exact primorial_c2_tail n (by omega) hn'

end LeanLab.LiuWang2002.Task460
#print axioms LeanLab.LiuWang2002.Task460.primorial_c2_prefix
#print axioms LeanLab.LiuWang2002.Task460.primorial_c2_tail
#print axioms LeanLab.LiuWang2002.Task460.primorial_c2
