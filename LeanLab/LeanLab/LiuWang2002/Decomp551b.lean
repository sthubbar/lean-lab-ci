import Mathlib

/-!
Proper subrange supplies for the sealed Decomp460c leaves.
Source Schoenfeld 1976 page 356, display 5.1 star, derived integer certificates.
The cutoffs are proof bookkeeping and are not printed paper constants.
All leaf dependent assemblies are CONDITIONAL ON the named open subranges.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task551

/-- LEAF. Schoenfeld page 356, display 5.1 star, derived integer
certificate strictly above 32000000 through 49000000. This is a proper
subrange of Task460.primorial_c6_lower. No analytic input is assumed. -/
theorem primorial_c6_lower_first (n : ℕ) (hn : 32000000 < n) (hn' : n ≤ 49000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Schoenfeld page 356, display 5.1 star, derived integer
certificate strictly above 49000000 through 66000000. This is a proper
subrange of Task460.primorial_c6_lower. No analytic input is assumed. -/
theorem primorial_c6_lower_second (n : ℕ) (hn : 49000000 < n) (hn' : n ≤ 66000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- Each new subrange has a concrete integer witness. The midpoint
belongs only to the first subrange. Derived domains for Schoenfeld
page 356, display 5.1 star. -/
theorem primorial_c6_lower_domains :
    (32000000 < (32000001 : ℕ) ∧ 32000001 ≤ 49000000) ∧
    (49000000 < (49000001 : ℕ) ∧ 49000001 ≤ 66000000) ∧
    (32000000 < (49000000 : ℕ) ∧ 49000000 ≤ 49000000) ∧ ¬ 49000000 < (49000000 : ℕ) := by
  norm_num

/-- Exact supply for Task460.primorial_c6_lower. CONDITIONAL ON
primorial_c6_lower_first and primorial_c6_lower_second.
Source Schoenfeld page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c6_lower (n : ℕ) (hn : 32000000 < n) (hn' : n ≤ 66000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 49000000
  · exact primorial_c6_lower_first n hn hm
  · exact primorial_c6_lower_second n (by omega) hn'

end LeanLab.LiuWang2002.Task551
#print axioms LeanLab.LiuWang2002.Task551.primorial_c6_lower_first
#print axioms LeanLab.LiuWang2002.Task551.primorial_c6_lower_second
#print axioms LeanLab.LiuWang2002.Task551.primorial_c6_lower_domains
#print axioms LeanLab.LiuWang2002.Task551.primorial_c6_lower
