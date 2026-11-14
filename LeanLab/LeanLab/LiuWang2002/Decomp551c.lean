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
certificate strictly above 66000000 through 83000000. This is a proper
subrange of Task460.primorial_c6_upper. No analytic input is assumed. -/
theorem primorial_c6_upper_first (n : ℕ) (hn : 66000000 < n) (hn' : n ≤ 83000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Schoenfeld page 356, display 5.1 star, derived integer
certificate strictly above 83000000 through 100000000. This is a proper
subrange of Task460.primorial_c6_upper. No analytic input is assumed. -/
theorem primorial_c6_upper_second (n : ℕ) (hn : 83000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- Each new subrange has a concrete integer witness. The midpoint
belongs only to the first subrange. Derived domains for Schoenfeld
page 356, display 5.1 star. -/
theorem primorial_c6_upper_domains :
    (66000000 < (66000001 : ℕ) ∧ 66000001 ≤ 83000000) ∧
    (83000000 < (83000001 : ℕ) ∧ 83000001 ≤ 100000000) ∧
    (66000000 < (83000000 : ℕ) ∧ 83000000 ≤ 83000000) ∧ ¬ 83000000 < (83000000 : ℕ) := by
  norm_num

/-- Exact supply for Task460.primorial_c6_upper. CONDITIONAL ON
primorial_c6_upper_first and primorial_c6_upper_second.
Source Schoenfeld page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c6_upper (n : ℕ) (hn : 66000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 83000000
  · exact primorial_c6_upper_first n hn hm
  · exact primorial_c6_upper_second n (by omega) hn'

end LeanLab.LiuWang2002.Task551
#print axioms LeanLab.LiuWang2002.Task551.primorial_c6_upper_first
#print axioms LeanLab.LiuWang2002.Task551.primorial_c6_upper_second
#print axioms LeanLab.LiuWang2002.Task551.primorial_c6_upper_domains
#print axioms LeanLab.LiuWang2002.Task551.primorial_c6_upper
