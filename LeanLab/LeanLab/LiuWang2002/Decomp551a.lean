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
certificate strictly above 16000000 through 20000000. This is a proper
subrange of Task460.primorial_c5_lower. No analytic input is assumed. -/
theorem primorial_c5_lower_first (n : ℕ) (hn : 16000000 < n) (hn' : n ≤ 20000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Schoenfeld page 356, display 5.1 star, derived integer
certificate strictly above 20000000 through 24000000. This is a proper
subrange of Task460.primorial_c5_lower. No analytic input is assumed. -/
theorem primorial_c5_lower_second (n : ℕ) (hn : 20000000 < n) (hn' : n ≤ 24000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- Each new subrange has a concrete integer witness. The midpoint
belongs only to the first subrange. Derived domains for Schoenfeld
page 356, display 5.1 star. -/
theorem primorial_c5_lower_domains :
    (16000000 < (16000001 : ℕ) ∧ 16000001 ≤ 20000000) ∧
    (20000000 < (20000001 : ℕ) ∧ 20000001 ≤ 24000000) ∧
    (16000000 < (20000000 : ℕ) ∧ 20000000 ≤ 20000000) ∧ ¬ 20000000 < (20000000 : ℕ) := by
  norm_num

/-- Exact supply for Task460.primorial_c5_lower. CONDITIONAL ON
primorial_c5_lower_first and primorial_c5_lower_second.
Source Schoenfeld page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c5_lower (n : ℕ) (hn : 16000000 < n) (hn' : n ≤ 24000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 20000000
  · exact primorial_c5_lower_first n hn hm
  · exact primorial_c5_lower_second n (by omega) hn'

/-- LEAF. Schoenfeld page 356, display 5.1 star, derived integer
certificate strictly above 24000000 through 28000000. This is a proper
subrange of Task460.primorial_c5_upper. No analytic input is assumed. -/
theorem primorial_c5_upper_first (n : ℕ) (hn : 24000000 < n) (hn' : n ≤ 28000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Schoenfeld page 356, display 5.1 star, derived integer
certificate strictly above 28000000 through 32000000. This is a proper
subrange of Task460.primorial_c5_upper. No analytic input is assumed. -/
theorem primorial_c5_upper_second (n : ℕ) (hn : 28000000 < n) (hn' : n ≤ 32000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- Each new subrange has a concrete integer witness. The midpoint
belongs only to the first subrange. Derived domains for Schoenfeld
page 356, display 5.1 star. -/
theorem primorial_c5_upper_domains :
    (24000000 < (24000001 : ℕ) ∧ 24000001 ≤ 28000000) ∧
    (28000000 < (28000001 : ℕ) ∧ 28000001 ≤ 32000000) ∧
    (24000000 < (28000000 : ℕ) ∧ 28000000 ≤ 28000000) ∧ ¬ 28000000 < (28000000 : ℕ) := by
  norm_num

/-- Exact supply for Task460.primorial_c5_upper. CONDITIONAL ON
primorial_c5_upper_first and primorial_c5_upper_second.
Source Schoenfeld page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c5_upper (n : ℕ) (hn : 24000000 < n) (hn' : n ≤ 32000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 28000000
  · exact primorial_c5_upper_first n hn hm
  · exact primorial_c5_upper_second n (by omega) hn'

end LeanLab.LiuWang2002.Task551
#print axioms LeanLab.LiuWang2002.Task551.primorial_c5_lower_first
#print axioms LeanLab.LiuWang2002.Task551.primorial_c5_lower_second
#print axioms LeanLab.LiuWang2002.Task551.primorial_c5_lower_domains
#print axioms LeanLab.LiuWang2002.Task551.primorial_c5_lower
#print axioms LeanLab.LiuWang2002.Task551.primorial_c5_upper_first
#print axioms LeanLab.LiuWang2002.Task551.primorial_c5_upper_second
#print axioms LeanLab.LiuWang2002.Task551.primorial_c5_upper_domains
#print axioms LeanLab.LiuWang2002.Task551.primorial_c5_upper
