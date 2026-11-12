import LeanLab.LiuWang2002.CheckData368_132
import LeanLab.LiuWang2002.Decomp460a

/-!
Strictly smaller finite ranges supplying Task352.primorial_block_c.
Source Schoenfeld page 356, display 5.1 star, derived integer certificates.
The five remaining ranges are open and the final assembly is CONDITIONAL.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
1000000 strictly below n through 2000000. Later ranges are separate. -/
theorem primorial_c1 (n : ℕ) (hn : 1000000 < n) (hn' : n ≤ 2000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact prefix_132 n (by omega) hn'

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
2000000 strictly below n through 4000000. This is one proper subrange. -/
theorem primorial_c2 (n : ℕ) (hn : 2000000 < n) (hn' : n ≤ 4000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact LeanLab.LiuWang2002.Task460.primorial_c2 n hn hn'

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
4000000 strictly below n through 8000000. This is one proper subrange. -/
theorem primorial_c3 (n : ℕ) (hn : 4000000 < n) (hn' : n ≤ 8000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
8000000 strictly below n through 16000000. This is one proper subrange. -/
theorem primorial_c4 (n : ℕ) (hn : 8000000 < n) (hn' : n ≤ 16000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
16000000 strictly below n through 32000000. This is one proper subrange. -/
theorem primorial_c5 (n : ℕ) (hn : 16000000 < n) (hn' : n ≤ 32000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
32000000 strictly below n through 100000000. This excludes the entire
lower prefix and is a proper subrange of the original last block. -/
theorem primorial_c6 (n : ℕ) (hn : 32000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- The exact final block statement. CONDITIONAL ON the five unproved
proper subranges above 2000000. The assembly has no local sorry.
Source page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_block_c (n : ℕ) (hn : 1000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases h1 : n ≤ 2000000
  · exact primorial_c1 n hn h1
  by_cases h2 : n ≤ 4000000
  · exact primorial_c2 n (by omega) h2
  by_cases h3 : n ≤ 8000000
  · exact primorial_c3 n (by omega) h3
  by_cases h4 : n ≤ 16000000
  · exact primorial_c4 n (by omega) h4
  by_cases h5 : n ≤ 32000000
  · exact primorial_c5 n (by omega) h5
  exact primorial_c6 n (by omega) hn'

/-- Each proper subrange has a concrete positive integer witness.
Derived nonempty domains for page 356, display 5.1 star. -/
theorem split_instances :
    (1000000 < (1000001 : ℕ) ∧ 1000001 ≤ 2000000) ∧
    (2000000 < (2000001 : ℕ) ∧ 2000001 ≤ 4000000) ∧
    (4000000 < (4000001 : ℕ) ∧ 4000001 ≤ 8000000) ∧
    (8000000 < (8000001 : ℕ) ∧ 8000001 ≤ 16000000) ∧
    (16000000 < (16000001 : ℕ) ∧ 16000001 ≤ 32000000) ∧
    (32000000 < (32000001 : ℕ) ∧ 32000001 ≤ 100000000) := by
  norm_num

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.primorial_c1
#print axioms LeanLab.LiuWang2002.Task368.primorial_c2
#print axioms LeanLab.LiuWang2002.Task368.primorial_c3
#print axioms LeanLab.LiuWang2002.Task368.primorial_c4
#print axioms LeanLab.LiuWang2002.Task368.primorial_c5
#print axioms LeanLab.LiuWang2002.Task368.primorial_c6
#print axioms LeanLab.LiuWang2002.Task368.primorial_block_c
#print axioms LeanLab.LiuWang2002.Task368.split_instances
