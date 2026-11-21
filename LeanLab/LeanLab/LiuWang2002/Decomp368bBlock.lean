import LeanLab.LiuWang2002.Decomp368bC1
import LeanLab.LiuWang2002.Decomp368bC2
import LeanLab.LiuWang2002.Decomp368bC3
import LeanLab.LiuWang2002.Decomp368bC4
import LeanLab.LiuWang2002.Decomp368bC5
import LeanLab.LiuWang2002.Decomp368bC6

/-!
Task666 memory repair. Existing declarations are moved without changing their text.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite certificates.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- The exact final block statement. Every finite subrange is supplied by
a kernel checked theorem. The assembly has no local sorry.
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

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.primorial_block_c
