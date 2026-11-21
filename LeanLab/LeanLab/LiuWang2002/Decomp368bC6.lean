import LeanLab.Ported.Prove2Me.LL_Decomp368b_primorial_c6

/-!
Task666 memory repair. Existing declarations are moved without changing their text.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite certificates.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
32000000 strictly below n through 100000000. This excludes the entire
lower prefix and is a proper subrange of the original last block. -/
theorem primorial_c6 (n : ℕ) (hn : 32000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact LeanLab.Ported.Prove2Me.Task666.LL_Decomp368b.primorial_c6 n hn hn'

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.primorial_c6
