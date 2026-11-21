import LeanLab.Ported.Prove2Me.LL_Decomp368b_primorial_c3

/-!
Task666 memory repair. Existing declarations are moved without changing their text.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite certificates.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
4000000 strictly below n through 8000000. This is one proper subrange. -/
theorem primorial_c3 (n : ℕ) (hn : 4000000 < n) (hn' : n ≤ 8000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact LeanLab.Ported.Prove2Me.Task664.LL_Decomp368b.primorial_c3 n hn hn'

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.primorial_c3
