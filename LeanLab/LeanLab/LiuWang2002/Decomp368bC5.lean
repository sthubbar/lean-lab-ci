import LeanLab.LiuWang2002.Chain666

/-!
Task666 memory repair. Existing declarations are moved without changing their text.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite certificates.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
16000000 strictly below n through 32000000. This is one proper subrange. -/
theorem primorial_c5 (n : ℕ) (hn : 16000000 < n) (hn' : n ≤ 32000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact LeanLab.LiuWang2002.Task666.primorial_c5_chain n hn hn'

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.primorial_c5
