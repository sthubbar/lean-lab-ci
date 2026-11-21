import LeanLab.LiuWang2002.Lower664

/-!
Task666 memory repair. Existing declarations are moved without changing their text.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite certificates.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
2000000 strictly below n through 4000000. This is one proper subrange. -/
theorem primorial_c2 (n : ℕ) (hn : 2000000 < n) (hn' : n ≤ 4000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact Task664.primorial_1m_4m n (by omega) hn'

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.primorial_c2
