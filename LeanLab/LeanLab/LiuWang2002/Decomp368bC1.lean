import LeanLab.LiuWang2002.Lower664

/-!
Task666 memory repair. Existing declarations are moved without changing their text.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite certificates.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for
1000000 strictly below n through 2000000. Later ranges are separate. -/
theorem primorial_c1 (n : ℕ) (hn : 1000000 < n) (hn' : n ≤ 2000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact Task664.primorial_1m_4m n hn (by omega)

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.primorial_c1
