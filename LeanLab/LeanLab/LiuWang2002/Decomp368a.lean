import LeanLab.LiuWang2002.CheckData368_70

/-!
Exact supply for Task352.primorial_block_b. The source file stays sealed.
Source Schoenfeld page 356, display 5.1 star, derived integer certificate.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- The exact second integer block, supplied without the original leaf.
Derived finite certificate for page 356, display 5.1 star. -/
theorem primorial_block_b (n : ℕ) (hn : 10000 < n) (hn' : n ≤ 1000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact prefix_70 n (by omega) hn'

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.primorial_block_b
