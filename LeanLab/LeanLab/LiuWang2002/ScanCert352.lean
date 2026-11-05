import LeanLab.LiuWang2002.ThetaScan352

/-!
Shared prefix certificate for the first finite theta block.
Source Schoenfeld page 356, display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel certificate for the shared scan from 64 through 1000.
The state and cutoff are derived data for page 356, display 5.1 star. -/
theorem scan_to_1000 :
    thetaScan 936 64 (primorial 64) (25 ^ 64) (68 ^ 64) = true := by
  decide +kernel

/-- The integer certificate holds throughout the first scanned interval.
Derived finite range result for page 356, display 5.1 star. -/
theorem primorial_through_1000 (n : ℕ) (hn : 64 < n) (hn' : n ≤ 1000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact thetaScan_sound 936 64 scan_to_1000 n hn (by omega)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel certificate for the shared smallest factor scan through 10000.
Derived finite proof data for page 356, display 5.1 star. -/
theorem scan_to_10000 :
    thetaScan 9936 64 (primorial 64) (25 ^ 64) (68 ^ 64) = true := by
  decide +kernel

/-- Every integer in the first remaining finite block has a certificate.
Derived finite range result for page 356, display 5.1 star. -/
theorem primorial_through_10000 (n : ℕ) (hn : 64 < n) (hn' : n ≤ 10000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact thetaScan_sound 9936 64 scan_to_10000 n hn (by omega)

end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.scan_to_1000
#print axioms LeanLab.LiuWang2002.Task352.primorial_through_1000
#print axioms LeanLab.LiuWang2002.Task352.scan_to_10000
#print axioms LeanLab.LiuWang2002.Task352.primorial_through_10000
