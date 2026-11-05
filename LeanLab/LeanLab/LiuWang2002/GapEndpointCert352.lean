import Mathlib

/-!
Exact rational certificates for Schoenfeld page 356, middle cutoffs.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Integer power comparisons giving the two rational upper endpoints.
Derived certificate for page 356, proof of display 5.1 star. -/
theorem gap_endpoint_certificate :
    (271828183 : ℕ) ^ 1843 < 100936350 ^ 100 * 100000000 ^ 1843 ∧
    (271828183 : ℕ) ^ 1845 < 102975400 ^ 100 * 100000000 ^ 1845 := by
  decide +kernel
end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.gap_endpoint_certificate
