import LeanLab.LiuWang2002.GapCert352

/-!
Finite lower certificate for the last middle intervals on Schoenfeld page 356.
The endpoints are derived proof data for the proof of display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Exact certificate at square endpoint 10000 squared. Derived data for
page 356, the proper prime power lower bound following display 9.3. -/
theorem late_certificate_0 :
    2718282 ^ 10512 < gapProduct 100000000 * 1000000 ^ 10512 := by
  rw [gapProduct_eq_fast]
  decide +kernel
end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.late_certificate_0
