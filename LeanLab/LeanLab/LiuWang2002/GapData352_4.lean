import LeanLab.LiuWang2002.GapCert352

/-!
Finite proper prime power certificate for Schoenfeld page 356, display 9.3.
The integers are derived certificate data.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- An exact integer comparison giving a lower gap bound at 100781521.
Derived certificate for page 356, display 9.3. -/
theorem gap_certificate_4 :
    2718282 ^ 84397 < gapProduct 100781521 ^ 8 * 1000000 ^ 84397 := by
  rw [gapProduct_eq_fast]
  decide +kernel
end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.gap_certificate_4
