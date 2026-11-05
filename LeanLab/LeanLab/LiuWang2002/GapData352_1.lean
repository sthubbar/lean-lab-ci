import LeanLab.LiuWang2002.GapCert352

/-!
Finite proper prime power certificate for Schoenfeld page 356, display 9.3.
The integers are derived certificate data.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- An exact integer comparison giving a lower gap bound at 100140049.
Derived certificate for page 356, display 9.3. -/
theorem gap_certificate_1 :
    2718282 ^ 10521 < gapProduct 100140049 ^ 1 * 1000000 ^ 10521 := by
  rw [gapProduct_eq_fast]
  decide +kernel
end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.gap_certificate_1
