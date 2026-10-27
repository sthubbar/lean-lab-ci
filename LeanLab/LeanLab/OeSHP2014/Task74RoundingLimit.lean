import LeanLab.OeSHP2014.Task74Fits

/-! The printed and full precision error bounds differ.
This is a rounding limitation, not a paper error.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- The rounded printed second moment coefficients do not meet the full precision limit. -/
theorem table12_printed_fit2_exceeds :
    0.000032 < momentFit 0.99260 (-3.7012) 7.7338 10 - 0.8464098596 := by
  have he : |momentFit 0.99260 (-3.7012) 7.7338 10 -
      0.84644577778145| ≤ 0.000000000001 := by
    convert momentFit_error_of_cert 10 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (16928915555629 / 20000000000000) (1 / 1000000000000)
      (43429448190307 / 1000000000000000) (43429448190327 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h := (abs_le.mp he).1
  linarith

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.table12_printed_fit2_exceeds
