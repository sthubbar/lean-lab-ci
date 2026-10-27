import LeanLab.OeSHP2014.Task74Fits

/-! Printed Table 12 data on page 2056 and fit formula on page 2057.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

def momentRows2 : List (ℕ × ℚ) := [
  (10, 8464098596 / 10^10),
  (11, 8585304971 / 10^10),
  (12, 8687826270 / 10^10),
  (13, 8775846594 / 10^10),
  (14, 8852189506 / 10^10),
  (15, 8919091355 / 10^10),
  (16, 8978213100 / 10^10),
  (17, 9030862730 / 10^10),
  (18, 9078065824 / 10^10)]

theorem table12_fit2 : ∀ r ∈ momentRows2,
    |momentFit (4963 / 5000) (-9253 / 2500) (38669 / 5000) r.1 - (r.2 : ℝ)| ≤ (37 / 1000000) := by
  intro r hr
  simp only [momentRows2, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · convert momentFit_error_of_cert 10 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (2116024649 / 2500000000) (37 / 1000000)
      (43429448190307 / 1000000000000000) (43429448190327 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 11 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (8585304971 / 10000000000) (37 / 1000000)
      (19740658268321 / 500000000000000) (39481316536661 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 12 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (868782627 / 1000000000) (37 / 1000000)
      (7238241365051 / 200000000000000) (4523900853159 / 125000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 13 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (4387923297 / 5000000000) (37 / 1000000)
      (33407267838697 / 1000000000000000) (33407267838713 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 14 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (4426094753 / 5000000000) (37 / 1000000)
      (31021034421647 / 1000000000000000) (15510517210831 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 15 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (1783818271 / 2000000000) (37 / 1000000)
      (7238241365051 / 250000000000000) (14476482730109 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 16 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (89782131 / 100000000) (37 / 1000000)
      (27143405118941 / 1000000000000000) (13571702559477 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 17 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (903086273 / 1000000000) (37 / 1000000)
      (3193341778699 / 125000000000000) (6386683557401 / 250000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 18 (by norm_num)
      (4963 / 5000) (-9253 / 2500) (38669 / 5000) (283689557 / 312500000) (37 / 1000000)
      (24127471216837 / 1000000000000000) (1507966951053 / 62500000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.table12_fit2
