import LeanLab.OeSHP2014.Task74Moment2

/-! A rounding witness for Table 12 on pages 2056 and 2057.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- A coefficient inside the printed rounding cell meets the printed error bound. -/
theorem table12_fit2_rounding_witness :
    |(0.992596 : ℝ) - 0.99260| < 0.000005 ∧
    ∀ r ∈ momentRows2,
      |momentFit 0.992596 (-3.7012) 7.7338 r.1 - (r.2 : ℝ)| ≤ 0.000032 := by
  constructor
  · norm_num
  intro r hr
  simp only [momentRows2, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · convert momentFit_error_of_cert 10 (by norm_num)
      (248149 / 250000) (-9253 / 2500) (38669 / 5000) (2116024649 / 2500000000) (1 / 31250)
      (43429448190307 / 1000000000000000) (43429448190327 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 11 (by norm_num)
      (248149 / 250000) (-9253 / 2500) (38669 / 5000) (8585304971 / 10000000000) (1 / 31250)
      (19740658268321 / 500000000000000) (39481316536661 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 12 (by norm_num)
      (248149 / 250000) (-9253 / 2500) (38669 / 5000) (868782627 / 1000000000) (1 / 31250)
      (7238241365051 / 200000000000000) (4523900853159 / 125000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 13 (by norm_num)
      (248149 / 250000) (-9253 / 2500) (38669 / 5000) (4387923297 / 5000000000) (1 / 31250)
      (33407267838697 / 1000000000000000) (33407267838713 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 14 (by norm_num)
      (248149 / 250000) (-9253 / 2500) (38669 / 5000) (4426094753 / 5000000000) (1 / 31250)
      (31021034421647 / 1000000000000000) (15510517210831 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 15 (by norm_num)
      (248149 / 250000) (-9253 / 2500) (38669 / 5000) (1783818271 / 2000000000) (1 / 31250)
      (7238241365051 / 250000000000000) (14476482730109 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 16 (by norm_num)
      (248149 / 250000) (-9253 / 2500) (38669 / 5000) (89782131 / 100000000) (1 / 31250)
      (27143405118941 / 1000000000000000) (13571702559477 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 17 (by norm_num)
      (248149 / 250000) (-9253 / 2500) (38669 / 5000) (903086273 / 1000000000) (1 / 31250)
      (3193341778699 / 125000000000000) (6386683557401 / 250000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 18 (by norm_num)
      (248149 / 250000) (-9253 / 2500) (38669 / 5000) (283689557 / 312500000) (1 / 31250)
      (24127471216837 / 1000000000000000) (1507966951053 / 62500000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.table12_fit2_rounding_witness
