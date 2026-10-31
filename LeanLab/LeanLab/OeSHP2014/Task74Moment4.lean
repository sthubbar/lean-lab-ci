import LeanLab.OeSHP2014.Task74Fits

/-! Printed Table 12 data on page 2056 and fit formula on page 2057.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

def momentRows4 : List (ℕ × ℚ) := [
  (10, 5675297645 / 10^10),
  (11, 5963595130 / 10^10),
  (12, 6214928727 / 10^10),
  (13, 6436059388 / 10^10),
  (14, 6631624243 / 10^10),
  (15, 6805959792 / 10^10),
  (16, 6962328171 / 10^10),
  (17, 7103390224 / 10^10),
  (18, 7231323343 / 10^10)]

theorem table12_fit4 : ∀ r ∈ momentRows4,
    |momentFit (97109 / 100000) (-2303 / 200) (25619 / 500) r.1 - (r.2 : ℝ)| ≤ (1 / 6250) := by
  intro r hr
  simp only [momentRows4, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · convert momentFit_error_of_cert 10 (by norm_num)
      (97109 / 100000) (-2303 / 200) (25619 / 500) (1135059529 / 2000000000) (1 / 6250)
      (43429448190307 / 1000000000000000) (43429448190327 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 11 (by norm_num)
      (97109 / 100000) (-2303 / 200) (25619 / 500) (596359513 / 1000000000) (1 / 6250)
      (19740658268321 / 500000000000000) (39481316536661 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 12 (by norm_num)
      (97109 / 100000) (-2303 / 200) (25619 / 500) (6214928727 / 10000000000) (1 / 6250)
      (7238241365051 / 200000000000000) (4523900853159 / 125000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 13 (by norm_num)
      (97109 / 100000) (-2303 / 200) (25619 / 500) (1609014847 / 2500000000) (1 / 6250)
      (33407267838697 / 1000000000000000) (33407267838713 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 14 (by norm_num)
      (97109 / 100000) (-2303 / 200) (25619 / 500) (6631624243 / 10000000000) (1 / 6250)
      (31021034421647 / 1000000000000000) (15510517210831 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 15 (by norm_num)
      (97109 / 100000) (-2303 / 200) (25619 / 500) (425372487 / 625000000) (1 / 6250)
      (7238241365051 / 250000000000000) (14476482730109 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 16 (by norm_num)
      (97109 / 100000) (-2303 / 200) (25619 / 500) (6962328171 / 10000000000) (1 / 6250)
      (27143405118941 / 1000000000000000) (13571702559477 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 17 (by norm_num)
      (97109 / 100000) (-2303 / 200) (25619 / 500) (443961889 / 625000000) (1 / 6250)
      (3193341778699 / 125000000000000) (6386683557401 / 250000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 18 (by norm_num)
      (97109 / 100000) (-2303 / 200) (25619 / 500) (7231323343 / 10000000000) (1 / 6250)
      (24127471216837 / 1000000000000000) (1507966951053 / 62500000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.table12_fit4
