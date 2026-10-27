import LeanLab.OeSHP2014.Task74Fits

/-! Printed Table 12 data on page 2056 and fit formula on page 2057.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

def momentRows3 : List (ℕ × ℚ) := [
  (10, 6974579430 / 10^10),
  (11, 7195994626 / 10^10),
  (12, 7385895560 / 10^10),
  (13, 7550798973 / 10^10),
  (14, 7695103964 / 10^10),
  (15, 7822550563 / 10^10),
  (16, 7935938057 / 10^10),
  (17, 8037506718 / 10^10),
  (18, 8129043169 / 10^10)]

theorem table12_fit3 : ∀ r ∈ momentRows3,
    |momentFit (98357 / 100000) (-76839 / 10000) (6317 / 250) r.1 - (r.2 : ℝ)| ≤ (13 / 200000) := by
  intro r hr
  simp only [momentRows3, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · convert momentFit_error_of_cert 10 (by norm_num)
      (98357 / 100000) (-76839 / 10000) (6317 / 250) (697457943 / 1000000000) (13 / 200000)
      (43429448190307 / 1000000000000000) (43429448190327 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 11 (by norm_num)
      (98357 / 100000) (-76839 / 10000) (6317 / 250) (3597997313 / 5000000000) (13 / 200000)
      (19740658268321 / 500000000000000) (39481316536661 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 12 (by norm_num)
      (98357 / 100000) (-76839 / 10000) (6317 / 250) (184647389 / 250000000) (13 / 200000)
      (7238241365051 / 200000000000000) (4523900853159 / 125000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 13 (by norm_num)
      (98357 / 100000) (-76839 / 10000) (6317 / 250) (7550798973 / 10000000000) (13 / 200000)
      (33407267838697 / 1000000000000000) (33407267838713 / 1000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 14 (by norm_num)
      (98357 / 100000) (-76839 / 10000) (6317 / 250) (1923775991 / 2500000000) (13 / 200000)
      (31021034421647 / 1000000000000000) (15510517210831 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 15 (by norm_num)
      (98357 / 100000) (-76839 / 10000) (6317 / 250) (7822550563 / 10000000000) (13 / 200000)
      (7238241365051 / 250000000000000) (14476482730109 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 16 (by norm_num)
      (98357 / 100000) (-76839 / 10000) (6317 / 250) (7935938057 / 10000000000) (13 / 200000)
      (27143405118941 / 1000000000000000) (13571702559477 / 500000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 17 (by norm_num)
      (98357 / 100000) (-76839 / 10000) (6317 / 250) (4018753359 / 5000000000) (13 / 200000)
      (3193341778699 / 125000000000000) (6386683557401 / 250000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert momentFit_error_of_cert 18 (by norm_num)
      (98357 / 100000) (-76839 / 10000) (6317 / 250) (8129043169 / 10000000000) (13 / 200000)
      (24127471216837 / 1000000000000000) (1507966951053 / 62500000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.table12_fit3
