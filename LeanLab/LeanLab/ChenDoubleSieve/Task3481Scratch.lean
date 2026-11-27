import LeanLab.ChenDoubleSieve.Table1Algebra

noncomputable section
namespace LeanLab.ChenDoubleSieve.Burst9Matrix
open Wu04Table
open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology
open Wu04Table
open LeanLab.ChenDoubleSieve.Wu04Integral

/-- On the open panel `]11/5, 23/10[` the row-0 `Xi2` kernel has four active windows.
This records the exact reduced kernel before the quadrature bounds are assembled. -/
private theorem Xi2_0_1_eq {t : ℝ} (h1 : ((11/5 : ℝ) : ℝ) < t) (h2 : t < (23/10 : ℝ)) :
    Wu04Functional.Xi2 (Wu04Functional.tableParams ⟨0, by norm_num⟩) t =
      Wu04Integral.sigma0 t / (5 * t) * log (1024 / (22972653/781250 : ℝ)) +
        log ((t + 1) ^ 2 / ((253/100 : ℝ) * (19/10 : ℝ))) / (5 * t) +
        log ((t + 1) / ((36/25 : ℝ) * (177/50 : ℝ))) / (5 * t) +
        log ((t + 1) / ((6/5 : ℝ) * (177/50 : ℝ))) / (5 * t) +
        log (177/50 - t) / (5 * t * (1 - t / (227/50 : ℝ))) := by
  have p0 : ((127/50 : ℝ) : ℝ) ≤ t ∧ t ≤ 3 := by constructor <;> linarith
  have pa0 : ((153/100 : ℝ) : ℝ) ≤ t := by linarith
  have pa2 : ((406/275 : ℝ) : ℝ) ≤ t := by linarith
  have pa4 : ((2863/1450 : ℝ) : ℝ) ≤ t := by linarith
  have pa7 : ((864189/511850 : ℝ) : ℝ) ≤ t := by linarith
  have n1 : ¬ (((127/50 : ℝ) : ℝ) ≤ t ∧ t ≤ 3) := by
    intro hc; linarith [hc.1, hc.2]
  have n2 : ¬ (((3807/2900 : ℝ) : ℝ) ≤ t ∧ t ≤ (153/100 : ℝ)) := by
    intro hc; linarith [hc.1, hc.2]
  have n3 : ¬ (((406/275 : ℝ) : ℝ) ≤ t ∧ t ≤ (127/50 : ℝ)) := by
    intro hc; linarith [hc.1, hc.2]
  have n4 : ¬ (((2863/1450 : ℝ) : ℝ) ≤ t ∧ t ≤ (127/50 : ℝ)) := by
    intro hc; linarith [hc.1, hc.2]
  have n5 : ¬ (((2561/1525 : ℝ) : ℝ) ≤ t ∧ t ≤ (2863/1450 : ℝ)) := by
    intro hc; linarith [hc.1, hc.2]
  have n6 : ¬ (((750008/538325 : ℝ) : ℝ) ≤ t ∧ t ≤ (2561/1525 : ℝ)) := by
    intro hc; linarith [hc.1, hc.2]
  have n7 : ¬ (((2043/1450 : ℝ) : ℝ) ≤ t ∧ t ≤ (864189/511850 : ℝ)) := by
    intro hc; linarith [hc.1, hc.2]
  have n8 : ¬ (((864189/511850 : ℝ) : ℝ) ≤ t ∧ t ≤ (127/50 : ℝ)) := by
    intro hc; linarith [hc.1, hc.2]
  simp only [Wu04Functional.Xi2, Wu04Functional.ind, Wu04Functional.alpha,
    Wu04Functional.tableParams]
  norm_num
  simp only [if_neg n1, if_neg n2, if_pos pa0, if_pos pa2, if_pos pa4,
    if_neg n3, if_neg n4, if_neg n5, if_neg n6, if_neg n7, if_pos pa7, if_neg n8]
  ring


end LeanLab.ChenDoubleSieve.Burst9Matrix
