import LeanLab.Zhao2025.Zhao2025U6825Lemma31

/-!
An explicit margin below the printed 19.62 absorbs the epsilon factor in Lemma 3.1.
Source: Zhao 2025, displays 3.5 and 3.13, pages 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- A tighter enclosure leaves a positive margin under the printed coefficient. -/
theorem C313_tighter : C (1 / 12) (1 / 4) (1 / 6) 1.311 (1 / 2) ≤ 19.612 := by
  unfold C
  exact (sqrt_enclose (lo := 19.61) (hi := 19.612)
    (by norm_num) (by norm_num) (by norm_num) B313a B313b (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2

#print axioms C313_tighter

end LeanLab.Zhao2025.Task56
