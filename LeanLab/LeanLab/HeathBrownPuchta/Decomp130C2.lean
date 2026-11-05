import LeanLab.HeathBrownPuchta.SReduction

/-!
P0012 page 26, display 41, the C2 reduction supporting Decomp130.
The sole cited input is Liu Liu Wang 1999 display 3.9 as quoted by P0012.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.HeathBrownPuchta.Decomp130

/-- LEAF. P0012 page 26 cites Liu, Liu and Wang 1999 display 3.9.
For m equal to the product of 2^e minus 1 up to n, m over phi m is at most
exp gamma times log n for every integer n at least 9.
Source https://arxiv.org/abs/math/0201299 page 26 reference 13. -/
theorem liu_liu_wang215 : LeanLab.HeathBrownPuchta.SReduction.LLW := by
  sorry
/-- P0012 page 26, display 41. CONDITIONAL ON liu_liu_wang215. -/
theorem c2_bound215 : LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 22141 / 10000 := by
  exact LeanLab.HeathBrownPuchta.SReduction.C2_le_at_20 liu_liu_wang215

end LeanLab.HeathBrownPuchta.Decomp130
