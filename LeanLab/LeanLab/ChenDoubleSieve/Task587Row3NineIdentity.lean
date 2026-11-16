import LeanLab.ChenDoubleSieve.Task587Row3NineData

/-!
Exact polynomial identity for Wu 2004 Lemma 5.2 page 26, D2,9 at Table 1 row four page 30.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- The coefficient list is the reciprocal polynomial after translation.
Wu 2004 page 26, derived exact algebraic identity. -/
theorem r3NineTerms_eval (y : Fin 3 → ℝ) :
    listEvalN r3NineTerms y = r3NinePoly (fun j => 25 / 89 + y j) := by
  norm_num [listEvalN, r3NineTerms, r3NineTerms0, r3NineTerms1, r3NineTerms2,
    r3NineTerms3, r3NinePoly, reciprocalUpper, sum_range_succ, Fin.prod_univ_succ]
  <;> ring

/-- The polynomial integral fits a rational upper bound.
Wu 2004 page 26, derived exact ordered moment certificate. -/
theorem r3Nine_polynomial_certificate :
    (∫ x in domain (fun _ : Fin 3 => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)),
      r3NinePoly x) ≤ (2203 / 100000 : ℝ) := by
  have he (x : Fin 3 → ℝ) :
      listEvalN r3NineTerms (fun j => x j - (25 / 89 : ℝ)) = r3NinePoly x := by
    rw [r3NineTerms_eval]
    congr 1
    funext j
    ring
  have h := integral_listEvalN r3NineTerms (by norm_num : (25 / 89 : ℚ) ≤ 2 / 5)
  simp only [Rat.cast_div, Rat.cast_ofNat, he] at h
  rw [r3NineTerms_moment] at h
  push_cast at h
  apply h.le.trans
  norm_num

end LeanLab.ChenDoubleSieve.Task587
