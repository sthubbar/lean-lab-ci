import LeanLab.ChenDoubleSieve.Task562ListData
import LeanLab.ChenDoubleSieve.Task562Polynomial

/-!
Algebraic identity for the explicit D2,16 polynomial coefficients, Wu 2004 page 26.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Finset
namespace LeanLab.ChenDoubleSieve.Task562

/-- The explicit list represents the proved polynomial enclosure in shifted coordinates.
Wu 2004 page 26, derived exact algebraic certificate. -/
theorem r3Terms_eval (y : Fin 4 → ℝ) :
    listEval r3Terms y = r3Poly (fun j => y j + (100 / 291 : ℝ)) := by
  simp only [listEval, r3Terms, r3TermsBlock00, r3TermsBlock01, r3TermsBlock02, r3TermsBlock03, r3TermsBlock04, r3TermsBlock05, r3TermsBlock06, r3TermsBlock07, r3TermsBlock08, r3TermsBlock09, r3TermsBlock10, r3TermsBlock11, r3TermsBlock12, r3TermsBlock13, r3TermsBlock14, r3TermsBlock15, r3TermsBlock16, r3TermsBlock17, r3TermsBlock18, r3TermsBlock19, r3TermsBlock20, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, pow_zero, pow_one, mul_one]
  unfold r3Poly g3 p5
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    mul_one, add_zero]
  push_cast
  ring

end LeanLab.ChenDoubleSieve.Task562
