import LeanLab.ChenDoubleSieve.Task562ListIdentity
import LeanLab.ChenDoubleSieve.Task562ListCheck

/-!
Exact supply for the smallest open I2 bound, Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/pdf/0705.1652, Table 1 row four page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- The exact polynomial integral fits the remaining rational kernel budget.
Wu 2004 page 26, derived finite coefficient certificate. -/
theorem r3_polynomial_certificate :
    (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)), r3Poly x) ≤
      (43179 / 1000000000 : ℝ) := by
  have he (x : Fin 4 → ℝ) : listEval r3Terms (fun j => x j - (100 / 291 : ℝ)) = r3Poly x := by
    rw [r3Terms_eval]
    congr 1
    funext j
    ring
  have h := integral_listEval r3Terms (by norm_num : (100 / 291 : ℚ) ≤ 2 / 5)
  simp only [Rat.cast_div, Rat.cast_ofNat, he] at h
  rw [r3Terms_moment] at h
  push_cast at h
  exact h.le.trans polynomial_candidate_fits

/-- The rational phi two integral satisfies its exact certificate budget.
Wu 2004 page 26, D2,16 at Table 1 row four page 30. -/
theorem r3_rational_clean :
    (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)), r3Base x) ≤
      (43179 / 1000000000 : ℝ) :=
  r3_integral_le_polynomial.trans r3_polynomial_certificate

/-- The exact original bound I2_r3_16 follows with no numerical or quadrature input.
Wu 2004 Lemma 5.2 page 26, D2,16 at Table 1 row four page 30. -/
theorem I2_r3_16_clean {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 7 ≤ (21601/500000000 : ℝ) := by
  have h := r3_sup_envelope hω hz
  have hc := r3_rational_clean
  linarith

end LeanLab.ChenDoubleSieve.Task562
