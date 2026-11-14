import LeanLab.ChenDoubleSieve.Task562Supply

/-!
A rational integral certificate for Wu 2004 Lemma 5.2 page 26, D2,16.
Source: https://arxiv.org/pdf/0705.1652, Table 1 row four page 30.
The Buchstab function and the unbounded phi parameter have been eliminated from the leaf.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,16 at Table 1 row four page 30.
The integral of the exact rational phi two kernel is at most 0.000043179.
This is strictly smaller than the original leaf: there is no Buchstab function and no phi supremum.
The written certificate route is a polynomial upper enclosure of the positive rational kernel
on the compact ordered chamber, followed by exact rational integration of its monomials.
The kernel is symmetric in the four coordinates. Gaussian orders 12, 24 and 48 give
0.0000431570725003, which motivates the budget but supplies no quadrature proof. -/
theorem r3_rational_certificate :
    (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)), r3Base x) ≤
      (43179 / 1000000000 : ℝ) := by
  exact r3_rational_clean

/-- The exact original I2_r3_16 statement follows from one rational certificate and the
proved corner error. Wu 2004 page 26 and Table 1 page 30. The rational certificate is supplied. -/
theorem I2_r3_16_from_rational {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 7 ≤ (21601/500000000 : ℝ) := by
  have h := r3_sup_envelope hω hz
  have hc := r3_rational_certificate
  linarith

end LeanLab.ChenDoubleSieve.Task562
