/-
P0095 Lu 2010, page 2366 generalized Gauss sum and page 2379 equation 63.
CODEX task47, unit U-8104. AI wrote this Lean code. Binary Goldbach is open.
The finite Gauss sum and rational Fourier sum conventions agree exactly.
-/
import LeanLab.ExceptionalSet.Lu2010Eq86
import LeanLab.PNTPort.Vinogradov.MinorArcs

namespace LeanLab.ExceptionalSet.Lu2010GaussFourier
open Finset ZMod
open LeanLab.PNTPort.LargeSieve
open LeanLab.ExceptionalSet.Lu2010Eq86

theorem std_neg_nat_product {q : ℕ} [NeZero q] (a k : ℕ) :
    stdAddChar (-(k : ZMod q) * (a : ZMod q)) = e (-(k : ℝ) * a / q) := by
  have he : -(k : ZMod q) * (a : ZMod q) = ((-((k : ℤ) * a) : ℤ) : ZMod q) := by
    push_cast
    ring
  rw [he, stdAddChar_coe]
  unfold e
  congr 1
  push_cast
  ring

/-- Generalized Gauss sum at minus k, as the reduced numerator sum used by the Fourier expansion. -/
theorem gauss_reduced {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) :
    gaussSum χ (stdAddChar.mulShift (-(k : ZMod q))) =
      ∑ a ∈ (range q).filter (fun a => a.Coprime q), χ (a : ZMod q) * e (-(k : ℝ) * a / q) := by
  classical
  unfold gaussSum
  simp only [AddChar.mulShift_apply]
  have hv : (∑ a : ZMod q, χ a * stdAddChar (-(k : ZMod q) * a)) =
      ∑ a : ZMod q, χ (a.val : ZMod q) * e (-(k : ℝ) * a.val / q) := by
    apply sum_congr rfl
    intro a _
    rw [← std_neg_nat_product, natCast_zmod_val]
  rw [hv, LeanLab.PNTPort.Vinogradov.sum_zmod_eq_range
    (fun a => χ (a : ZMod q) * e (-(k : ℝ) * a / q)), sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : a.Coprime q
  · simp [ha]
  · have hunit : ¬ IsUnit (a : ZMod q) := by
      simpa only [ZMod.isUnit_iff_coprime] using ha
    rw [if_neg ha, χ.map_nonunit hunit, zero_mul]

/-- Regroup the rational Fourier sum by denominator. -/
theorem rationalSum_double (Q : ℕ) (B : ℕ × ℕ → ℂ) (k : ℕ) :
    rationalSum Q B (k : ℤ) = ∑ q ∈ Icc 1 Q,
      ∑ a ∈ (range q).filter (fun a => a.Coprime q), B (q, a) * e (-(k : ℝ) * a / q) := by
  classical
  unfold rationalSum farey
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro q hq
  have hqQ := (mem_Icc.mp hq).2
  rw [← sum_filter]
  have hs : (range Q).filter (fun a => a < q ∧ a.Coprime q) =
      (range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [mem_filter, mem_range]
    omega
  rw [hs]
  apply sum_congr rfl
  intro a _
  unfold fareyPt
  congr 2
  push_cast
  ring

end LeanLab.ExceptionalSet.Lu2010GaussFourier

#print axioms LeanLab.ExceptionalSet.Lu2010GaussFourier.std_neg_nat_product
#print axioms LeanLab.ExceptionalSet.Lu2010GaussFourier.gauss_reduced
#print axioms LeanLab.ExceptionalSet.Lu2010GaussFourier.rationalSum_double
