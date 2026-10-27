/-
AI wrote this Lean code for CODEX task58.
Exact identities for the centered nested-integral polynomial certificates.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58NestedCertificates
import LeanLab.ChenPrimeExceptional.Task58Centered
import LeanLab.ChenPrimeExceptional.Task58MassIntegral

open Real Finset intervalIntegral MeasureTheory

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

theorem evalTerms_range (n : ℕ) (c : ℕ → ℚ) (d : ℕ → ℕ) (x : ℝ) :
    evalTerms ((List.range n).map (fun k => (c k, d k))) x =
      ∑ k ∈ range n, (c k : ℝ) * x ^ d k := by
  induction n with
  | zero => simp [evalTerms]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, evalTerms_append, ih, List.map_cons,
      List.map_nil, evalTerms_cons, evalTerms_nil, add_zero, sum_range_succ]

theorem logThreeHalvesQ_cast : (logThreeHalvesQ : ℝ) = logThreeHalvesApprox := by
  norm_num [logThreeHalvesQ, logThreeHalvesApprox, List.range_succ, sum_range_succ]

theorem centeredLogTerms_eval (z : ℝ) :
    evalTerms centeredLogTerms z = centeredLogPoly (z + 1 / 2) := by
  unfold centeredLogTerms
  rw [evalTerms_cons, evalTerms_range, logThreeHalvesQ_cast]
  simp only [pow_zero, mul_one]
  unfold centeredLogPoly
  rw [logPoly_expansion]
  congr 1
  apply sum_congr rfl
  intro i hi
  push_cast
  have he : (2 * (z + 1 / 2) - 1) / 3 = (2 / 3 : ℝ) * z := by ring
  rw [he, mul_pow]
  ring

theorem centeredReciprocalTerms_eval (z : ℝ) :
    evalTerms centeredReciprocalTerms z = centeredReciprocalPoly (z + 1 / 2) := by
  unfold centeredReciprocalTerms
  rw [evalTerms_range]
  unfold centeredReciprocalPoly geomPoly
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  push_cast
  have he : -(2 * (z + 1 / 2) - 1) / 5 = (-2 / 5 : ℝ) * z := by ring
  rw [he, mul_pow]
  ring

theorem centeredInnerTerms_eval (z : ℝ) :
    evalTerms centeredInnerTerms z = centeredInnerPoly (z + 1 / 2) := by
  unfold centeredInnerTerms centeredInnerPoly
  rw [evalTerms_mul, centeredLogTerms_eval, centeredReciprocalTerms_eval]

/-- The polynomial inner primitive, before evaluation of the rational mass. -/
def Happrox (w : ℝ) : ℝ := ∫ u in (0 : ℝ)..w, centeredInnerPoly u

theorem centeredHTerms_eval (z : ℝ) : evalTerms centeredHTerms z = Happrox (z + 1 / 2) := by
  unfold centeredHTerms
  rw [evalTerms_cons, Rat.cast_neg, pow_zero, mul_one,
    ← evalTerms_cast (antiTerms centeredInnerTerms) (-1 / 2)]
  rw [neg_add_eq_sub, ← integral_evalTerms_real]
  rw [integral_congr (fun u _ => centeredInnerTerms_eval u), integral_comp_add_right]
  norm_num [Happrox]

theorem centeredInnerPoly_continuous : Continuous centeredInnerPoly := by
  have h : Continuous (fun w : ℝ => evalTerms centeredInnerTerms (w - 1 / 2)) :=
    (evalTerms_continuous _).comp (continuous_id.sub continuous_const)
  convert h using 1
  ext w
  rw [centeredInnerTerms_eval]
  congr 1
  ring

theorem H_shift (w : ℝ) : H (2 + w) = ∫ u in (0 : ℝ)..w, inner (2 + u) := by
  rw [integral_comp_add_left]
  norm_num [H]

theorem Happrox_error {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |Happrox w - H (2 + w)| ≤ (1 / 1000000000 : ℝ) := by
  have hp : IntervalIntegrable centeredInnerPoly volume 0 w :=
    centeredInnerPoly_continuous.intervalIntegrable _ _
  have hi : IntervalIntegrable (fun u : ℝ => inner (2 + u)) volume 0 w := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hw.1]
    apply inner_continuous.comp (continuousOn_const.add continuousOn_id)
    intro u hu
    change (2 + u : ℝ) ∈ Set.Icc 2 3
    constructor <;> linarith [hu.1, hu.2, hw.2]
  have h := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := w)
    (C := (1 / 1000000000 : ℝ)) (f := fun u => centeredInnerPoly u - inner (2 + u)) (by
      intro u hu
      rw [Set.uIoc_of_le hw.1] at hu
      rw [Real.norm_eq_abs]
      exact centeredInnerPoly_error ⟨hu.1.le, hu.2.trans hw.2⟩)
  rw [integral_sub hp hi, Real.norm_eq_abs, ← H_shift] at h
  have hab : |w - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hw.1]; exact hw.2
  exact h.trans (by nlinarith)

theorem Happrox_bounds {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |Happrox w| ≤ 1 ∧ |1 + Happrox w| ≤ 2 := by
  have herr := Happrox_error hw
  rw [abs_le] at herr
  have hH := H_bounds (v := 2 + w) ⟨by linarith [hw.1], by linarith [hw.2]⟩
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [hw.2]

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.evalTerms_range
#print axioms LeanLab.ChenPrimeExceptional.Task58.logThreeHalvesQ_cast
#print axioms LeanLab.ChenPrimeExceptional.Task58.centeredLogTerms_eval
#print axioms LeanLab.ChenPrimeExceptional.Task58.centeredReciprocalTerms_eval
#print axioms LeanLab.ChenPrimeExceptional.Task58.centeredInnerTerms_eval
#print axioms LeanLab.ChenPrimeExceptional.Task58.centeredHTerms_eval
#print axioms LeanLab.ChenPrimeExceptional.Task58.centeredInnerPoly_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.H_shift
#print axioms LeanLab.ChenPrimeExceptional.Task58.Happrox_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.Happrox_bounds
