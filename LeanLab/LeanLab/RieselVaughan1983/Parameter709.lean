import LeanLab.RieselVaughan1983.Decomp426d
import Mathlib.Topology.Order.IntermediateValue

/-!
The parameter chosen in the proof of Schoenfeld 1976 Theorem 11.
The polynomial form of H extends to the lower endpoint without a singular quotient.
This file proves no estimate for psi.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Set

namespace LeanLab.RieselVaughan1983.Task709

/-- The expression H from Schoenfeld page 345 equation 7.28.
The paper sets d equal to log of 17 divided by 2 pi. -/
noncomputable def schoenfeldH (X d v : ℝ) : ℝ :=
  v ^ 4 * (2 * v ^ 2 - 1) * (v + d / X) ^ 3 /
    (v + (1 + 2 * d) / (2 * X))

/-- The parameter function k from Schoenfeld page 345 equation 7.27.
The polynomial form of H gives its continuous extension at the lower endpoint. -/
noncomputable def schoenfeldK (X d v : ℝ) : ℝ :=
  (17 * X / (2 * Real.pi)) * sqrt (schoenfeldH X d v) *
    exp (-2 * X * (1 - v)) * exp (-X * (1 - v) ^ 2 / v)

/-- The strict increase of H on the parameter interval used on page 345. -/
theorem schoenfeldH_increasing (X d v w : ℝ) (hX : 0 < X) (hd : 0 ≤ d)
    (hv : 0 < v) (hden : 1 < 2 * v ^ 2) (hvw : v < w) (hw : w ≤ 1) :
    schoenfeldH X d v < schoenfeldH X d w := by
  have ha : 0 ≤ (1 + 2 * d) / (2 * X) := by positivity
  have hb : 0 ≤ d / X := by positivity
  have hw0 : 0 < w := hv.trans hvw
  have hw2 : w ^ 2 ≤ 3 / 2 := by nlinarith
  have hdw : 0 < 2 * w ^ 2 - 1 := by nlinarith
  have hvA : 0 < v + (1 + 2 * d) / (2 * X) := by positivity
  have hwA : 0 < w + (1 + 2 * d) / (2 * X) := by positivity
  have h := Task426.schoenfeld_H_increasing ha hb hv hden hvw hw2
  convert h using 1 <;> dsimp [schoenfeldH] <;>
    field_simp

/-- Strict increase of k asserted after equation 7.27 on page 345. -/
theorem schoenfeldK_increasing (X d v w : ℝ) (hX : 0 < X) (hd : 0 ≤ d)
    (hv : 0 < v) (hden : 1 < 2 * v ^ 2) (hvw : v < w) (hw : w ≤ 1) :
    schoenfeldK X d v < schoenfeldK X d w := by
  have hvH : 0 ≤ schoenfeldH X d v := by
    unfold schoenfeldH
    have : 0 < 2 * v ^ 2 - 1 := by linarith
    positivity
  have hH := schoenfeldH_increasing X d v w hX hd hv hden hvw hw
  have hroot := Real.sqrt_lt_sqrt hvH hH
  have he1 : exp (-2 * X * (1 - v)) ≤ exp (-2 * X * (1 - w)) := by
    apply exp_le_exp.mpr
    nlinarith
  have he2 : exp (-X * (1 - v) ^ 2 / v) ≤ exp (-X * (1 - w) ^ 2 / w) := by
    apply exp_le_exp.mpr
    have h := Task426.schoenfeld_exponent_kernel_decreasing hv hvw hw
    have hm := mul_le_mul_of_nonpos_left h.le (show -X ≤ 0 by linarith)
    simpa only [mul_div_assoc] using hm
  unfold schoenfeldK
  calc
    _ < (17 * X / (2 * Real.pi)) * sqrt (schoenfeldH X d w) *
        exp (-2 * X * (1 - v)) * exp (-X * (1 - v) ^ 2 / v) := by
      gcongr
    _ ≤ _ := by gcongr

/-- The unique parameter selected after equation 7.27 on page 345 exists.
The stronger family X at least one and d nonnegative includes the paper's parameters. -/
theorem schoenfeld_parameter_exists_unique (X d : ℝ) (hX : 1 ≤ X) (hd : 0 ≤ d) :
    ∃! v : ℝ, v ∈ Ioo (sqrt (1 / 2)) 1 ∧ schoenfeldK X d v = 1 := by
  have hX0 : 0 < X := by linarith
  let l : ℝ := sqrt (1 / 2)
  have hl0 : 0 < l := by dsimp [l]; positivity
  have hlsq : l ^ 2 = 1 / 2 := by exact sq_sqrt (by norm_num)
  have hl1 : l < 1 := by nlinarith
  have hK0 : schoenfeldK X d l = 0 := by
    simp [schoenfeldK, schoenfeldH, hlsq]
  have hK1 : 1 < schoenfeldK X d 1 := by
    simpa [schoenfeldK, schoenfeldH, show (2 : ℝ) - 1 = 1 by norm_num] using Task426.schoenfeld_k_one_gt_one X d hX hd
  have hcontH : ContinuousOn (schoenfeldH X d) (Icc l 1) := by
    unfold schoenfeldH
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have hx0 : 0 < x := hl0.trans_le hx.1
    positivity
  have hcont : ContinuousOn (schoenfeldK X d) (Icc l 1) := by
    unfold schoenfeldK
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hcontH)
      · fun_prop
    · apply Real.continuous_exp.comp_continuousOn
      apply ContinuousOn.div (by fun_prop) continuousOn_id
      intro x hx
      exact ne_of_gt (hl0.trans_le hx.1)
  obtain ⟨v, hv, hvK⟩ := intermediate_value_Icc hl1.le hcont
    (show (1 : ℝ) ∈ Icc (schoenfeldK X d l) (schoenfeldK X d 1) by
      rw [hK0]; exact ⟨by norm_num, hK1.le⟩)
  have hvl : l < v := by
    have hne : l ≠ v := by intro h; subst v; rw [hK0] at hvK; norm_num at hvK
    exact lt_of_le_of_ne hv.1 hne
  have hv1 : v < 1 := by
    have hne : v ≠ 1 := by intro h; subst v; linarith
    exact lt_of_le_of_ne hv.2 hne
  refine ⟨v, ⟨⟨hvl, hv1⟩, hvK⟩, ?_⟩
  intro w hw
  have hv0 : 0 < v := hl0.trans hvl
  have hw0 : 0 < w := hl0.trans hw.1.1
  have hvden : 1 < 2 * v ^ 2 := by nlinarith
  have hwden : 1 < 2 * w ^ 2 := by nlinarith [hw.1.1]
  rcases lt_trichotomy w v with hlt | heq | hgt
  · have h := schoenfeldK_increasing X d w v hX0 hd hw0 hwden hlt hv1.le
    linarith [hw.2]
  · exact heq
  · have h := schoenfeldK_increasing X d v w hX0 hd hv0 hvden hgt hw.1.2.le
    linarith [hw.2]

end LeanLab.RieselVaughan1983.Task709
