/-
Real parameter supply for the weighted smooth tail.
Source https://arxiv.org/abs/0801.0130 page 14 below display 50.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438j

namespace LeanLab.KumchevLiu2007.Rankin447
open Real

/-- Page 14 below display 50, derived real parameter absorption.
A positive power of log x in an exponential dominates every fixed power
of log x. The proof uses the Mathlib little o estimate for log against rpow. -/
theorem rankin_parameter_absorption (D B ε : ℝ) (hD : 0 ≤ D)
    (hB : 0 < B) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (max 1 (Real.log Q)) ^ D /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) ≤
          C / Real.log x ^ B := by
  let η := min ε (1 / 2 : ℝ)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hDB : 0 < D + B := by linarith
  have hc : 0 < η / (6 * (D + B)) := by positivity
  obtain ⟨L0, hb⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop hη).bound hc)
  refine ⟨1, max 2 (Real.exp (max L0 2)), by norm_num, le_max_left _ _, ?_⟩
  intro x y Q hx hy _hyx hQpos hQ
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := by linarith
  let L := Real.log x
  have hL : max L0 2 ≤ L := by
    apply (Real.le_log_iff_exp_le hxpos).mpr
    exact (le_max_right _ _).trans hx
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hlog : Real.log L ≤ η / (6 * (D + B)) * L ^ η := by
    have hh := hb L ((le_max_left _ _).trans hL)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      abs_of_pos (Real.rpow_pos_of_pos hLpos _)] using hh
  have hlogs : (D + B) * Real.log L ≤ η / 6 * L ^ η := by
    have hh := mul_le_mul_of_nonneg_left hlog hDB.le
    have he : (D + B) * (η / (6 * (D + B))) = η / 6 := by field_simp
    calc
      _ ≤ (D + B) * (η / (6 * (D + B)) * L ^ η) := hh
      _ = _ := by rw [← mul_assoc, he]
  let V := max 1 (Real.log Q)
  have hV1 : 1 ≤ V := le_max_left _ _
  have hVpos : 0 < V := by linarith
  have hV : V ≤ L ^ (1 - η) := by
    apply max_le
    · exact Real.one_le_rpow hL1 (by linarith)
    · have hlogQ : Real.log Q ≤ L ^ (1 - ε) :=
        (Real.log_le_iff_le_exp hQpos).mpr hQ
      exact hlogQ.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hVL : V ≤ L := by
    calc
      _ ≤ L ^ (1 - η) := hV
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L := Real.rpow_one L
  have hscale : V * L ^ η ≤ L := by
    calc
      _ ≤ L ^ (1 - η) * L ^ η :=
        mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hLpos.le _)
      _ = L := by rw [← Real.rpow_add hLpos]; simp
  have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos ε).trans_le hy
  have hlogy : η * L ≤ Real.log y := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hxpos ε) hy
    rw [Real.log_rpow hxpos] at hh
    exact (mul_le_mul_of_nonneg_right hηε hLpos.le).trans hh
  have harg0 : η / 6 * L ^ η ≤ Real.log y / (6 * V) := by
    apply (le_div_iff₀ (by positivity : 0 < 6 * V)).mpr
    have hh := mul_le_mul_of_nonneg_left hscale hη.le
    nlinarith
  have hT : 0 < y ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hypos _
  have harg : Real.exp (η / 6 * L ^ η) ≤
      (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * V)) := by
    rw [Real.rpow_def_of_pos hT]
    apply Real.exp_le_exp.mpr
    rw [Real.log_rpow hypos]
    convert harg0 using 1 <;> ring
  have hnum : V ^ D * L ^ B ≤ Real.exp (η / 6 * L ^ η) := by
    calc
      _ ≤ L ^ D * L ^ B :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hVpos.le hVL hD)
          (Real.rpow_nonneg hLpos.le _)
      _ = L ^ (D + B) := (Real.rpow_add hLpos _ _).symm
      _ = Real.exp ((D + B) * Real.log L) := by
        rw [Real.rpow_def_of_pos hLpos]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hlogs
  change V ^ D / (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * V)) ≤ 1 / L ^ B
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hLpos B)).mpr
  simpa only [one_mul] using hnum.trans harg

#print axioms rankin_parameter_absorption
end LeanLab.KumchevLiu2007.Rankin447
