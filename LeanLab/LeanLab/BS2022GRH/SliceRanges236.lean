/- AI wrote the Lean code for CODEX task236.
Bilinear slice ranges for journal Theorem 7 p. 1239. Goldbach is open. -/
import LeanLab.BS2022GRH.SliceSieveAssembly236
namespace LeanLab.BS2022GRH.SliceRemainder236
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- Basic domains of the bilinear substitution X equals N over w, Y equals the smaller
of y and one plus epsilon times w, and Z equals w, journal p. 1239. -/
theorem slice_bilinear_basic_ranges (n j : ℕ) (ε₁ : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1)
    (hj : j ∈ slices n ε₁) :
    25 ≤ (n : ℝ) / w n ε₁ j ∧ 25 ≤ min (U7153.yy n) ((1 + ε₁) * w n ε₁ j) ∧
    25 ≤ w n ε₁ j ∧ w n ε₁ j < min (U7153.yy n) ((1 + ε₁) * w n ε₁ j) ∧
    min (U7153.yy n) ((1 + ε₁) * w n ε₁ j) ≤ 2 * w n ε₁ j := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hnN : 0 < n := by exact_mod_cast hn0
  have hL := Lemma11C164.log_lower n hn
  have hz0 : 0 < U7153.zz n := rpow_pos_of_pos hn0 _
  have hw0 := w_pos n j ε₁ hnN hε
  have hzw : U7153.zz n ≤ w n ε₁ j := by
    unfold w
    exact le_mul_of_one_le_right hz0.le (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + ε₁))
  have hz100 : exp 100 ≤ U7153.zz n := by
    apply (le_log_iff_exp_le hz0).mp
    rw [U7153.zz, log_rpow hn0]
    linarith
  have h25 : (25 : ℝ) ≤ exp 100 := by linarith [add_one_le_exp (100 : ℝ)]
  have hw25 := h25.trans (hz100.trans hzw)
  have hwy := w_lt_y hnN hε hj
  have hwY : w n ε₁ j < min (U7153.yy n) ((1 + ε₁) * w n ε₁ j) := by
    apply lt_min hwy
    nlinarith
  have hquot : (n : ℝ) / U7153.yy n = (n : ℝ) ^ (2 / 3 : ℝ) := by
    unfold U7153.yy
    nth_rw 1 [← rpow_one (n : ℝ)]
    rw [← rpow_sub hn0]
    congr 1
    ring
  have hp100 : exp 100 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
    apply (le_log_iff_exp_le (rpow_pos_of_pos hn0 _)).mp
    rw [log_rpow hn0]
    linarith
  have hX25 : 25 ≤ (n : ℝ) / w n ε₁ j := by
    calc
      25 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := h25.trans hp100
      _ = (n : ℝ) / U7153.yy n := hquot.symm
      _ ≤ _ := div_le_div_of_nonneg_left hn0.le hw0 hwy.le
  refine ⟨hX25, hw25.trans hwY.le, hw25, hwY, ?_⟩
  exact (min_le_right _ _).trans (by nlinarith)

/-- Condition 25 puts D star above the Lemma 5 range, journal p. 1239. -/
theorem slice_Dstar_ge (α A u X : ℝ) (n : ℕ)
    (hα : 0 < α) (hα1 : α < 1 / 16) (hA : 0 < A)
    (hc : Cond25 α A u X) (hX : exp (exp 10) ≤ X) (hn : X ≤ (n : ℝ)) :
    1e8 ≤ √(n : ℝ) / log n ^ (A + 1) := by
  have hX1 : 1 < X := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hL : 0 < log (n : ℝ) := log_pos (by linarith)
  have hP : 0 < log (n : ℝ) ^ (A + 1) := rpow_pos_of_pos hL _
  have hc19 : Cond19 α A u X :=
    ⟨(le_max_left _ _).trans hc.1, hc.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
  have h19 := DecompC169b.cond19_at α A u X n hα hA hc19 hX1 hn
  have h := Journal.remark1_H hn1 (by linarith : α ≤ 1 / 2) hP hc.2.2.2.1 h19
  norm_num at h ⊢
  exact h

/-- The upper w guard required by the decreasing middle term of mbar,
journal p. 1240 after display 31. -/
theorem slice_w_le_sqrt_half (n j : ℕ) (ε₁ : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hj : j ∈ slices n ε₁) :
    w n ε₁ j ≤ √((n : ℝ) / 2) := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hnN : 0 < n := by exact_mod_cast hn0
  have hL := Lemma11C164.log_lower n hn
  have hy0 : 0 < U7153.yy n := rpow_pos_of_pos hn0 _
  have hy100 : exp 100 ≤ U7153.yy n := by
    apply (le_log_iff_exp_le hy0).mp
    rw [U7153.yy, log_rpow hn0]
    linarith
  have hy2 : 2 ≤ U7153.yy n := by linarith [add_one_le_exp (100 : ℝ)]
  have hy3 : (U7153.yy n) ^ (3 : ℕ) = (n : ℝ) := by
    rw [U7153.yy, ← rpow_natCast, ← rpow_mul hn0.le]
    norm_num
  have hsq : (U7153.yy n) ^ 2 ≤ (n : ℝ) / 2 := by
    nlinarith [mul_nonneg (sq_nonneg (U7153.yy n)) (sub_nonneg.mpr hy2)]
  exact (w_lt_y hnN hε hj).le.trans (le_sqrt_of_sq_le hsq)

end
end LeanLab.BS2022GRH.SliceRemainder236
#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_bilinear_basic_ranges
#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_Dstar_ge

#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_w_le_sqrt_half
