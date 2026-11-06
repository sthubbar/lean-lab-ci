/- AI wrote this Lean code for CODEX task406. Goldbach is open.
Source: Ramare 2019 pp. 155, 156, 169. https://doi.org/10.4064/bc118-10 -/
import LeanLab.BS2022GRH.PaperInputs148

namespace LeanLab.BS2022GRH.PhiBridge406
open Real Finset ChenThresholdGRH
noncomputable section

/-- Journal p. 1216 Lemma 5. Algebraic form of its printed error. -/
theorem mphi_error_identity (x : ℝ) (hx : 1 < x) :
    Mphi x * log x = log x + 1.333 +
      min (2.44 / √x) (11 / (√x * log x)) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlog := log_pos hx
  have hroot : 0 < √x := sqrt_pos.mpr hx0
  have ha : 2.44 / (√x * log x) * log x = 2.44 / √x := by
    field_simp [hlog.ne', hroot.ne']
  have hb : 11 / (√x * log x ^ 2) * log x = 11 / (√x * log x) := by
    field_simp [hlog.ne', hroot.ne']
  unfold Mphi
  rw [add_mul, add_mul, one_mul, div_mul_cancel₀ _ hlog.ne',
    min_mul_of_nonneg _ _ hlog.le, ha, hb]

/-- Ramare p. 169 Lemma 9.3 error is below both journal p. 1216 branches. -/
theorem finite_error_le_printed_min (x : ℝ) (hx : 1 < x) :
    2.2 / x ^ (3 / 4 : ℝ) ≤ min (2.44 / √x) (11 / (√x * log x)) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hr : 0 < √x := sqrt_pos.mpr hx0
  have hl := log_pos hx
  have hq : 0 < x ^ (1 / 4 : ℝ) := rpow_pos_of_pos hx0 _
  have hq1 : 1 ≤ x ^ (1 / 4 : ℝ) := one_le_rpow hx.le (by norm_num)
  have hp : x ^ (3 / 4 : ℝ) = √x * x ^ (1 / 4 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_add hx0]
    norm_num
  have hlog := log_le_sub_one_of_pos hq
  rw [log_rpow hx0] at hlog
  rw [hp]
  apply le_min
  · apply (div_le_div_iff₀ (mul_pos hr hq) hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq1 hr.le]
  · apply (div_le_div_iff₀ (mul_pos hr hq) (mul_pos hr hl)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog hr.le]

/-- Ramare p. 155 constant rounding absorbs the coarse p. 156 error above this cutoff. -/
theorem coarse_error_absorbed (x : ℝ) (hx : 1e8 ≤ x) :
    (1.3326 : ℝ) + 2.44 / √x ≤ 1.333 := by
  have hr : (10000 : ℝ) ≤ √x := by
    apply (le_sqrt (by norm_num) (by linarith : 0 ≤ x)).mpr
    norm_num at hx ⊢
    exact hx
  have he : 2.44 / √x ≤ (2.44 : ℝ) / 10000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr
  linarith

/-- CONDITIONAL ON Ramare p. 155 constant, p. 169 Lemma 9.3 and p. 156 coarse error.
This proves the exact journal p. 1216 Lemma 5 second estimate from those inputs. -/
theorem lemma5_phi_of_ramare (C : ℝ) (hC : C ≤ 1.3326)
    (hfinite : ∀ x : ℝ, 1 ≤ x → x ≤ 2e9 →
      |(∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n), (1 : ℝ) / n.totient)
        - log x - C| ≤ 2.2 / x ^ (3 / 4 : ℝ))
    (hcoarse : ∀ x : ℝ, 1 < x →
      |(∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n), (1 : ℝ) / n.totient)
        - log x - C| ≤ 2.44 / √x) : PaperInputs148.Lemma5PhiJ := by
  intro x hx
  rw [mphi_error_identity x hx]
  by_cases hsmall : x ≤ 1e8
  · have he := (abs_le.mp (hfinite x hx.le (by linarith))).2
    have hb := finite_error_le_printed_min x hx
    linarith
  · have he := (abs_le.mp (hcoarse x hx)).2
    have hb := coarse_error_absorbed x (le_of_lt (lt_of_not_ge hsmall))
    have hl : 0 ≤ log x := (log_pos hx).le
    have hm : 0 ≤ min (2.44 / √x) (11 / (√x * log x)) := by
      apply le_min <;> positivity
    linarith

end
end LeanLab.BS2022GRH.PhiBridge406
#print axioms LeanLab.BS2022GRH.PhiBridge406.mphi_error_identity
#print axioms LeanLab.BS2022GRH.PhiBridge406.finite_error_le_printed_min
#print axioms LeanLab.BS2022GRH.PhiBridge406.coarse_error_absorbed
#print axioms LeanLab.BS2022GRH.PhiBridge406.lemma5_phi_of_ramare
