/-
AI wrote this Lean code. Binary Goldbach is open.
Source: Pintz and Ruzsa 2003 page 185 Corollaries 1 and 2, cited as 26 in P0024.
The cited bounds remain Props. Only their elementary transfer is proved here.
-/
import LeanLab.PlattTrudgian2014.LambdaThreshold

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Filter

def PowerLogBound (c lam : ℝ) (A : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
    (volume (bigSet N lam)).toReal ≤ C * (N : ℝ) ^ (-c) / (Lof N : ℝ) ^ A

def PRHalfInput : Prop := PowerLogBound (1 / 2) 0.7163435444776661 100

def PRThreeFifthsInput : Prop := PowerLogBound (3 / 5) 0.7894008449792309 100

theorem Lof_tendsto_atTop : Tendsto Lof atTop atTop := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.log 2) atTop atTop :=
    Tendsto.atTop_div_const hl (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_atTop.2
  intro M
  filter_upwards [hlog.eventually_ge_atTop (M : ℝ)] with N hN
  exact Nat.le_floor hN

theorem powerLogBound_unit (c : ℝ) (A : ℕ) : PowerLogBound c 1 A := by
  refine ⟨0, by norm_num, 2, fun N hN hN2 => ?_⟩
  simp [bigSet_one_empty]

/-- CONDITIONAL ON the supplied PowerLogBound. -/
theorem lambdaOK_of_powerLogBound {c lam : ℝ} {A : ℕ} (hA : 1 ≤ A)
    (h : PowerLogBound c lam A) : LambdaOK c lam := by
  obtain ⟨C, hC, N0, hbound⟩ := h
  obtain ⟨M, hM⟩ := exists_nat_gt (max C 1)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (Lof_tendsto_atTop.eventually_ge_atTop M)
  refine ⟨max N0 (max N1 2), fun N hN => ?_⟩
  have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
  have hNN1 : N1 ≤ N := (le_max_left N1 2).trans ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_right N1 2).trans ((le_max_right _ _).trans hN)
  have hLM : (M : ℝ) ≤ Lof N := by exact_mod_cast hN1 N hNN1
  have hCL : C < (Lof N : ℝ) := ((le_max_left C 1).trans_lt hM).trans_le hLM
  have hL1 : (1 : ℝ) ≤ Lof N := ((le_max_right C 1).trans hM.le).trans hLM
  have hpow : C < (Lof N : ℝ) ^ A :=
    hCL.trans_le (by simpa only [pow_one] using pow_le_pow_right₀ hL1 hA)
  have hden : (0 : ℝ) < (Lof N : ℝ) ^ A := pow_pos (by linarith) _
  have hfrac : C / (Lof N : ℝ) ^ A < 1 := (div_lt_one hden).mpr hpow
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ C * (N : ℝ) ^ (-c) / (Lof N : ℝ) ^ A := hbound N hN0 hN2
    _ = (C / (Lof N : ℝ) ^ A) * (N : ℝ) ^ (-c) := by ring
    _ < 1 * (N : ℝ) ^ (-c) := mul_lt_mul_of_pos_right hfrac (Real.rpow_pos_of_pos hNp _)
    _ = _ := one_mul _

theorem pr_half_constant_lt_pt : (0.7163435444776661 : ℝ) < 0.7163436 := by norm_num

/-- CONDITIONAL ON Pintz and Ruzsa Corollary 1 as the measure bound PRHalfInput. -/
theorem pt_lambda_GRH_of_pr (h : PRHalfInput) : LambdaOK (1 / 2) 0.7163436 := by
  apply lambdaOK_mono pr_half_constant_lt_pt.le
  exact lambdaOK_of_powerLogBound (by norm_num : 1 ≤ 100) h

/-- CONDITIONAL ON Pintz and Ruzsa Corollary 2 as PRThreeFifthsInput. -/
theorem pr_three_fifths_lambda (h : PRThreeFifthsInput) : LambdaOK (3 / 5) 0.7894008449792309 :=
  lambdaOK_of_powerLogBound (by norm_num : 1 ≤ 100) h

#print axioms Lof_tendsto_atTop
#print axioms powerLogBound_unit
#print axioms lambdaOK_of_powerLogBound
#print axioms pr_half_constant_lt_pt
#print axioms pt_lambda_GRH_of_pr
#print axioms pr_three_fifths_lambda

end LeanLab.PlattTrudgian2014
