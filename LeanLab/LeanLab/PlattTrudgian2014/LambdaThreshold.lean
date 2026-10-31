/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 3 display 5.
The infimum uses LambdaOK with the existing repaired normalization.
No assertion of attainment is made.
-/
import LeanLab.PlattTrudgian2014.LambdaWeak

namespace LeanLab.PlattTrudgian2014

open MeasureTheory

noncomputable def lambdaThreshold (c : ℝ) : ℝ :=
  sInf {lam : ℝ | 0 ≤ lam ∧ LambdaOK c lam}

theorem bigSet_one_empty (N : ℕ) : bigSet N 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hn := norm_G_le (Lof N) x
  have hh := hx.2
  simp only [one_mul] at hh
  exact (not_lt_of_ge hn) hh

theorem lambdaOK_one (c : ℝ) : LambdaOK c 1 := by
  refine ⟨1, fun N hN => ?_⟩
  rw [bigSet_one_empty]
  simp only [measure_empty, ENNReal.toReal_zero]
  exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _

theorem lambdaThreshold_nonneg (c : ℝ) : 0 ≤ lambdaThreshold c := by
  apply le_csInf (s := {lam : ℝ | 0 ≤ lam ∧ LambdaOK c lam})
  · exact ⟨1, by norm_num, lambdaOK_one c⟩
  · exact fun _ h => h.1

theorem lambdaThreshold_le {c lam : ℝ} (hl : 0 ≤ lam) (h : LambdaOK c lam) :
    lambdaThreshold c ≤ lam := by
  exact csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hl, h⟩

theorem lambdaThreshold_le_one (c : ℝ) : lambdaThreshold c ≤ 1 :=
  lambdaThreshold_le (by norm_num) (lambdaOK_one c)

theorem lambdaThreshold_mono {c c' : ℝ} (hc : c ≤ c') :
    lambdaThreshold c ≤ lambdaThreshold c' := by
  apply le_csInf (s := {lam : ℝ | 0 ≤ lam ∧ LambdaOK c' lam})
  · exact ⟨1, by norm_num, lambdaOK_one c'⟩
  · intro lam h
    exact lambdaThreshold_le h.1 (lambdaOK_c_mono hc h.2)

theorem lambdaThreshold_uncond_h1 : lambdaThreshold (109 / 154) ≤ 0.8977 :=
  lambdaThreshold_le (by norm_num) pt_lambda_uncond_h1

theorem lambdaThreshold_GRH_h1 : lambdaThreshold (1 / 2) ≤ 0.7938 :=
  lambdaThreshold_le (by norm_num) pt_lambda_GRH_h1

#print axioms bigSet_one_empty
#print axioms lambdaOK_one
#print axioms lambdaThreshold_nonneg
#print axioms lambdaThreshold_le
#print axioms lambdaThreshold_le_one
#print axioms lambdaThreshold_mono
#print axioms lambdaThreshold_uncond_h1
#print axioms lambdaThreshold_GRH_h1

end LeanLab.PlattTrudgian2014
