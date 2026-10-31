/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 3 displays 4 and 5 and page 6 Section 3.
These bounds use LambdaOK, the existing repaired normalization.
The h = 1 method follows arXiv math/0201299 pages 29 to 30.
-/
import LeanLab.PlattTrudgian2014.LambdaDirections

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex Filter
open scoped Topology

/-- A strict exponential saving in L absorbs both a constant and the floor in log base 2. -/
theorem lambdaOK_of_exp_decay {c lam C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hgap : c * Real.log 2 < b)
    (hvol : ∀ N : ℕ, 2 ≤ N → (volume (bigSet N lam)).toReal ≤ C * Real.exp (-b * Lof N)) :
    LambdaOK c lam := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < b / Real.log 2 - c := by
    rw [sub_pos, lt_div_iff₀ hl]
    exact hgap
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    (ht.eventually_gt_atTop ((Real.log (C + 1) + b) / (b / Real.log 2 - c)))
  refine ⟨max N0 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlarge := (div_lt_iff₀ hd).mp (hN0 N ((le_max_left _ _).trans hN))
  have hf : Real.log (N : ℝ) / Real.log 2 < (Lof N : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloor := mul_le_mul_of_nonneg_left hf.le hb
  have he : Real.log (C + 1) + -b * Lof N < -c * Real.log N := by
    have heq : b * (Real.log (N : ℝ) / Real.log 2) =
        Real.log N * (b / Real.log 2) := by ring
    rw [heq] at hfloor
    nlinarith
  have hCe : C < Real.exp (Real.log (C + 1)) := by
    rw [Real.exp_log (by linarith)]
    linarith
  calc
    _ ≤ C * Real.exp (-b * Lof N) := hvol N hN2
    _ < Real.exp (Real.log (C + 1)) * Real.exp (-b * Lof N) :=
      mul_lt_mul_of_pos_right hCe (Real.exp_pos _)
    _ = Real.exp (Real.log (C + 1) + -b * Lof N) := (Real.exp_add _ _).symm
    _ < Real.exp (-c * Real.log N) := Real.exp_lt_exp.mpr he
    _ = (N : ℝ) ^ (-c) := by rw [Real.rpow_def_of_pos hNpos]; congr 1; ring

theorem lambdaOK_of_cosh {c lam a t : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hal : a < lam)
    (ht : 0 < t) (hgap : c * Real.log 2 < t * a - Real.log (Real.cosh t)) :
    LambdaOK c lam := by
  obtain ⟨C, hC, hvol⟩ := bigSet_exp_bound ha hal ht
  apply lambdaOK_of_exp_decay hC _ hgap hvol
  exact (mul_nonneg hc (Real.log_pos (by norm_num)).le).trans hgap.le

theorem log_cosh_log_four_upper :
    Real.log (Real.cosh (Real.log 4)) ≤ Real.log 2 + 0.06066 := by
  have hp : (17 / 16 : ℝ) ≤ (1 + 0.06066 / 64) ^ (64 : ℕ) := by norm_num
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 17 / 16) hp
  rw [Real.log_pow] at hm
  have hq := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 0.06066 / 64)
  have he : Real.log (Real.cosh (Real.log 4)) = Real.log 2 + Real.log (17 / 16) := by
    rw [Real.cosh_log (by norm_num : (0 : ℝ) < 4)]
    rw [show ((4 : ℝ) + 4⁻¹) / 2 = 2 * (17 / 16) by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  linarith

theorem log_cosh_log_four_lower :
    Real.log 2 + 1 / 17 ≤ Real.log (Real.cosh (Real.log 4)) := by
  have hq := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 17 / 16)
  rw [Real.cosh_log (by norm_num : (0 : ℝ) < 4)]
  rw [show ((4 : ℝ) + 4⁻¹) / 2 = 2 * (17 / 16) by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  norm_num at hq
  linarith

theorem h1_uncond_log_four_insufficient :
    Real.log 4 * 0.8594 - Real.log (Real.cosh (Real.log 4)) <
      (109 / 154 : ℝ) * Real.log 2 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hh := log_cosh_log_four_lower
  rw [hlog4] at hh ⊢
  have hl := Real.log_two_lt_d9
  have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

theorem h1_GRH_log_four_insufficient :
    Real.log 4 * 0.7163436 - Real.log (Real.cosh (Real.log 4)) <
      (1 / 2 : ℝ) * Real.log 2 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hh := log_cosh_log_four_lower
  rw [hlog4] at hh ⊢
  have hl := Real.log_two_lt_d9
  have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

#print axioms lambdaOK_of_exp_decay

#print axioms lambdaOK_of_cosh

#print axioms log_cosh_log_four_upper

#print axioms log_cosh_log_four_lower

#print axioms h1_uncond_log_four_insufficient

#print axioms h1_GRH_log_four_insufficient

end LeanLab.PlattTrudgian2014
