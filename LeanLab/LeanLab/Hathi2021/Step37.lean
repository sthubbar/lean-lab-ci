/-
P0080 Hathi 2021, arXiv 2109.13174v3, pages 10 to 11, the step behind `c₃'` in (3.7): with
`u(d) = e^γ log log d + 2.5064/log log d`, `u(2^{1.12 y²}) ≤ 2 e^γ log y` for `y = x/2 ≥ 18.5`,
which reduces to `e^γ log(1.12 log 2) + 2.5064/(2 log y + log(1.12 log 2)) ≤ 0`.
At `y = 18.5`, that is `x = 37`, the left side is about -0.00195, so the step holds, but only just;
at `y = 18`, the bound written in the `1.06` case, it would be +0.0025. Python, PROGRESS.md.
Unit U-6158, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.GammaBounds

namespace LeanLab.Hathi2021.Step37
open Real Finset

/-- **The tight step at `x = 37`.** -/
theorem step_112 :
    exp eulerMascheroniConstant * log (112 / 100 * log 2) +
      25064 / 10000 / (2 * log (37 / 2) + log (112 / 100 * log 2)) < 0 := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  set t := 112 / 100 * log 2 with ht
  have ht1 : 112 / 100 * (0.6931471803 : ℝ) < t := by rw [ht]; linarith
  have ht2 : t < 112 / 100 * (0.6931471808 : ℝ) := by rw [ht]; linarith
  have ht0 : 0 < t := by linarith
  set z := (1 - t) / (1 + t) with hz
  have hz0 : 0 < z := by rw [hz]; apply div_pos <;> linarith
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  have hlog : log t = -(log (1 + z) - log (1 - z)) := by
    have h1 : 1 + z = 2 / (1 + t) := by rw [hz]; field_simp; ring
    have h2 : 1 - z = 2 * t / (1 + t) := by rw [hz]; field_simp; ring
    rw [h1, h2, Real.log_div (by norm_num) (by linarith), Real.log_div (by positivity) (by linarith),
      Real.log_mul (by norm_num) ht0.ne']
    ring
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one (x := z) (by rw [abs_of_pos hz0]; exact hz1)
  set S := log (1 + z) - log (1 - z) with hSdef
  -- lower bound by two terms
  have hSlo : 2 * z + 2 * (1 / 3) * z ^ 3 ≤ S := by
    have := sum_le_hasSum (range 2) (fun k _ => by positivity) hS
    simp only [sum_range_succ, sum_range_zero] at this
    norm_num at this ⊢
    linarith
  -- upper bound by the geometric series
  have hSup : S ≤ 2 * z * (1 - z ^ 2)⁻¹ := by
    have hg := (hasSum_geometric_of_lt_one (r := z ^ 2) (by positivity)
      (by nlinarith)).mul_left (2 * z)
    refine hasSum_le (fun k => ?_) hS hg
    have hk : (0 : ℝ) < 2 * k + 1 := by positivity
    have : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by rw [div_le_one hk]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hp : (0 : ℝ) ≤ z ^ (2 * k + 1) := by positivity
    calc 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1) ≤ 2 * 1 * z ^ (2 * k + 1) := by
          gcongr
      _ = 2 * z * (z ^ 2) ^ k := by ring
  -- bounds on z from the bounds on t
  have hzlo : (1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ)) ≤ z := by
    rw [hz, div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  have hzhi : z ≤ (1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ)) := by
    rw [hz, div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have hzl0 : 0 < ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) := by norm_num
  have hSlo' : 2 * ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) + 2 * (1 / 3) * ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) ^ 3 ≤ S := by
    have : ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) ^ 3 ≤ z ^ 3 := pow_le_pow_left₀ hzl0.le hzlo 3
    linarith
  have hzh1 : ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) < 1 := by norm_num
  have hSup' : S ≤ 2 * ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) * (1 - ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) ^ 2)⁻¹ := by
    have hz2 : z ^ 2 ≤ ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) ^ 2 := pow_le_pow_left₀ hz0.le hzhi 2
    have hzh2 : ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) ^ 2 < 1 := by nlinarith [hzl0]
    have h1 : (1 - z ^ 2)⁻¹ ≤ (1 - ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) ^ 2)⁻¹ := by
      apply inv_anti₀ (by linarith) (by linarith)
    have h2 : 0 ≤ (1 - z ^ 2)⁻¹ := inv_nonneg.mpr (by nlinarith)
    calc S ≤ 2 * z * (1 - z ^ 2)⁻¹ := hSup
      _ ≤ 2 * ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) * (1 - ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) ^ 2)⁻¹ := by
          apply mul_le_mul (by linarith) h1 h2 (by nlinarith)
  -- log 18.5 ≥ 4.209 log 2
  have h18 : (4209 / 1000 : ℝ) * log 2 ≤ log (37 / 2) := by
    have hn : (2 : ℕ) ^ 5209 ≤ 37 ^ 1000 := by decide +kernel
    have hpow : (2 : ℝ) ^ 4209 ≤ (37 / 2) ^ 1000 := by
      rw [div_pow, le_div_iff₀ (by positivity), ← pow_add]
      exact_mod_cast hn
    have := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  -- e^γ ≥ 1.781
  have hg : (1.781 : ℝ) ≤ exp eulerMascheroniConstant := by
    have hγ := LeanLab.ChenExplicit.Gamma.gamma_gt
    have h := Real.sum_le_exp_of_nonneg (x := (0.57720 : ℝ)) (by norm_num) 7
    have h2 : exp (0.57720 : ℝ) ≤ exp eulerMascheroniConstant := exp_le_exp.mpr hγ.le
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith
  -- assemble
  rw [hlog]
  have hDlo : 2 * ((4209 / 1000) * 0.6931471803) - (2 * ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) * (1 - ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) ^ 2)⁻¹) ≤ 2 * log (37 / 2) + -S := by
    nlinarith
  have hDpos : (0 : ℝ) < 2 * ((4209 / 1000) * 0.6931471803) - (2 * ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) * (1 - ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) ^ 2)⁻¹) := by
    norm_num
  have hterm : 25064 / 10000 / (2 * log (37 / 2) + -S) ≤
      25064 / 10000 / (2 * ((4209 / 1000) * 0.6931471803) - (2 * ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) * (1 - ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) ^ 2)⁻¹)) :=
    div_le_div_of_nonneg_left (by norm_num) hDpos hDlo
  have hSlo0 : 0 < (2 * ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) + 2 * (1 / 3) * ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) ^ 3) := by positivity
  have hfirst : exp eulerMascheroniConstant * -S ≤ 1.781 * -(2 * ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) + 2 * (1 / 3) * ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) ^ 3) := by nlinarith
  have hnum : (1.781 : ℝ) * -(2 * ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) + 2 * (1 / 3) * ((1 - (112 / 100 * 0.6931471808 : ℝ)) / (1 + (112 / 100 * 0.6931471808 : ℝ))) ^ 3) + 25064 / 10000 / (2 * ((4209 / 1000) * 0.6931471803) - (2 * ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) * (1 - ((1 - (112 / 100 * 0.6931471803 : ℝ)) / (1 + (112 / 100 * 0.6931471803 : ℝ))) ^ 2)⁻¹)) < 0 := by
    norm_num
  linarith

end LeanLab.Hathi2021.Step37
