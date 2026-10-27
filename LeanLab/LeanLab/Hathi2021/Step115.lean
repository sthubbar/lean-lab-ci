/-
P0080 Hathi 2021, arXiv 2109.13174v3, pages 10 and 11.
Extend the existing x equal to 37 check to the full scalar range x at least 37.
The separate Rosser and Schoenfeld estimate remains cited.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Step37

open Real

namespace LeanLab.Hathi2021.Step115

/-- Pages 10 and 11, the scalar 1.12 step, for every x at least 37.
The paper uses this step on the smaller interval from 37 to 99. -/
theorem step_112_all (x : ℝ) (hx : 37 ≤ x) :
    exp eulerMascheroniConstant * log (112 / 100 * log 2) +
      25064 / 10000 / (2 * log (x / 2) + log (112 / 100 * log 2)) < 0 := by
  have htwo : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht : (1 / 2 : ℝ) ≤ 112 / 100 * log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogt := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) ht
  rw [one_div, Real.log_inv] at hlogt
  have h37 : log (2 : ℝ) ≤ log (37 / 2) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hD : 0 < 2 * log (37 / 2) + log (112 / 100 * log 2) := by linarith
  have hmono : log (37 / 2 : ℝ) ≤ log (x / 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hterm : 25064 / 10000 / (2 * log (x / 2) + log (112 / 100 * log 2)) ≤
      25064 / 10000 / (2 * log (37 / 2) + log (112 / 100 * log 2)) :=
    div_le_div_of_nonneg_left (by norm_num) hD (by linarith)
  linarith [Step37.step_112]

/-- Page 10, the explicit Rosser and Schoenfeld upper-bound expression. -/
noncomputable def u (d : ℝ) : ℝ :=
  exp eulerMascheroniConstant * log (log d) + 25064 / 10000 / log (log d)

/-- Pages 10 and 11, the full scalar u step at the 1.12 exponent. -/
theorem u_step_112 (x : ℝ) (hx : 37 ≤ x) :
    u ((2 : ℝ) ^ ((112 / 100 : ℝ) * (x / 2) ^ 2)) <
      2 * exp eulerMascheroniConstant * log (x / 2) := by
  have hy : 0 < x / 2 := by linarith
  have ht : (0 : ℝ) < 112 / 100 * log 2 := by
    apply mul_pos (by norm_num)
    exact Real.log_pos (by norm_num)
  have hlogs : log (log ((2 : ℝ) ^ ((112 / 100 : ℝ) * (x / 2) ^ 2))) =
      2 * log (x / 2) + log (112 / 100 * log 2) := by
    rw [Real.log_rpow (by norm_num)]
    rw [show (112 / 100 * (x / 2) ^ 2) * log 2 =
      (112 / 100 * log 2) * (x / 2) ^ 2 by ring]
    rw [Real.log_mul ht.ne' (pow_ne_zero 2 hy.ne'), Real.log_pow]
    ring
  simp only [u, hlogs]
  have h := step_112_all x hx
  nlinarith

/-- Page 10, u is strictly increasing for real arguments at least 30. -/
theorem u_strictMonoOn : StrictMonoOn u (Set.Ici 30) := by
  let E := exp eulerMascheroniConstant
  let c : ℝ := 25064 / 10000
  have hE : (7 / 4 : ℝ) ≤ E := by
    have hγ := LeanLab.ChenExplicit.Gamma.gamma_gt
    have hs := Real.sum_le_exp_of_nonneg (x := (0.57720 : ℝ)) (by norm_num) 4
    have hm : exp (0.57720 : ℝ) ≤ E := Real.exp_le_exp.mpr hγ.le
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hs
    norm_num at hs
    linarith
  have hloglog30 : (6 / 5 : ℝ) ≤ log (log 30) := by
    have hp : (2 : ℝ) ^ 49 ≤ (30 : ℝ) ^ 10 := by norm_num
    have hl := Real.log_le_log (by positivity) hp
    rw [Real.log_pow, Real.log_pow] at hl
    have h30 : (339 / 100 : ℝ) < log 30 := by
      have := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have he : exp (6 / 5 : ℝ) ≤ 339 / 100 := by
      have hsmall : exp (3 / 100 : ℝ) ≤ 100 / 97 := by
        have h := Real.exp_bound_div_one_sub_of_interval
          (by norm_num : (0 : ℝ) ≤ 3 / 100) (by norm_num : (3 / 100 : ℝ) < 1)
        norm_num at h
        exact h
      calc
        exp (6 / 5 : ℝ) = exp (3 / 100 : ℝ) ^ 40 := by
          rw [← Real.exp_nat_mul]
          congr 1
          norm_num
        _ ≤ (100 / 97 : ℝ) ^ 40 := pow_le_pow_left₀ (Real.exp_pos _).le hsmall 40
        _ ≤ 339 / 100 := by norm_num
    have h := Real.log_le_log (Real.exp_pos _) (he.trans h30.le)
    rw [Real.log_exp] at h
    exact h
  intro a ha b hb hab
  change 30 ≤ a at ha
  change 30 ≤ b at hb
  let y₁ := log (log a)
  let y₂ := log (log b)
  have h₁ : (6 / 5 : ℝ) ≤ y₁ := by
    apply hloglog30.trans
    apply Real.log_le_log (Real.log_pos (by norm_num))
    exact Real.log_le_log (by norm_num) ha
  have h₂ : (6 / 5 : ℝ) ≤ y₂ := by
    apply hloglog30.trans
    apply Real.log_le_log (Real.log_pos (by norm_num))
    exact Real.log_le_log (by norm_num) hb
  have h₁p : 0 < y₁ := by linarith
  have h₂p : 0 < y₂ := by linarith
  have h12 : y₁ < y₂ := by
    apply Real.log_lt_log
    · exact Real.log_pos (by linarith [ha])
    · exact Real.log_lt_log (by linarith [ha]) hab
  have hyy : (36 / 25 : ℝ) ≤ y₁ * y₂ := by
    have h := mul_le_mul h₁ h₂ (by norm_num : (0 : ℝ) ≤ 6 / 5) h₁p.le
    norm_num at h
    exact h
  have hc : c < E * (y₁ * y₂) := by
    calc
      c < (7 / 4 : ℝ) * (36 / 25) := by norm_num [c]
      _ ≤ E * (y₁ * y₂) := mul_le_mul hE hyy (by norm_num) (by linarith)
  have hdiv : c / (y₁ * y₂) < E := (div_lt_iff₀ (mul_pos h₁p h₂p)).mpr hc
  have hm := mul_lt_mul_of_pos_right hdiv (sub_pos.mpr h12)
  have hid : c / y₁ - c / y₂ = c / (y₁ * y₂) * (y₂ - y₁) := by
    field_simp [h₁p.ne', h₂p.ne']
  rw [← hid] at hm
  change E * y₁ + c / y₁ < E * y₂ + c / y₂
  nlinarith

/-- Page 10, the full scalar u step at the 1.06 exponent. -/
theorem u_step_106 (x : ℝ) (hx : 37 ≤ x) :
    u ((2 : ℝ) ^ ((106 / 100 : ℝ) * (x / 2) ^ 2)) <
      2 * exp eulerMascheroniConstant * log (x / 2) := by
  have hy : (37 / 2 : ℝ) ≤ x / 2 := by linarith
  have he : (5 : ℝ) ≤ 106 / 100 * (x / 2) ^ 2 := by
    nlinarith [sq_nonneg (x / 2 - 37 / 2)]
  have hlo : (30 : ℝ) ≤ (2 : ℝ) ^ ((106 / 100 : ℝ) * (x / 2) ^ 2) := by
    calc
      (30 : ℝ) ≤ (2 : ℝ) ^ (5 : ℝ) := by norm_num [Real.rpow_ofNat]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
  have harg : (2 : ℝ) ^ ((106 / 100 : ℝ) * (x / 2) ^ 2) ≤
      (2 : ℝ) ^ ((112 / 100 : ℝ) * (x / 2) ^ 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [sq_nonneg (x / 2)]
  have hm := u_strictMonoOn.monotoneOn hlo (hlo.trans harg) harg
  exact hm.trans_lt (u_step_112 x hx)

end LeanLab.Hathi2021.Step115
