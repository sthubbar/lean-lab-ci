import LeanLab.Ricci1937.CTau

/-!
Ricci 1937, page 79, the remaining lower sieve tau values in formula 2.4.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Real Finset
noncomputable section

/-- Page 79, formula 2.4, at f = 2. -/
theorem ricciTau_two_lt : ricciTau 2 < 2.7994 := by
  have h0 : exp (-(9 / 20 : ℝ)) ≤ 1 / (313662437 / 200000000 : ℝ) := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h1 : exp (-(73 / 100 : ℝ)) ≤ 1 / (2075080607 / 1000000000 : ℝ) := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h2 : exp (-(99 / 100 : ℝ)) ≤ 1 / (269123447 / 100000000 : ℝ) := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h3 : exp (-(1 / 4 : ℝ)) ≤ 1 / (160503177 / 125000000 : ℝ) := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have htail : exp (-(99 / 100 : ℝ)) /
      (1 - exp (-(1 / 4 : ℝ))) ≤
      (1 / (269123447 / 100000000 : ℝ)) / (1 - 1 / (160503177 / 125000000 : ℝ)) :=
    div_le_div₀ (by positivity) h2 (by norm_num) (by linarith)
  norm_num [ricciTau] at *
  linarith

/-- Page 79, formula 2.4, at f = 3. -/
theorem ricciTau_three_lt : ricciTau 3 < 4.7223 := by
  have h0 : exp (-(3 / 10 : ℝ)) ≤ 1 / (1349858807 / 1000000000 : ℝ) := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h1 : exp (-(73 / 150 : ℝ)) ≤ 1 / (12710033 / 7812500 : ℝ) := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h2 : exp (-(33 / 50 : ℝ)) ≤ 1 / (967396167 / 500000000 : ℝ) := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h3 : exp (-(1 / 6 : ℝ)) ≤ 1 / (295340103 / 250000000 : ℝ) := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have htail : exp (-(33 / 50 : ℝ)) /
      (1 - exp (-(1 / 6 : ℝ))) ≤
      (1 / (967396167 / 500000000 : ℝ)) / (1 - 1 / (295340103 / 250000000 : ℝ)) :=
    div_le_div₀ (by positivity) h2 (by norm_num) (by linarith)
  norm_num [ricciTau] at *
  linarith

/-- A Taylor upper estimate on the unit interval, used for condition 1.5. -/
lemma ricci_exp_upper_small {x r : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hr : ∑ i ∈ range 10, x ^ i / (i.factorial : ℝ) +
      x ^ 10 * ((11 : ℝ) / ((Nat.factorial 10 : ℝ) * 10)) ≤ r) : exp x ≤ r := by
  have h := Real.exp_bound (x := x) (by rw [abs_le]; constructor <;> linarith)
    (n := 10) (by norm_num)
  rw [abs_of_nonneg hx0] at h
  have hu := (abs_le.mp h).2
  linarith

/-- Page 78, condition 1.5, throughout the two printed choices of theta. -/
theorem ricci_theta_admissible {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 0.532) :
    exp t * (t * exp 1 / 2) ^ 2 < 1 ∧ 1 < exp t := by
  have h06 : exp (0.6 : ℝ) ≤ 1.83 := ricci_exp_upper_small (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial])
  have he : exp t ≤ 1.83 := (exp_le_exp.mpr (by linarith : t ≤ 0.6)).trans h06
  have he1 : exp 1 ≤ (2.719 : ℝ) := le_of_lt (by linarith [exp_one_lt_d9])
  have hprod := mul_le_mul ht he1 (exp_pos 1).le (by norm_num : (0 : ℝ) ≤ 0.532)
  have hu : t * exp 1 / 2 ≤ 0.724 := by linarith
  have hu0 : 0 ≤ t * exp 1 / 2 := by positivity
  have hsq := pow_le_pow_left₀ hu0 hu 2
  have hmul := mul_le_mul he hsq (sq_nonneg (t * exp 1 / 2)) (by norm_num : (0 : ℝ) ≤ 1.83)
  exact ⟨lt_of_le_of_lt hmul (by norm_num), one_lt_exp_iff.mpr ht0⟩

example : exp (0.5 : ℝ) * (0.5 * exp 1 / 2) ^ 2 < 1 ∧ 1 < exp (0.5 : ℝ) :=
  ricci_theta_admissible (by norm_num) (by norm_num)

example : exp (0.532 : ℝ) * (0.532 * exp 1 / 2) ^ 2 < 1 ∧ 1 < exp (0.532 : ℝ) :=
  ricci_theta_admissible (by norm_num) le_rfl

end
end LeanLab.Ricci1937
