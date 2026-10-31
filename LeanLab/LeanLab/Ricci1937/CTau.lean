import Mathlib

/-!
Ricci 1937, page 79, formulas 2.3 and 2.4. The lower sieve parameters.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Real Finset
noncomputable section

/-- The value of tau at the parameters in formula 2.3. -/
def ricciTau (f : ℝ) : ℝ :=
  exp (-0.90 / f) + exp (-1.46 / f) + exp (-1.98 / f) / (1 - exp (-0.50 / f))

/-- A finite Taylor lower estimate for exp. -/
lemma ricci_exp_lower {x r : ℝ} (hx : 0 ≤ x)
    (hr : r ≤ ∑ i ∈ range 12, x ^ i / (i.factorial : ℝ)) : r ≤ exp x :=
  hr.trans (Real.sum_le_exp_of_nonneg hx 12)

/-- A positive Taylor lower bound for exp gives an upper bound for exp of the negative. -/
lemma ricci_exp_neg_upper {x r : ℝ} (hr : 0 < r) (h : r ≤ exp x) : exp (-x) ≤ 1 / r := by
  rw [exp_neg, one_div]
  exact inv_anti₀ hr h

/-- Formula 2.4: tau at f = 1 is less than 0.9898. -/
theorem ricciTau_one_lt : ricciTau 1 < 0.9898 := by
  have h09 : exp (-0.9) ≤ 1 / 2.4596 := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h146 : exp (-1.46) ≤ 1 / 4.3055 := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h198 : exp (-1.98) ≤ 1 / 7.2427 := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h05 : exp (-0.5) ≤ 1 / 1.6487 := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have hden : 0 < 1 - exp (-0.5) := by linarith
  have htail : exp (-1.98) / (1 - exp (-0.5)) ≤
      (1 / 7.2427 : ℝ) / (1 - 1 / 1.6487) :=
    div_le_div₀ (by positivity) h198 (by norm_num) (by linarith)
  norm_num [ricciTau] at *
  linarith

/-- The exponent identity in the lower error term on page 83. -/
lemma c2_error_exponent_identity {g s τ ε : ℝ} (hs : s ≠ 0) :
    g / s + ((s - g) / (2 * s)) * (2 * τ + ε) =
      1 - (1 - τ - ε / 2) * (1 - g / s) := by
  field_simp
  ring

/-- Page 83: the relative gap from g to s has a uniform lower bound. -/
lemma c2_ratio_gap {g s : ℕ} (hsg : g < s) :
    1 / ((g : ℝ) + 1) ≤ 1 - (g : ℝ) / s := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hsgR : (g : ℝ) + 1 ≤ s := by exact_mod_cast hsg
  rw [one_sub_div hspos.ne']
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (g : ℝ) + 1) hspos).mpr
  nlinarith [show (0 : ℝ) ≤ g by positivity]

/-- An explicit positive power saving in page 83, with epsilon = 1/100. -/
theorem c2_error_margin {g s : ℕ} (hsg : g < s) :
    (0.0052 : ℝ) / ((g : ℝ) + 1) <
      (1 - ricciTau 1 - (0.01 : ℝ) / 2) * (1 - (g : ℝ) / s) := by
  have hgap := c2_ratio_gap hsg
  have hgp : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  have hratio : 0 < 1 - (g : ℝ) / s :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ((g : ℝ) + 1)) hgap
  have htau := ricciTau_one_lt
  have hbase : (0.0052 : ℝ) < 1 - ricciTau 1 - (0.01 : ℝ) / 2 := by linarith
  calc
    (0.0052 : ℝ) / ((g : ℝ) + 1) =
        (0.0052 : ℝ) * (1 / ((g : ℝ) + 1)) := by ring
    _ ≤ (0.0052 : ℝ) * (1 - (g : ℝ) / s) := by gcongr
    _ < (1 - ricciTau 1 - (0.01 : ℝ) / 2) * (1 - (g : ℝ) / s) :=
      mul_lt_mul_of_pos_right hbase hratio

example : (0.0052 : ℝ) / (1 + 1) <
    (1 - ricciTau 1 - (0.01 : ℝ) / 2) * (1 - (1 : ℝ) / 3) := by
  simpa using c2_error_margin (g := 1) (s := 3) (by norm_num)

end
end LeanLab.Ricci1937
