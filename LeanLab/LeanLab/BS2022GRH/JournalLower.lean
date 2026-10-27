/-
P0021, T2 FRONTIER: the journal version's own Section 5.4 argument, re-run at better parameters,
lowers the GRH Chen threshold from exp(exp 14) to exp(exp 13.45).

Bordignon-Starichkova, Ramanujan J. 64 (2024), choose u = 1000 and α₁ = α₂ = α₃ = 10⁻³. Their
Theorems 5, 6, 7 allow any 400 ≤ u ≤ 10⁸, α₁ < 1/8, α₂ < 1/24, α₃ < 1/16, and need
log X₂ ≥ (A + 1)/αᵢ and X₂^{αᵢ}/log^{A+1} X₂ ≥ e^u, display (19), (21), (25). At u = 1500,
α = 0.0024, A = 10:
* ε(1500) = 1/8349.33 < 1/8349 by display (6), Python only, numerics/journal54_U1166.py;
  Table 1 row ε⁻¹ = 6100 gives C₁ = 112, C₂ = 114;
* the main-term constant K3J(0.0024, e^γ, 1/8349, 112, 114, c̄) > 0.0042 > 4·10⁻³, PROVED below,
  true value 0.00518;
* α log X₂ − 11 log log X₂ ≥ 1500 at log log X₂ = 13.45, PROVED below, since e^{13.45} ≥ 686646;
  the other conditions are far weaker.
So GRH and the journal's Theorems 5 to 7 and Lemma 9, at these parameters, give
π₂(N) > 4·10⁻³ U_N N/log² N for N ≥ exp(exp 13.45). CONDITIONAL ON GRH and those cited results;
a re-optimisation of the authors' own parameters, MODEL in the choice only. Python scan:
u = 1650 gives 13.42, the optimum of this argument with constant 4·10⁻³; 13.37 if only K > 0 is
asked.

AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1168, files first named U1166 before the id clash. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.JournalMargin

namespace LeanLab.BS2022GRH.Journal
open Real

lemma log29808_ge : (1.09219 : ℝ) ≤ log (3 - 8 * 0.0024) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have e : (1.09219 : ℝ) = 1 + 0.09219 := by norm_num
  rw [e, exp_add]
  have h1 := Real.exp_one_lt_d9
  have h2 : exp (0.09219 : ℝ) ≤ 1.0965734 := by
    have h := Real.exp_bound' (x := (0.09219 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  calc exp 1 * exp 0.09219 ≤ 2.7182818286 * 1.0965734 := by gcongr
    _ ≤ 3 - 8 * 0.0024 := by norm_num

lemma exp19808_le : exp (8 * 0.0024 - 2 : ℝ) ≤ 0.13796 := by
  have h2 : (7.24852 : ℝ) ≤ exp 1.9808 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1.9808 : ℝ)) (by norm_num) 18
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have e : (8 * 0.0024 - 2 : ℝ) = -1.9808 := by norm_num
  rw [e, exp_neg]
  have : (exp 1.9808)⁻¹ ≤ (7.24852 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
  have : (7.24852 : ℝ)⁻¹ ≤ 0.13796 := by norm_num
  linarith

lemma logr24_le : log ((3 - 8 * 0.0024) / (3 - 18 * 0.0024) : ℝ) ≤ 0.0081169 := by
  refine le_trans (Real.log_le_sub_one_of_pos (by norm_num)) ?_
  norm_num

/-- **The main-term margin at u = 1500, α = 0.0024**: K3J > 0.0042 > 4·10⁻³. -/
theorem theorem3_lower_main :
    (0.0042 : ℝ) < K3J 0.0024 (exp eulerMascheroniConstant) (1 / 8349) 112 114
      LeanLab.ChenExplicit.BJS.cbar := by
  obtain ⟨hg1, hg2⟩ := g_bounds
  have hc := LeanLab.ChenExplicit.BJS.cbar_lt
  have hc0 := LeanLab.ChenExplicit.BJS.cbar_gt
  have hl3 := log29808_ge
  have he := exp19808_le
  have hl6 := log6_le
  have hl83 := log83_le
  have hlr := logr24_le
  have hl83' : 0 ≤ log (8 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have hr0 : 0 ≤ log ((3 - 8 * 0.0024) / (3 - 18 * 0.0024) : ℝ) := Real.log_nonneg (by norm_num)
  have hl60 : 0 ≤ log (6 : ℝ) := Real.log_nonneg (by norm_num)
  set g := exp eulerMascheroniConstant
  set cb := LeanLab.ChenExplicit.BJS.cbar
  set r := log ((3 - 8 * 0.0024) / (3 - 18 * 0.0024) : ℝ)
  have hg0 : 0 ≤ g := (exp_pos _).le
  have hl30 : 0 ≤ log (3 - 8 * 0.0024 : ℝ) := by linarith
  have T1 : 1.78103 * 1.09219 ≤ g * log (3 - 8 * 0.0024 : ℝ) :=
    mul_le_mul hg1 hl3 (by norm_num) hg0
  have T3 : g * (log 6 + r) ≤ 1.781081 * (1.79176 + 0.0081169) :=
    mul_le_mul hg2 (add_le_add hl6 hlr) (by linarith) (by norm_num)
  have T4 : (2 * g / (1 / 2 - 0.0024) + 3 * (1 / 8349) * 112) * cb ≤
      (2 * 1.781081 / (1 / 2 - 0.0024) + 3 * (1 / 8349) * 112) * 0.363084 := by
    have h1 : 2 * g / (1 / 2 - 0.0024) ≤ 2 * 1.781081 / (1 / 2 - 0.0024) := by
      apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    have h2 : 0 ≤ 2 * g / (1 / 2 - 0.0024) + 3 * (1 / 8349) * 112 := by positivity
    exact mul_le_mul (by linarith) (by norm_num at hc ⊢; linarith) (by linarith) (by norm_num)
  have T5 : log (8 / 3) * (1 / 8349) * 112 ≤ (0.98083 : ℝ) * (1 / 8349) * 112 := by nlinarith
  unfold K3J
  have e1 : 2 * g * log (3 - 8 * 0.0024) / (4 - 8 * 0.0024) =
      2 * (g * log (3 - 8 * 0.0024)) / 3.9808 := by norm_num; ring
  have e2 : g / 4 * (log 6 + r) / (1 / 2 - 0.0024) = g * (log 6 + r) / 1.9904 := by
    norm_num; ring
  rw [e1, e2]
  have hE : (1 / 8349 : ℝ) * 114 * 3 * exp (8 * 0.0024 - 2) / (4 - 8 * 0.0024)
      ≤ (1 / 8349) * 114 * 3 * 0.13796 / (4 - 8 * 0.0024) := by
    apply div_le_div_of_nonneg_right _ (by norm_num); nlinarith
  have hA : 2 * (1.78103 * 1.09219) / 3.9808 ≤ 2 * (g * log (3 - 8 * 0.0024 : ℝ)) / 3.9808 := by
    apply div_le_div_of_nonneg_right _ (by norm_num); linarith
  have hB : g * (log 6 + r) / 1.9904 ≤ 1.781081 * (1.79176 + 0.0081169) / 1.9904 :=
    div_le_div_of_nonneg_right T3 (by norm_num)
  have fin : (0.0042 : ℝ) < 8 * (2 * (1.78103 * 1.09219) / 3.9808
      - (1 / 8349) * 114 * 3 * 0.13796 / (4 - 8 * 0.0024))
      - 1 / 2 * (8 * ((1 + 5e-5) * (1.781081 * (1.79176 + 0.0081169) / 1.9904
        + 0.98083 * (1 / 8349) * 112)))
      - 1 / 2 * ((2 * 1.781081 / (1 / 2 - 0.0024) + 3 * (1 / 8349) * 112) * 0.363084) := by
    norm_num
  nlinarith

/-- `e^{13.45} ≥ 686646`, from `e > 2.7182818283` and `e^{0.45} ≥ 1.568`. -/
lemma exp1345_ge : (686646 : ℝ) ≤ exp 13.45 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : (1.568 : ℝ) ≤ exp 0.45 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.45 : ℝ)) (by norm_num) 8
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have e : exp (13.45 : ℝ) = exp 1 ^ 13 * exp 0.45 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have h13 : (2.7182818283 : ℝ) ^ 13 ≤ exp 1 ^ 13 := pow_le_pow_left₀ (by norm_num) h1.le 13
  calc (686646 : ℝ) ≤ 2.7182818283 ^ 13 * 1.568 := by norm_num
    _ ≤ exp 1 ^ 13 * exp 0.45 := mul_le_mul h13 h2 (by norm_num) (by positivity)

/-- **Conditions (19), (21), (25) at log log X₂ = 13.45**: with L = log X₂ = e^{13.45},
`0.0024 L − 11 log L ≥ 1500`, that is `X₂^α / log^{A+1} X₂ ≥ e^{1500}` at A = 10, and
`L ≥ 11/0.0024`. -/
theorem conditions_1345 :
    (1500 : ℝ) ≤ 0.0024 * exp 13.45 - 11 * 13.45 ∧ 11 / 0.0024 ≤ exp (13.45 : ℝ) := by
  have h := exp1345_ge
  constructor <;> nlinarith

#print axioms theorem3_lower_main
#print axioms conditions_1345

end LeanLab.BS2022GRH.Journal
