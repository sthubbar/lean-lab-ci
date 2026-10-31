import Mathlib

/-!
# P0092 Ricci 1937, page 90, case 5°: the printed b = 366 against the paper's own rule

Unit U-1079, PC run 20261019T1603Z-20267. AI wrote the Lean code. Binary Goldbach is OPEN.

Page 89 fixes a and b by `[1 + 2τ̄] ≤ a` and `[e^ω (1 + 2τ̄)] ≤ b`. This rule reproduces
b = 6, 7, 9, 15 in cases 1° to 4°. Page 90, case 5°: `ω = 5,21`, `d = 9`,
`τ̄ = e^{-θ₁} + e^{-(θ₁+θ₂)} + e^{-(θ₁+θ₂+θ₃)} (1 - e^{-6θ})/(1 - e^{-θ})
      + e^{-½(ω+θ₁+θ₂+θ₃+6θ)}/(1 - e^{-½θ})`,
with (2.3) `θ₁ = 0,90, θ₂ = 0,56, θ₃ = 0,52, θ = 0,50`; printed `τ̄ < 1, a = 2, b = 366`.

`case5_rule_floor_ge`: with the printed τ̄ and ω, `[e^ω (1 + 2τ̄)] ≥ 367`, so the printed
b = 366 does not satisfy the paper's rule; the value is about 549. 366 = [183,1 · 2] matches
`e^ω (1 + τ̄)` instead. PROVED below with a deliberately loose lower bound, 400.
-/

namespace LeanLab.Ricci1937

open Real

noncomputable section

def θ₁ : ℝ := 0.90
def θ₂ : ℝ := 0.56
def θ₃ : ℝ := 0.52
def θ  : ℝ := 0.50
def ω5 : ℝ := 5.21

/-- The printed τ̄ of case 5°, page 90. -/
def tauBar5 : ℝ :=
  exp (-θ₁) + exp (-(θ₁ + θ₂)) + exp (-(θ₁ + θ₂ + θ₃)) * (1 - exp (-(6 * θ))) / (1 - exp (-θ))
    + exp (-(1 / 2) * (ω5 + θ₁ + θ₂ + θ₃ + 6 * θ)) / (1 - exp (-(1 / 2) * θ))

lemma exp_neg_ge_of_le {x : ℝ} (hx : x ≤ 2) : exp (-2) ≤ exp (-x) := exp_le_exp.mpr (by linarith)

lemma exp_neg_two_gt : (0.1353 : ℝ) < exp (-2) := by
  rw [exp_neg, show (2:ℝ) = 1 + 1 by norm_num, exp_add]
  have h := exp_one_lt_d9
  have h0 := exp_pos 1
  rw [lt_inv_comm₀ (by norm_num) (by positivity)]
  nlinarith

lemma exp_neg_one_gt : (0.3678 : ℝ) < exp (-1) := by
  rw [exp_neg]
  have h := exp_one_lt_d9
  rw [lt_inv_comm₀ (by norm_num) (exp_pos 1)]
  linarith

lemma tauBar5_gt : (0.638 : ℝ) < tauBar5 := by
  have h1 : exp (-1) ≤ exp (-θ₁) := exp_le_exp.mpr (by norm_num [θ₁])
  have h2 : exp (-2) ≤ exp (-(θ₁ + θ₂)) := exp_le_exp.mpr (by norm_num [θ₁, θ₂])
  have h3 : exp (-2) ≤ exp (-(θ₁ + θ₂ + θ₃)) := exp_le_exp.mpr (by norm_num [θ₁, θ₂, θ₃])
  have hq : 1 ≤ (1 - exp (-(6 * θ))) / (1 - exp (-θ)) := by
    have hd : 0 < 1 - exp (-θ) := by
      have : exp (-θ) < 1 := exp_lt_one_iff.mpr (by norm_num [θ])
      linarith
    rw [le_div_iff₀ hd]
    have : exp (-(6 * θ)) ≤ exp (-θ) := exp_le_exp.mpr (by norm_num [θ])
    linarith
  have h4 : 0 ≤ exp (-(1 / 2) * (ω5 + θ₁ + θ₂ + θ₃ + 6 * θ)) / (1 - exp (-(1 / 2) * θ)) := by
    apply div_nonneg (exp_pos _).le
    have : exp (-(1 / 2) * θ) ≤ 1 := exp_le_one_iff.mpr (by norm_num [θ])
    linarith
  have h3' : exp (-2) ≤ exp (-(θ₁ + θ₂ + θ₃)) * (1 - exp (-(6 * θ))) / (1 - exp (-θ)) := by
    rw [mul_div_assoc]
    have := exp_pos (-(θ₁ + θ₂ + θ₃))
    nlinarith
  have := exp_neg_two_gt
  have := exp_neg_one_gt
  unfold tauBar5
  linarith

lemma exp_521_gt : (179.5 : ℝ) < exp ω5 := by
  have h5 : (2.7182818283 : ℝ) ^ 5 < exp 1 ^ 5 :=
    pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num)
  have h21 : (1.21 : ℝ) ≤ exp 0.21 := by
    have := add_one_le_exp (0.21 : ℝ); linarith
  have hsplit : exp ω5 = exp 1 ^ 5 * exp 0.21 := by
    rw [← exp_nat_mul, ← exp_add]; norm_num [ω5]
  rw [hsplit]
  have hm := mul_le_mul h5.le h21 (by norm_num) (by positivity)
  have : (179.5 : ℝ) < 2.7182818283 ^ 5 * 1.21 := by norm_num
  linarith

/-- **Case 5° does not satisfy the paper's own rule for b, PROVED.** `[e^ω (1 + 2τ̄)] ≥ 367`,
so the printed `b = 366` fails `[e^ω (1 + 2τ̄)] ≤ b`. -/
theorem case5_rule_value_gt : (400 : ℝ) < exp ω5 * (1 + 2 * tauBar5) := by
  have h1 := tauBar5_gt; have h2 := exp_521_gt
  have := mul_le_mul h2.le (show (1 + 2 * 0.638 : ℝ) ≤ 1 + 2 * tauBar5 by linarith) (by norm_num)
    (exp_pos _).le
  linarith

theorem case5_rule_floor_ge : 367 ≤ ⌊exp ω5 * (1 + 2 * tauBar5)⌋ := by
  have := case5_rule_value_gt
  rw [Int.le_floor]; push_cast; linarith

/-- The printed `b = 366` violates the page 89 rule `[e^ω (1 + 2τ̄)] ≤ b`. -/
theorem printed_366_not_rule : ¬ (⌊exp ω5 * (1 + 2 * tauBar5)⌋ ≤ 366) := by
  have := case5_rule_floor_ge; omega

end
end LeanLab.Ricci1937
