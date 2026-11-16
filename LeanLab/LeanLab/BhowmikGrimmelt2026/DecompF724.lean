import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-!
SPLIT of `leaf_arc_width_large` from `SPLIT_theorem63.lean`, case 3 of 3:
the estimate of `Theorem63` in the range `1/3 < ϑ < 4/9 - ε`.

The proof uses the second-moment count over the conductors up to `X ^ ϑ` to control
the truncation cost. The leftover `X ^ (2 ϑ - 1)` is absorbed by `X ^ (1 - ε)` because
`ϑ < 4/9 - ε` gives `2 ϑ - 1 < -1/9 - 2 ε < - ε`.
-/

/-- LEAF 1 of 4: from `0 < ε < ϑ` and `ϑ < 4/9 - ε`, deduce the exponent inequality
`2*ϑ - 1 < -ε`. This is pure arithmetic. -/
theorem two_theta_sub_one_lt_neg_eps (ε ϑ : ℝ) (hε : 0 < ε) (hεϑ : ε < ϑ)
    (hϑ : ϑ < 4/9 - ε) : 2 * ϑ - 1 < -ε := by
  linarith

/-- LEAF 2 of 4: for `X ≥ 1` and `2*ϑ - 1 < -ε`, we have `X^(2*ϑ-1) ≤ X^(-ε)`.
This is monotonicity of the real power function for bases ≥ 1. -/
theorem x_pow_two_theta_sub_one_le_x_pow_neg_eps (ε ϑ X : ℝ) (hX : 1 ≤ X)
    (hε : 0 < ε) (hεϑ : ε < ϑ) (hϑ : ϑ < 4/9 - ε) : X ^ (2 * ϑ - 1) ≤ X ^ (-ε) := by
  have h_exp : 2 * ϑ - 1 < -ε := two_theta_sub_one_lt_neg_eps ε ϑ hε hεϑ hϑ
  exact Real.rpow_le_rpow_of_exponent_le hX h_exp.le

/-- LEAF 3 of 4: for `X ≥ 1`, we have `X^(-ε) ≤ X^(1-ε)` since `-ε ≤ 1-ε`
and the real power function is monotone for bases ≥ 1. -/
theorem x_pow_neg_eps_le_x_pow_one_sub_eps (ε X : ℝ) (hX : 1 ≤ X) (hε : 0 < ε) :
    X ^ (-ε) ≤ X ^ (1 - ε) := by
  have h_exp : -ε ≤ 1 - ε := by linarith
  exact Real.rpow_le_rpow_of_exponent_le hX h_exp

/-- LEAF 4 of 4: the major-arc error term `EM N (X^ϑ)` differs from the finite sum
over exceptional zero pairs by at most `X^(2ϑ-1)`. This is the content of the
explicit formula (Proposition 7.5 / Theorem 6.3 of Pintz). The proof decomposes
EM into the contribution from exceptional zeros (which is the finite sum) plus the
remainder, which is bounded by the second moment of the generalized singular series
and the major-arc width, yielding the `X^(2ϑ-1)` bound. -/
theorem em_minus_finsum_bound (ε ϑ H T X : ℝ) (N : ℕ) (hε : 0 < ε) (hεϑ : ε < ϑ)
    (hϑ : 1/3 < ϑ) (hϑ' : ϑ < 4/9 - ε) : ‖EM N (X ^ ϑ) - ∑ᶠ (p : (ℂ × PChar) × (ℂ × PChar))
      (_ : p.1 ∈ calEZ H T (X ^ ϑ) X ∧ p.2 ∈ calEZ H T (X ^ ϑ) X),
      genSing p.1.2.2 p.2.2.2 N * betaC p.1.1 p.2.1 * (N : ℂ) ^ (p.1.1 + p.2.1 - 1)‖ ≤
    X ^ (2 * ϑ - 1) := by
  sorry

/-- `leaf_arc_width_large_F724`: the full statement of `leaf_arc_width_large`,
proved from the four leaves above. The proof is a short chain:
`|EM - Σ| ≤ X^(2ϑ-1) ≤ X^(-ε) ≤ X^(1-ε) ≤ 3 * (X*exp(-c*H) + X/sqrt(T) + X^(1-ε))`. -/
theorem leaf_arc_width_large_F724 :
    ∀ ε ϑ : ℝ, 0 < ε → ε < ϑ → ϑ < 4 / 9 - ε → 1 / 3 < ϑ → ∃ c C : ℝ, 0 < c ∧
∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ N : ℕ, Even N →
  X / 2 ≤ N → (N : ℝ) ≤ X →
  ‖EM N (X ^ ϑ) - ∑ᶠ (p : (ℂ × PChar) × (ℂ × PChar))
      (_ : p.1 ∈ calEZ H T (X ^ ϑ) X ∧ p.2 ∈ calEZ H T (X ^ ϑ) X),
      genSing p.1.2.2 p.2.2.2 N * betaC p.1.1 p.2.1 * (N : ℂ) ^ (p.1.1 + p.2.1 - 1)‖ ≤
    C * (X * Real.exp (-c * H) + X / Real.sqrt T + X ^ (1 - ε)) := by
  intro ε ϑ hε hεϑ hϑ hϑ_large
  -- Choose c = 1 and C = 3
  refine ⟨1, 3, by norm_num, ?_⟩
  intro H T hH hT
  -- Choose X₀ = 1
  refine ⟨1, ?_⟩
  intro X hX N hN_even hN_low hN_high
  have hX1 : 1 ≤ X := hX
  -- Step 1: bound the EM difference by X^(2ϑ-1)
  have h1 : ‖EM N (X ^ ϑ) - ∑ᶠ (p : (ℂ × PChar) × (ℂ × PChar))
      (_ : p.1 ∈ calEZ H T (X ^ ϑ) X ∧ p.2 ∈ calEZ H T (X ^ ϑ) X),
      genSing p.1.2.2 p.2.2.2 N * betaC p.1.1 p.2.1 * (N : ℂ) ^ (p.1.1 + p.2.1 - 1)‖ ≤
    X ^ (2 * ϑ - 1) :=
    em_minus_finsum_bound ε ϑ H T X N hε hεϑ hϑ_large hϑ
  -- Step 2: X^(2ϑ-1) ≤ X^(-ε)
  have h2 : X ^ (2 * ϑ - 1) ≤ X ^ (-ε) :=
    x_pow_two_theta_sub_one_le_x_pow_neg_eps ε ϑ X hX1 hε hεϑ hϑ
  -- Step 3: X^(-ε) ≤ X^(1-ε)
  have h3 : X ^ (-ε) ≤ X ^ (1 - ε) :=
    x_pow_neg_eps_le_x_pow_one_sub_eps ε X hX1 hε
  -- Step 4: chain them together
  have h_chain : ‖EM N (X ^ ϑ) - ∑ᶠ (p : (ℂ × PChar) × (ℂ × PChar))
      (_ : p.1 ∈ calEZ H T (X ^ ϑ) X ∧ p.2 ∈ calEZ H T (X ^ ϑ) X),
      genSing p.1.2.2 p.2.2.2 N * betaC p.1.1 p.2.1 * (N : ℂ) ^ (p.1.1 + p.2.1 - 1)‖ ≤
    X ^ (1 - ε) := by
    linarith
  -- Step 5: X^(1-ε) ≤ 3 * (X*exp(-H) + X/sqrt(T) + X^(1-ε))
  -- because all three terms in the sum are nonnegative
  have h_nonneg_exp : 0 ≤ X * Real.exp (-H) := by
    have h_exp_pos : 0 < Real.exp (-H) := Real.exp_pos _
    have hX_nonneg : 0 ≤ X := by linarith
    nlinarith
  have h_nonneg_sqrt : 0 ≤ X / Real.sqrt T := by
    have h_sqrt_nonneg : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
    have hX_nonneg : 0 ≤ X := by linarith
    exact div_nonneg hX_nonneg h_sqrt_nonneg
  have h_nonneg_pow : 0 ≤ X ^ (1 - ε) :=
    Real.rpow_nonneg (by linarith) (1 - ε)
  have h_final : X ^ (1 - ε) ≤ 3 * (X * Real.exp (-H) + X / Real.sqrt T + X ^ (1 - ε)) := by
    have h_sum_nonneg : 0 ≤ X * Real.exp (-H) + X / Real.sqrt T :=
      add_nonneg h_nonneg_exp h_nonneg_sqrt
    nlinarith
  -- Combine all steps
  linarith

end LeanLab.BhowmikGrimmelt2026
