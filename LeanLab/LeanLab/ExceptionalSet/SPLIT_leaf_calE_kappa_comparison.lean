import LeanLab.ExceptionalSet.SPLIT_leaf_decay_rescale

/-!
Split of the scalar `κ`-versus-`η` comparison inside the rescaling step.

The file `SPLIT_leaf_decay_rescale` records the target `leaf_calE_kappa_comparison`: for
`1 < γ < 3 / 2`, positive `η` and `κ` with `κ ≤ η / 6`, and `N ≥ 64`, the pure decay
`exp (-(η / 4) * (log N) ^ (3 - 2γ))` is dominated by the `κ`-th scale raised to the power
`-(3 / 2)`.  Since `calE γ κ N = exp (κ * (log N) ^ (3 - 2γ))`, the whole content is:

* rewriting the negative power of the exponential as a single exponential;
* the arithmetic `κ ≤ η / 6` giving `(3 / 2) * κ ≤ η / 4`;
* non-negativity of the real power `(log N) ^ (3 - 2γ)` (no range hypothesis on `γ` needed);
* the order step on the two exponents, then monotonicity of `exp`.

The four leaves below are exactly those steps.  No exponential sum, phase or cancellation is
involved, and every leaf is a strictly weaker statement than the target.  Note that the
chain never uses `1 < γ` or `γ < 3 / 2`: a real power with a non-negative base is
non-negative for every exponent, so the range of `γ` is not needed here.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE expSumF)
open LeanLab.ExceptionalSet.Decomp404e (phaseSum)

/-- LEAF. Rewriting step: the negative power of the `κ`-th scale is the single exponential
of `-(3 / 2) * κ * (log N) ^ (3 - 2γ)`.  This is the identity `x ^ y = exp (log x * y)` for
the positive `x = calE γ κ N`, followed by `log (exp z) = z`. -/
theorem leaf_calE_rpow_exp (γ κ : ℝ) (N : ℕ) :
    calE γ κ N ^ (-(3 / 2 : ℝ)) =
      Real.exp (-((3 / 2) * κ * Real.log (N : ℝ) ^ (3 - 2 * γ))) := by
  sorry

/-- LEAF. The `κ` side of the comparison, as pure arithmetic: from `κ ≤ η / 6` follows
`(3 / 2) * κ ≤ η / 4`.  This is the only step that uses the cap on `κ`, and it is uniform
in `N`. -/
theorem leaf_kappa_sixth_le_quarter (κ η : ℝ) (h : κ ≤ η / 6) :
    (3 / 2) * κ ≤ η / 4 := by
  sorry

/-- LEAF. Positivity input: a real power with the base `log N` is non-negative for `N ≥ 1`.
This is what lets the order step scale by `(log N) ^ (3 - 2γ)` without a sign condition. -/
theorem leaf_log_rpow_nonneg (γ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := by
  sorry

/-- LEAF. The order step on the exponents: if `(3 / 2) * κ ≤ η / 4` and `x ≥ 0`, then
`-(η / 4) * x ≤ -((3 / 2) * κ * x)`.  This is one multiplication by a non-negative factor,
with no exponential and no logarithm in sight. -/
theorem leaf_exponent_order (x η κ : ℝ) (hκ : (3 / 2) * κ ≤ η / 4) (hx : 0 ≤ x) :
    -(η / 4) * x ≤ -((3 / 2) * κ * x) := by
  sorry

/-- Assembly from the four leaves: rewrite the negative power, reduce to the exponent
inequality, feed the `κ ≤ η / 6` arithmetic through the order step and finish with
monotonicity of `Real.exp`. -/
theorem leaf_calE_kappa_comparison_split
    (γ η κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hη : 0 < η) (hκ : 0 < κ) (hκ6 : κ ≤ η / 6) (N : ℕ) (hN : 64 ≤ N) : Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤ calE γ κ N ^ (-(3 / 2 : ℝ)) := by
  rw [leaf_calE_rpow_exp γ κ N]
  refine Real.exp_le_exp.mpr ?_
  obtain ⟨hN1, -⟩ : (1 ≤ N ∧ 0 < N) := by omega
  exact leaf_exponent_order (Real.log (N : ℝ) ^ (3 - 2 * γ)) η κ
    (leaf_kappa_sixth_le_quarter κ η hκ6) (leaf_log_rpow_nonneg γ N hN1)

#print axioms leaf_calE_kappa_comparison_split

end LeanLab.ExceptionalSet.Decomp446c
