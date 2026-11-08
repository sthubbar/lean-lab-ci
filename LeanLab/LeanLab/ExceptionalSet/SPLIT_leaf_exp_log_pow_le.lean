import LeanLab.ExceptionalSet.SPLIT_leaf_decay_rescale

/-!
Split of the scalar growth step `leaf_exp_log_pow_le` of the distant phase rescaling.

For `1 < γ < 3 / 2` the exponent `a = 3 - 2 * γ` lies in `(0, 1)`, so `log ^ a` is
negligible against `log`, and for every positive `η` the inequality
`η * (log N) ^ a ≤ log N / 2` holds for all large `N`.  Exponentiating and using
`exp (log N / 2) ≤ N` turns that into `exp (η * (log N) ^ a) ≤ N`.

The leaves are exactly the three steps of that chain: the real-power decay
`x ^ (a - 1) → 0`, its transfer to the logarithm of an integer, the resulting
eventual half-log bound, and the elementary comparison `exp (log N / 2) ≤ N`.
No exponential sum, no phase, and no cancellation is involved.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE expSumF)
open LeanLab.ExceptionalSet.Decomp404e (phaseSum)

/-- LEAF. The real power decays: for `0 < a < 1` the exponent `a - 1` is negative, so
`x ^ (a - 1)` tends to `0` as `x → +∞`.  This is the analytic core of the whole step,
and it carries no integer index and no logarithm. -/
theorem leaf_rpow_sub_one_tendsto_zero (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Filter.Tendsto (fun x : ℝ => x ^ (a - 1)) Filter.atTop (nhds 0) := by
  sorry

/-- LEAF. Transfer of the previous leaf to the logarithm of an integer: since
`log N → +∞`, the quotient `(log N) ^ a / log N = (log N) ^ (a - 1)` still tends to `0`
along `N : ℕ`.  Only the values `N ≥ 2` matter; at `N = 0` and `N = 1` the logarithm
vanishes and the quotient is `0` by Lean's division convention. -/
theorem leaf_log_rpow_div_log_tendsto_zero (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ a / Real.log (N : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

/-- LEAF. From the vanishing quotient to the eventual half-log bound: with `ε = 1 / (2 * η)`
the previous leaf gives `η * (log N) ^ a ≤ log N / 2` for every large `N`.  This is where
the constant `η` is absorbed and it is the only place where positivity of `η` is used. -/
theorem leaf_eta_mul_log_pow_eventually_half (a η : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      η * Real.log (N : ℝ) ^ a ≤ Real.log (N : ℝ) / 2 := by
  sorry

/-- LEAF. The elementary comparison: for `1 ≤ N` the logarithm is nonnegative, so
`exp (log N / 2) ≤ exp (log N) = N`.  The hypothesis `1 ≤ N` cannot be dropped: at `N = 0`
the logarithm is `0`, `exp 0 = 1`, and the right side is `0`. -/
theorem leaf_exp_half_log_le (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (Real.log (N : ℝ) / 2) ≤ (N : ℝ) := by
  sorry

/-- Assembly of the growth step from the leaves: the exponent `3 - 2 * γ` lies in `(0, 1)`,
the half-log bound holds past its threshold, and `exp` is monotone, so
`exp (η * log ^ a) ≤ exp (log N / 2) ≤ N` for every `N` past the larger threshold. -/
theorem leaf_exp_log_pow_le_split (γ η : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.exp (η * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤ (N : ℝ) := by
  have ha0 : 0 < 3 - 2 * γ := by linarith
  have ha1 : 3 - 2 * γ < 1 := by linarith
  obtain ⟨N₁, hN₁⟩ := leaf_eta_mul_log_pow_eventually_half (3 - 2 * γ) η ha0 ha1 hη
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hstep : η * Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log (N : ℝ) / 2 := hN₁ N hN₁'
  exact (Real.exp_le_exp.mpr hstep).trans (leaf_exp_half_log_le N hN1)

-- Axiom audit driver.
#print axioms leaf_exp_log_pow_le_split

end LeanLab.ExceptionalSet.Decomp446c
