import LeanLab.ExceptionalSet.SPLIT_leaf_decay_rescale

/-!
Split of the scalar decay comparison `leaf_exp_decay_quarter` of
`LeanLab.ExceptionalSet.SPLIT_leaf_decay_rescale`.

The target compares the dyadic decay of the distant phase at the integer half index `N / 2`
with the decay at `N` carrying the exponent `η / 4`: for `1 < γ < 3 / 2`, positive `η` and
every `N ≥ 64`,

  `exp (-η * log (N / 2) ^ (3 - 2γ)) ≤ exp (-(η / 4) * log N ^ (3 - 2γ))`,

where `N / 2` is the natural floor and `log N` is the real logarithm.  The exponent
`a = 3 - 2γ` lies in `(0, 1)` with `γ` in that range.  The content is three scalar steps
and nothing else:

* the integer half index loses at most a factor `4` inside the logarithm, which is a
  genuinely log-arithmetic comparison at the floor (the only place `N / 2` enters);
* a real power with exponent in `(0, 1)` is monotone, so the factor `4` survives the power
  as the factor `1 / 4`, and no sign or range loss occurs because `log N ≥ 0` for `N ≥ 64`;
* the factor `η > 0` is moved inside the two sides, after which the two exponentials are
  compared by monotonicity of `Real.exp`.

The four leaves below are exactly those steps, each a strictly weaker scalar statement than
the target; the exponent range is isolated as its own arithmetic leaf so that the rest of
the file carries no hypothesis on `γ`.  No exponential sum, no phase and no cancellation is
involved, and the leaves do not restate the target.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE expSumF)
open LeanLab.ExceptionalSet.Decomp404e (phaseSum)

/-- LEAF. The exponent range: `1 < γ < 3 / 2` puts `3 - 2γ` strictly between `0` and `1`.
This is pure arithmetic on `γ`; it is what makes the real power in the target monotone and
strictly increasing, and it is the only leaf that mentions `γ`. -/
theorem leaf_exponent_mem_unit (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    0 < 3 - 2 * γ ∧ 3 - 2 * γ < 1 := by
  sorry

/-- LEAF. The integer half index inside the logarithm: for `N ≥ 64` the natural floor
`N / 2` is at least `N / 4` as a real, and since `log 4 ≤ 2` is absorbed by
`log N ≥ log 64`, the logarithm loses at most a factor `4`, i.e.
`(1 / 4) * log N ≤ log (N / 2)`.  For `N ≥ 64` the left index `N / 2` is at least `32`, so
both logarithms are positive and Lean's division truncates nothing that matters. -/
theorem leaf_log_half_index_ge_quarter :
    ∀ N : ℕ, 64 ≤ N → (1 / 4) * Real.log (N : ℝ) ≤ Real.log (N / 2 : ℕ) := by
  sorry

/-- LEAF. Monotonicity of a real power with exponent in `(0, 1)` together with
`(1 / 4) ^ a ≥ 1 / 4` for `0 < a < 1`: from `0 ≤ x` and `(1 / 4) * x ≤ y` follows
`(1 / 4) * x ^ a ≤ y ^ a`.  Both bases are non-negative, so `mul_rpow` applies, and the
factor `(1 / 4) ^ a` is at least `1 / 4` because `4 ^ (-a) ≥ 4 ^ (-1)`. -/
theorem leaf_rpow_quarter_le (a x y : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hx : 0 ≤ x)
    (hxy : (1 / 4) * x ≤ y) : (1 / 4) * x ^ a ≤ y ^ a := by
  sorry

/-- LEAF. The exponential comparison: for positive `η`, `(1 / 4) * s ≤ t` gives
`exp (-η * t) ≤ exp (-(η / 4) * s)`.  Multiplying by `η > 0` turns the hypothesis into
`(η / 4) * s ≤ η * t`, negation reverses it, and `Real.exp` is monotone. -/
theorem leaf_exp_decay_mono (η s t : ℝ) (hη : 0 < η) (h : (1 / 4) * s ≤ t) :
    Real.exp (-η * t) ≤ Real.exp (-(η / 4) * s) := by
  sorry

/-- Assembly of the decay comparison from the four leaves: take `a = 3 - 2γ`, feed the
half-index logarithm bound through the power leaf with `x = log N` and
`y = log (N / 2)`, then finish with the exponential leaf.  The non-negativity of `log N`
for `N ≥ 64` is supplied by Mathlib. -/
theorem leaf_exp_decay_quarter_split (γ η : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hη : 0 < η) :
    ∀ N : ℕ, 64 ≤ N →
      Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) ≤
        Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
  obtain ⟨ha0, ha1⟩ := leaf_exponent_mem_unit γ h1 h2
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h : (1 : ℕ) ≤ N := by omega
    exact_mod_cast h
  have hx : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hpow : (1 / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ) ≤
      Real.log (N / 2 : ℕ) ^ (3 - 2 * γ) :=
    leaf_rpow_quarter_le (3 - 2 * γ) (Real.log (N : ℝ)) (Real.log (N / 2 : ℕ))
      ha0 ha1 hx (leaf_log_half_index_ge_quarter N hN)
  exact leaf_exp_decay_mono η (Real.log (N : ℝ) ^ (3 - 2 * γ))
    (Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) hη hpow

#print axioms leaf_exp_decay_quarter_split

end LeanLab.ExceptionalSet.Decomp446c
