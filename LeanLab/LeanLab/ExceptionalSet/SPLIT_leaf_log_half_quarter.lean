import LeanLab.ExceptionalSet.SPLIT_leaf_decay_rescale

/-!
Split of the scalar half-index logarithm leaf `leaf_log_half_quarter` of
`LeanLab.ExceptionalSet.SPLIT_leaf_decay_rescale`.

The target is a pure scalar statement: for `0 < a < 1` and every `N ≥ 64`,

  `(1 / 4) * log N ^ a ≤ log (N / 2) ^ a`,

where `N / 2` is the natural floor and `log` is the real logarithm.  Its only content is
that the integer half index loses at most a factor `4` inside the logarithm, and that a
real power with exponent `a < 1` preserves that loss.

The three leaves are exactly those two steps plus the arithmetic of the floor:

* `leaf_half_nat_div_ge_quarter`: the natural floor `N / 2` is at least `N / 4` as a real,
  which is where `Lean`'s truncating division on `ℕ` is paid for;
* `leaf_log_half_ge_quarter`: consequently `log (N / 2) ≥ log N / 4`, since `log N ≥ log 16`
  absorbs the `log 4` of the split `log (N / 4) = log N - log 4`;
* `leaf_rpow_four_quarter_le`: the power step, `(1 / 4) * (4 * u) ^ a ≤ v ^ a` whenever
  `0 < u ≤ v` and `0 < a < 1`, which is `4 ^ a ≤ 4` together with monotonicity of `^ a`.

Assembly only substitutes `u = log N / 4`.  No positivity issue arises at the endpoints:
`N ≥ 64` forces `N / 2 ≥ 32`, so both logarithms are strictly positive, and `a > 0` is used
only to keep `(1 / 4) * (4 * u) ^ a` ordered against `u ^ a`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE expSumF)
open LeanLab.ExceptionalSet.Decomp404e (phaseSum)

/-- LEAF. The floor step on the index: for `N ≥ 64` the natural division `N / 2` is at
least `N / 4` read as a real.  This is the only leaf in which `Lean`'s truncation enters:
`N ≤ 4 * (N / 2)` holds in `ℕ` for every `N`, and `N ≥ 64` makes the loss of the odd unit
irrelevant.  It is an inequality between two explicit reals, with no logarithm and no
power. -/
theorem leaf_half_nat_div_ge_quarter :
    ∀ N : ℕ, 64 ≤ N → (N : ℝ) / 4 ≤ ((N / 2 : ℕ) : ℝ) := by
  sorry

/-- LEAF. The logarithm at the integer half of `N` is at least a quarter of the logarithm
at `N`: for `N ≥ 64`, `log (N / 2) ≥ log (N / 4) = log N - log 4 ≥ log N / 4`, the last
step because `log N ≥ log 16 = 2 * log 4`.  This is the monotone step which carries the
floor leaf through `Real.log`; no power is involved. -/
theorem leaf_log_half_ge_quarter :
    ∀ N : ℕ, 64 ≤ N → (1 / 4) * Real.log (N : ℝ) ≤ Real.log (N / 2 : ℕ) := by
  sorry

/-- LEAF. The power step, stated with no `ℕ` and no logarithm: for `0 < a < 1` and reals
`0 < u ≤ v`, one has `(1 / 4) * (4 * u) ^ a ≤ v ^ a`.  Indeed `(4 * u) ^ a = 4 ^ a * u ^ a`,
`u ^ a ≤ v ^ a` by monotonicity of the real power with positive exponent, and
`(1 / 4) * 4 ^ a ≤ 1` because `4 ^ a ≤ 4 ^ 1 = 4` for `a ≤ 1`.  The bound is attained at
`a = 1`, which the hypothesis `a < 1` excludes; `u > 0` is needed and cannot be dropped. -/
theorem leaf_rpow_four_quarter_le (a u v : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hu : 0 < u)
    (huv : u ≤ v) : (1 / 4) * (4 * u) ^ a ≤ v ^ a := by
  sorry

/-- Assembly of the half-index logarithm bound from the three leaves: take
`u = (1 / 4) * log N`, so that `4 * u = log N` by `ring`, and `v = log (N / 2)`.  The
order `u ≤ v` is the logarithm leaf, and `u > 0` is `Real.log_pos` at `N ≥ 64`.  The
conclusion of the power leaf, rewritten along `4 * u = log N`, is the target. -/
theorem leaf_log_half_quarter_split (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ N : ℕ, 64 ≤ N →
      (1 / 4) * Real.log (N : ℝ) ^ a ≤ Real.log (N / 2 : ℕ) ^ a := by
  intro N hN
  have hN64 : (2 : ℝ) ≤ (N : ℝ) := by
    have h : (2 : ℕ) ≤ N := by omega
    exact_mod_cast h
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hu : 0 < (1 / 4) * Real.log (N : ℝ) := by linarith
  have h4 : (4 : ℝ) * ((1 / 4) * Real.log (N : ℝ)) = Real.log (N : ℝ) := by ring
  have key := leaf_rpow_four_quarter_le a ((1 / 4) * Real.log (N : ℝ))
    (Real.log (N / 2 : ℕ)) ha0 ha1 hu (leaf_log_half_ge_quarter N hN)
  rwa [h4] at key

-- Axiom audit driver.
#print axioms leaf_log_half_quarter_split

end LeanLab.ExceptionalSet.Decomp446c
