import LeanLab.ExceptionalSet.Decomp446c

/-!
Split of the frequency range step of the distant phase input, page 366 of the source.

The target `leaf_frequency_range` is a pure scaling statement about the scale
`F γ N = exp ((log N) ^ γ)` at the two index sizes `2 * (N / 2)` and `N / 2`.
The scale is increasing in `γ` and in the index, so both conclusions follow from a
comparison of the exponents after taking logarithms: the lower conclusion needs
`(1 - 3 δ) * (log N) ^ γ ≤ (1 - 2 δ) * (log (2 * (N / 2))) ^ γ`, the upper conclusion
needs `log 2 + 6 δ * (log N) ^ γ ≤ 12 δ * (log (N / 2)) ^ γ`.  Both comparisons
hold once `log N` is large enough, because `γ > 1` makes the gap between
`(log N) ^ γ` and `(log (N / 2)) ^ γ` grow without bound, while the loss in
doubling the coefficient is only the fixed ratio `(1 - 2 δ) / (1 - 3 δ) < 1`
respectively the fixed `δ / 2`.  The elementary input to that comparison is the
tangent line bound `1 - r * t ≤ (1 - t) ^ r` for `r ≥ 1`, which transfers
`(log N - c) ^ γ ≥ (log N) ^ γ - γ * c * (log N) ^ (γ - 1)`.

Nothing here concludes anything about an exponential sum.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446c

open Filter Real Topology Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF. The tangent line bound at `1` for a real power: for `1 ≤ r` and `0 ≤ t ≤ 1` the
power `(1 - t) ^ r` lies above the line `1 - r * t`.  This is the single elementary
estimate behind both log-power gap leaves below; it is false for `r < 1` at `t = 1`. -/
theorem leaf_one_sub_rpow_lower (r t : ℝ) (hr : 1 ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - r * t ≤ (1 - t) ^ r := by
  have hs : -1 ≤ -t := by linarith
  have h := one_add_mul_self_le_rpow_one_add hs hr
  have h2 : 1 - r * t = 1 + r * (-t) := by ring
  have h3 : (1 - t) ^ r = (1 + (-t)) ^ r := by ring_nf
  linarith

/-- LEAF. Lower log-power gap.  Eventually the log-power at the doubled half index, scaled
by `1 - 2 δ`, dominates the log-power at `N` scaled by `1 - 3 δ`.  This is the estimate
that puts the lower threshold `F γ N ^ (3 δ - 1)` above `F γ (2 * (N / 2)) ^ (-(1 - 2 δ))`:
the floor in `N / 2` costs only a bounded change of the logarithm, the exponent gap
`- (1 - 3 δ) + (1 - 2 δ) = - δ` costs a factor `δ` of `(log N) ^ γ`, and `γ > 1` makes
`(log N) ^ γ` grow faster than `(log N) ^ (γ - 1)`. -/
theorem leaf_log_gap_lower (γ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ)
    (hδsmall : δ < min ((γ - 1) / 24) (1 / 12)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 - 3 * δ) * Real.log N ^ γ ≤
        (1 - 2 * δ) * Real.log (2 * ((N / 2 : ℕ) : ℝ)) ^ γ := by
  sorry

/-- LEAF. Upper log-power gap.  Eventually the log-power at `N / 2`, scaled by `12 δ`,
dominates `log 2 + 6 δ * (log N) ^ γ`.  This is the estimate that absorbs the factor `2`
of the hypothesis `|t| ≤ 2 * F γ N ^ (6 δ)` into the doubling of the exponent at the
half index. -/
theorem leaf_log_gap_upper (γ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ)
    (hδsmall : δ < min ((γ - 1) / 24) (1 / 12)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      6 * δ * Real.log N ^ γ + Real.log 2 ≤
        12 * δ * Real.log (((N / 2 : ℕ)) : ℝ) ^ γ := by
  sorry

/-- LEAF. Power identity for the scale `F`: raising `F γ x` to a real power multiplies the
log-power by that power, `F γ x ^ c = exp (c * (log x) ^ γ)`.  This is the identity that
carries the two log-power gap estimates over to the statement in terms of `F`. -/
theorem leaf_F_rpow_exp (γ x c : ℝ) :
    F γ x ^ c = Real.exp (c * Real.log x ^ γ) := by
  dsimp [F]
  rw [← Real.exp_mul]
  ring_nf

/-- Assembly of the frequency range step from the four leaves: take `N₀` beyond both
eventual thresholds, then the lower conclusion is the first gap leaf followed by the
strict lower hypothesis, and the upper conclusion is the upper hypothesis followed by
the factor `2 = exp (log 2)` folded into the second gap leaf. -/
theorem leaf_frequency_range_split (γ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hδsmall : δ < min ((γ - 1) / 24) (1 / 12)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
      F γ N ^ (3 * δ - 1) < |t| → |t| ≤ 2 * F γ N ^ (6 * δ) →
        F γ (2 * (N / 2 : ℕ)) ^ (-(1 - 2 * δ)) ≤ |t| ∧
          |t| ≤ F γ (N / 2 : ℕ) ^ (12 * δ) := by
  obtain ⟨Nl, hl⟩ := Filter.eventually_atTop.mp (leaf_log_gap_lower γ δ h1 h2 hδ hδsmall)
  obtain ⟨Nu, hu⟩ := Filter.eventually_atTop.mp (leaf_log_gap_upper γ δ h1 h2 hδ hδsmall)
  refine ⟨max Nl Nu, fun N hN t htlow hthigh => ⟨?_, ?_⟩⟩
  · have hgap := hl N ((le_max_left _ _).trans hN)
    rw [leaf_F_rpow_exp] at htlow ⊢
    refine le_trans (Real.exp_le_exp.mpr ?_) htlow.le
    linarith
  · have hgap := hu N ((le_max_right _ _).trans hN)
    rw [leaf_F_rpow_exp] at hthigh
    refine hthigh.trans ?_
    rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm,
      ← Real.exp_add, leaf_F_rpow_exp]
    exact Real.exp_le_exp.mpr (by linarith)

end LeanLab.ExceptionalSet.Decomp446c
