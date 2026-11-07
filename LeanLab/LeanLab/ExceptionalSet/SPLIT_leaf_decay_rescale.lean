import LeanLab.ExceptionalSet.Decomp446c

/-!
Split of the scalar rescaling step of the distant phase input, page 366 of the source.

The target `leaf_decay_rescale` is a pure scalar statement: for `1 < γ < 3 / 2`, positive
`η` and `B`, and every `0 < κ ≤ η / 6`, the dyadic exponential decay with constant `B`
at the index `N / 2`, plus the two absolute terms of the endpoint correction, is
eventually dominated by `C * N * calE γ κ N ^ (-(3 / 2))`.  Since
`calE γ κ N = exp (κ * (log N) ^ (3 - 2 γ))` and `γ > 1` makes the exponent
`a = 3 - 2 γ` lie in `(0, 1)`, the whole content is a comparison of three scales:

* the integer half index loses a factor `4` in the logarithm, and the power `a` keeps
  that loss, so `log (N / 2) ^ a ≥ (1 / 4) * (log N) ^ a`;
* hence the decay at `N / 2` is at most the decay at `N` with exponent `η / 4`, and
  `κ ≤ η / 6` makes `(3 / 2) * κ ≤ η / 4`, which turns that into the `calE` factor;
* finally `exp (η * log ^ a)` grows slower than linearly, which is what absorbs the
  absolute term `2` and the constant `B` into one uniform `C = 2 * B + 2`.

The leaves below are exactly those three steps plus the log comparison and the final
bookkeeping.  No exponential sum, no phase, and no cancellation is involved.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE expSumF)
open LeanLab.ExceptionalSet.Decomp404e (phaseSum)

/-- LEAF. The logarithm at the integer half of `N` is at least a quarter of the logarithm
at `N`, and a real power with exponent in `(0, 1)` preserves that lower bound.  This is
the only place where the integer floor `N / 2` enters: for `N ≥ 64` we have
`N / 2 ≥ N / 4` as reals, hence `log (N / 2) ≥ log N - log 4 ≥ log N / 4`, and
`(1 / 4) ^ a ≥ 1 / 4` because `a < 1`. -/
theorem leaf_log_half_quarter (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ N : ℕ, 64 ≤ N →
      (1 / 4) * Real.log (N : ℝ) ^ a ≤ Real.log (N / 2 : ℕ) ^ a := by
  sorry

/-- LEAF. The dyadic decay at the integer half of `N` is at most the decay recorded at
`N` with the exponent `η / 4`.  This is the previous leaf carried through the monotonicity
of `Real.exp` and the factor `η > 0`. -/
theorem leaf_exp_decay_quarter (γ η : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hη : 0 < η) :
    ∀ N : ℕ, 64 ≤ N →
      Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) ≤
        Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF. The `κ` side of the comparison: because `calE γ κ N ^ (-(3 / 2))` is
`exp (-(3 / 2) * κ * (log N) ^ (3 - 2 γ))`, the hypothesis `κ ≤ η / 6` gives
`(3 / 2) * κ ≤ η / 4`, so the `κ`-th scale dominates the `η / 4` decay.  This is the only
step that uses the cap on `κ`, and it is uniform in `N`. -/
theorem leaf_calE_kappa_comparison (γ η κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hη : 0 < η) (hκ : 0 < κ) (hκ6 : κ ≤ η / 6) (N : ℕ) (hN : 64 ≤ N) :
    Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤ calE γ κ N ^ (-(3 / 2 : ℝ)) := by
  sorry

/-- LEAF. The exponential of a fractional power of the logarithm grows slower than the
identity: for `a = 3 - 2 γ` in `(0, 1)` and any positive `η` the bound
`exp (η * (log N) ^ a) ≤ N` holds eventually.  Equivalently `(log N) ^ (1 - a) ≥ η`
eventually, which is what absorbs the two absolute terms of the target. -/
theorem leaf_exp_log_pow_le (γ η : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.exp (η * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤ (N : ℝ) := by
  sorry

/-- LEAF. Bookkeeping only: if `e ≤ Y`, `1 ≤ N * Y` and `B > 0`, then
`B * (N / 2) * e + 2 ≤ (2 * B + 2) * N * Y`.  The factor `B` is paid by `B * N * Y`, the
two absolute terms by `(B + 2) * N * Y` with the surplus `B` covering the mismatch between
`N / 2` and `N`. -/
theorem leaf_arith_bookkeeping (B : ℝ) (N : ℕ) (e Y : ℝ) (hB : 0 < B) (he : e ≤ Y)
    (hNY : 1 ≤ (N : ℝ) * Y) :
    B * (N / 2 : ℕ) * e + 2 ≤ (2 * B + 2) * (N : ℝ) * Y := by
  sorry

/-- Assembly of the rescaling step from the five leaves: take `C = 2 * B + 2` and `N₀`
beyond `64` and the threshold of the growth leaf, then chain the decay comparison, the
`κ` comparison and the bookkeeping. -/
theorem leaf_decay_rescale_split (γ η B : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hη : 0 < η) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ κ : ℝ, 0 < κ → κ ≤ η / 6 →
      ∀ N : ℕ, N₀ ≤ N →
        B * (N / 2 : ℕ) * Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) + 2 ≤
          C * N * calE γ κ N ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨Ne, he⟩ := leaf_exp_log_pow_le γ (η / 4) h1 h2 (by positivity)
  refine ⟨2 * B + 2, by linarith, max 64 Ne, fun κ hκ hκ6 N hN => ?_⟩
  have hN64 : 64 ≤ N := (le_max_left _ _).trans hN
  have hNe : Ne ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  have hX : Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) ≤
      calE γ κ N ^ (-(3 / 2 : ℝ)) :=
    (leaf_exp_decay_quarter γ η h1 h2 hη N hN64).trans
      (leaf_calE_kappa_comparison γ η κ h1 h2 hη hκ hκ6 N hN64)
  have hquarter : (1 : ℝ) / Real.exp (η / 4 * Real.log (N : ℝ) ^ (3 - 2 * γ))
      = Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hinv : (1 : ℝ) / (N : ℝ) ≤
      Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    rw [← hquarter]
    exact one_div_le_one_div_of_le (Real.exp_pos _) (he N hNe)
  have hNY : 1 ≤ (N : ℝ) * calE γ κ N ^ (-(3 / 2 : ℝ)) := by
    have hlin : (1 : ℝ) ≤
        (N : ℝ) * Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
      have hmul := mul_le_mul_of_nonneg_left hinv (le_of_lt hNpos)
      rwa [mul_one_div, div_self (ne_of_gt hNpos)] at hmul
    have hstep := mul_le_mul_of_nonneg_left
      (leaf_calE_kappa_comparison γ η κ h1 h2 hη hκ hκ6 N hN64) (le_of_lt hNpos)
    linarith
  exact leaf_arith_bookkeeping B N _ _ hB hX hNY

end LeanLab.ExceptionalSet.Decomp446c
