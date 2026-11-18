/-
FALSIFY unit ExceptionalSet/SPLIT_lemma9, burst 2026-11-17, session 52.

The LEAF `leaf_height_domination` of `LeanLab.ExceptionalSet.SPLIT_lemma9` is FALSE.
With `F γ N = exp (log N ^ γ)` and `calE γ κ N = exp (κ * log N ^ (3 - 2γ))`, the left
side `2 * F ^ δ + 2` has exponent `δ * log N ^ γ` and the right side `calE ^ (2/3)` has
exponent `(2/3) * κ * log N ^ (3 - 2γ)`.  For `γ > 1` we have `γ > 3 - 2γ`, so the left
exponent wins for all large `N`, whatever `δ > 0` and `κ` are.

This file proves the eventual strict reverse inequality, which is stronger than the
plain negation already recorded as `Decomp450f.not_height_domination`, and then the
negation of the leaf statement for every admissible tuple.  This is an audit of a formal
helper statement of the lab, not of the paper: Brüdern and Perelli 1998, p. 368 to 370,
do not use this size comparison.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma9

namespace LeanLab.ExceptionalSet.U1539

open Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- Standard real analysis, the growth comparison behind the falsity of
`leaf_height_domination`: for `γ > 1`, `δ > 0` and any real `κ`, eventually
`calE γ κ N ^ (2/3) < 2 * F γ N ^ δ + 2`.  The exponent `δ * log N ^ γ` of `F ^ δ`
dominates the exponent `(2/3) * κ * log N ^ (3 - 2γ)` of `calE ^ (2/3)` because
`log N ^ (3γ - 3)` tends to infinity. -/
theorem height_domination_eventually_reversed (γ : ℝ) (hγ₁ : 1 < γ)
    (δ κ : ℝ) (hδ : 0 < δ) :
    ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → calE γ κ N ^ (2 / 3 : ℝ) < 2 * F γ N ^ δ + 2 := by
  have ht : Tendsto (fun N : ℕ => δ * Real.log (N : ℝ) ^ (3 * γ - 3)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < 3 * γ - 3)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (κ * (2 / 3)))
  refine ⟨max 2 N₀, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hrate := hN₀ N ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have he : (3 - 2 * γ) + (3 * γ - 3) = γ := by ring
  have hexponent : (κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) * (2 / 3) ≤
      Real.log (N : ℝ) ^ γ * δ := by
    calc (κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) * (2 / 3)
        = Real.log (N : ℝ) ^ (3 - 2 * γ) * (κ * (2 / 3)) := by ring
      _ ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) * (δ * Real.log (N : ℝ) ^ (3 * γ - 3)) :=
        mul_le_mul_of_nonneg_left hrate (Real.rpow_nonneg hlog.le _)
      _ = Real.log (N : ℝ) ^ γ * δ := by
        rw [mul_left_comm _ δ, ← Real.rpow_add hlog, he]
        ring
  have hreverse : calE γ κ N ^ (2 / 3 : ℝ) ≤ F γ N ^ δ := by
    rw [calE, F, ← Real.exp_mul, ← Real.exp_mul]
    exact Real.exp_le_exp.mpr hexponent
  have hpos : 0 < F γ N ^ δ := Real.rpow_pos_of_pos (Real.exp_pos _) δ
  linarith

/-- FALSE verdict for the LEAF `leaf_height_domination` of `SPLIT_lemma9`: for every
admissible tuple `1 < γ < 3/2`, `δ > 0`, `κ > 0` the conclusion of the leaf, copied here
character for character, fails.  The witness is any `N` beyond both the claimed threshold
and the threshold of `height_domination_eventually_reversed`. -/
theorem leaf_height_domination_false (γ : ℝ) (hγ₁ : 1 < γ) (_hγ₂ : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (_hκ : 0 < κ) :
    ¬ (∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 2 * F γ N ^ δ + 2 ≤ calE γ κ N ^ (2 / 3 : ℝ)) := by
  rintro ⟨N₁, hN₁⟩
  obtain ⟨N₂, hN₂⟩ := height_domination_eventually_reversed γ hγ₁ δ κ hδ
  have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
  have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
  linarith

/-- The leaf as a closed proposition, all binders included, is false: the tuple
`γ = 5/4`, `δ = 1`, `κ = 1` is admissible and the conclusion fails there. -/
theorem leaf_height_domination_statement_false :
    ¬ (∀ (γ : ℝ), 1 < γ → γ < 3 / 2 → ∀ (δ κ : ℝ), 0 < δ → 0 < κ →
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 2 * F γ N ^ δ + 2 ≤ calE γ κ N ^ (2 / 3 : ℝ)) := by
  intro h
  exact leaf_height_domination_false (5 / 4) (by norm_num) (by norm_num) 1 1 one_pos one_pos
    (h (5 / 4) (by norm_num) (by norm_num) 1 1 one_pos one_pos)

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.height_domination_eventually_reversed
#print axioms LeanLab.ExceptionalSet.U1539.leaf_height_domination_false
#print axioms LeanLab.ExceptionalSet.U1539.leaf_height_domination_statement_false
