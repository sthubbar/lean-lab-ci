/-
Split of the sealed statement `lemma9` of `LeanLab.ExceptionalSet.State1539`.

The split statement `lemma9_split` below has the same type, `Lemma9`, and is proved from
the LEAF theorems in this file with no `sorry` of its own.  The leaves are the two steps
of the large-value argument recorded for this statement in the folder's PROGRESS.md
(a smoothed parity cutoff and a truncated Fourier expansion, which together place a large
value of `Phie` near a half-integer) and the elementary size comparisons that turn that
placement into a bound for the integer `h`.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### The large-value step -/

/-- LEAF 1 of the split of `lemma9`: the large-value step itself, without the size bound
on the integer `h`.  For `1 < γ < 3/2` there is `δ₀ > 0` such that for every `0 < δ < δ₀`
there is `κ > 0` so that every `α` with `|α| ≤ F γ N ^ δ` and `‖Phie γ N α‖ > N ℰ ^ (-1/3)`
lies within `F γ N ^ (δ - 1)` of a half-integer `h/2`.  This is the parity-cutoff and
truncated-Fourier-expansion part of the argument; it drops the bound `|h| ≤ ℰ ^ (2/3)`,
which LEAF 2 and LEAF 3 supply separately. -/
theorem leaf_gap_core :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ → N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖Phie γ N α‖ →
        ∃ h : ℤ, |α - h / 2| ≤ F γ N ^ (δ - 1) := by
  sorry

/-! ### The size of the integer `h` -/

/-- LEAF 2 of the split of `lemma9`: the size comparison.  For `1 < γ < 3/2` and any
`δ, κ > 0` the main term `2 * F γ N ^ δ + 2` is eventually dominated by `ℰ ^ (2/3)`,
because the exponent `γ` of `log N` in `F` exceeds the exponent `3 - 2γ` in `ℰ` as soon
as `γ > 1`.  This is the step that lets LEAF 3's gap bound be upgraded to a bound on `h`. -/
theorem leaf_height_domination (γ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 2 * F γ N ^ δ + 2 ≤ calE γ κ N ^ (2 / 3 : ℝ) := by
  sorry

/-- LEAF 3 of the split of `lemma9`: the gap bound is at most one.  For `0 < δ ≤ 1` and
`F γ N ≥ 1` we have `F γ N ^ (δ - 1) ≤ 1`, so `|α - h/2| ≤ F γ N ^ (δ - 1) ≤ 1`, and the
triangle step `|h| ≤ 2|α| + 2|α - h/2|` closes against LEAF 2's domination. -/
theorem leaf_gap_unit (γ : ℝ) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (N : ℕ) (hN : 3 ≤ N) : F γ N ^ (δ - 1) ≤ 1 := by
  sorry

/-! ### Assembly -/

/-- `lemma9` from the three leaves of this file. -/
theorem lemma9_split : Lemma9 := by
  intro γ hγ₁ hγ₂
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := leaf_gap_core γ hγ₁ hγ₂
  refine ⟨min δ₀ 1, lt_min hδ₀pos one_pos, ?_⟩
  intro δ hδpos hδlt
  have hδδ₀ : δ < δ₀ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδ₁ : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδlt (min_le_right _ _))
  obtain ⟨κ, hκpos, N₀, hN₀⟩ := hδ₀ δ hδpos hδδ₀
  obtain ⟨N₁, hN₁⟩ := leaf_height_domination γ hγ₁ hγ₂ δ κ hδpos hκpos
  refine ⟨κ, hκpos, max N₀ (max N₁ 3), ?_⟩
  intro N hN α hα hlarge
  have hN₀' : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨h, hh⟩ := hN₀ N hN₀' α hα hlarge
  have hdom : 2 * F γ N ^ δ + 2 ≤ calE γ κ N ^ (2 / 3 : ℝ) := hN₁ N hN₁'
  have hunit : F γ N ^ (δ - 1) ≤ 1 := leaf_gap_unit γ δ hδpos hδ₁ N hN3
  have hcast : ((|h| : ℤ) : ℝ) = |(h : ℝ)| := Int.cast_abs
  have hstep : ((|h| : ℤ) : ℝ) ≤ 2 * |α| + 2 * |α - (h : ℝ) / 2| := by
    rw [hcast]
    have htwo : (h : ℝ) = 2 * α + -(2 * (α - (h : ℝ) / 2)) := by ring
    calc |(h : ℝ)| = |2 * α + -(2 * (α - (h : ℝ) / 2))| := congrArg abs htwo
      _ ≤ |2 * α| + |-(2 * (α - (h : ℝ) / 2))| := abs_add_le _ _
      _ = 2 * |α| + 2 * |α - (h : ℝ) / 2| := by
            rw [abs_neg, abs_mul, abs_mul]
            norm_num
  have hβ : 2 * |α - (h : ℝ) / 2| ≤ 2 * F γ N ^ (δ - 1) := by linarith
  have hunit₂ : 2 * F γ N ^ (δ - 1) ≤ 2 := by linarith
  have hα₂ : 2 * |α| ≤ 2 * F γ N ^ δ := by linarith
  have hchain : ((|h| : ℤ) : ℝ) ≤ calE γ κ N ^ (2 / 3 : ℝ) := by
    calc ((|h| : ℤ) : ℝ) ≤ 2 * |α| + 2 * |α - (h : ℝ) / 2| := hstep
      _ ≤ 2 * F γ N ^ δ + 2 * F γ N ^ (δ - 1) := by linarith
      _ ≤ 2 * F γ N ^ δ + 2 := by linarith
      _ ≤ calE γ κ N ^ (2 / 3 : ℝ) := hdom
  refine ⟨h, ?_, hh⟩
  rw [← hcast]
  exact hchain

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.lemma9_split
