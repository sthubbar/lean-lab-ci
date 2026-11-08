/-
Split of `leaf_exp_sum_bound` in ExceptionalSet/SPLIT_lemma4.lean into smaller leaves.

The statement being split, verbatim after its name:

: ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C → C < γ - 1 → ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ, F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ F γ N ^ C → ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ))

`leaf_exp_sum_bound_split` below proves it from the leaves, with no `sorry` of its own and
without using the target theorem.  The cut is by which part of the frequency range the
frequency falls in, in the order the assembly uses them:

1. `leaf_exp_sum_near_edge` - the estimate in the bottom part of the range,
   `F(N)^{-1/2} < |α| < F(N)^{-1/4}`, where the frequency is only just above the lower edge
   that the target allows.
2. `leaf_exp_sum_bulk` - the estimate on the rest of the range, `F(N)^{-1/4} ≤ |α| ≤ 1`,
   where the frequency is a genuine power of `F(N)` away from that edge.
   Both leaves repeat the hypotheses of the target unchanged and differ from it only by the
   extra restriction of `|α|` to one part of the range, so each is strictly weaker than the
   target and neither implies the other.
3. `leaf_decay_merge` - the comparison that lets a single pair `(κ, B)` serve both parts: a
   smaller decay rate and a larger constant majorise each part's bound, because the
   exponential factor `exp(-κ (log N)^{3-2γ})` is at most `1` and increasing as `κ` decreases.

The assembly splits on `F(N)^{-1/4} ≤ |α|` and takes `min κ` and `max B`; the exponent
`(log N)^{3-2γ}` is nonnegative for `N ≥ 1`, which is what makes step 3 apply there.  Both
parts of the range are nonempty once `N` is large, since `F(N)^{-1/2} < F(N)^{-1/4} < 1`.

AI wrote the Lean code.  The leaves are open; the assembly is proved.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma4

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. The estimate in the bottom part of the frequency range, `F(N)^{-1/2} < |α| <
F(N)^{-1/4}`: the target with the extra hypothesis `|α| < F(N)^{-1/4}`, hence strictly
weaker.  This is the part in which the frequency is only just above the lower edge
`F(N)^{-1/2}` that the target fixes, and every hypothesis of the target is repeated
unchanged.  The restriction is nonempty at large `N`, where `F(N)^{-1/2} < F(N)^{-1/4}`. -/
theorem leaf_exp_sum_near_edge :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C → C < γ - 1 →
      ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
        F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → |α| < F γ N ^ (-(1 / 4 : ℝ)) →
        ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ F γ N ^ C →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
          B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF. The estimate on the rest of the frequency range, `F(N)^{-1/4} ≤ |α| ≤ 1`: the
target with the extra hypothesis `F(N)^{-1/4} ≤ |α|`, hence strictly weaker.  Together with
`leaf_exp_sum_near_edge` this covers every `α` of the target, and the constants are allowed to
differ between the two parts, which is what makes each part a sub-case rather than a repeat of
the whole.  The restriction is nonempty at large `N`, where `F(N)^{-1/4} < 1`. -/
theorem leaf_exp_sum_bulk :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C → C < γ - 1 →
      ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
        F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → F γ N ^ (-(1 / 4 : ℝ)) ≤ |α| →
        ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ F γ N ^ C →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
          B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF. The comparison that merges the two parts into one pair of constants: for `0 < κ ≤ κ'`,
`0 < B ≤ B'` and `0 ≤ X`, the bound with the smaller decay rate and the larger constant
dominates the bound with the larger decay rate and the smaller constant, the factor
`exp (-κ' X) ≤ exp (-κ X)` coming from `κ X ≤ κ' X` and `N ≥ 0` from the cast of `ℕ`. -/
theorem leaf_decay_merge (κ κ' B B' X : ℝ) (N : ℕ)
    (hκ : 0 < κ) (hκ' : κ ≤ κ') (hB : 0 < B) (hB' : B ≤ B') (hX : 0 ≤ X) :
    B * N * Real.exp (-κ' * X) ≤ B' * N * Real.exp (-κ * X) := by
  sorry

/-! ### Assembly -/

/-- `leaf_exp_sum_bound`: the exponential sum over `N/2 < n ≤ N` at the frequency `hα` is
`O(N exp(-κ (log N)^{3-2γ}))` for `F(N)^{-1/2} < |α| ≤ 1` and `h ≤ F(N)^C`.  Proved from the
leaves above, with no `sorry` here and without using the target theorem: the two frequency
regimes are exhaustive by `le_or_gt`, and `leaf_decay_merge` carries each of them to the
common pair `(min κ, max B)`. -/
theorem leaf_exp_sum_bound_split :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C → C < γ - 1 → ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ, F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ F γ N ^ C → ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  intro γ hγ1 hγ2 C hC hCγ
  obtain ⟨κ₁, B₁, hκ₁, hB₁, hnear⟩ := leaf_exp_sum_near_edge γ hγ1 hγ2 C hC hCγ
  obtain ⟨κ₂, B₂, hκ₂, hB₂, hbulk⟩ := leaf_exp_sum_bulk γ hγ1 hγ2 C hC hCγ
  refine ⟨min κ₁ κ₂, max B₁ B₂, lt_min hκ₁ hκ₂, lt_of_lt_of_le hB₁ (le_max_left _ _), ?_⟩
  intro N hN α hlow hhigh h hh1 hhC
  have hX : (0 : ℝ) ≤ Real.log N ^ (3 - 2 * γ) := by
    refine Real.rpow_nonneg ?_ _
    exact Real.log_nonneg (by exact_mod_cast hN)
  rcases le_or_gt (F γ N ^ (-(1 / 4 : ℝ))) |α| with hblk | htop
  · refine le_trans (hbulk N hN α hlow hhigh hblk h hh1 hhC) ?_
    exact leaf_decay_merge (min κ₁ κ₂) κ₂ B₂ (max B₁ B₂)
      (Real.log N ^ (3 - 2 * γ)) N (lt_min hκ₁ hκ₂) (min_le_right _ _) hB₂
      (le_max_right _ _) hX
  · refine le_trans (hnear N hN α hlow hhigh htop h hh1 hhC) ?_
    exact leaf_decay_merge (min κ₁ κ₂) κ₁ B₁ (max B₁ B₂)
      (Real.log N ^ (3 - 2 * γ)) N (lt_min hκ₁ hκ₂) (min_le_left _ _) hB₁
      (le_max_left _ _) hX

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.leaf_exp_sum_bound_split
