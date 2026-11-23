import LeanLab.ExceptionalSet.DQ5Decisions
import LeanLab.ExceptionalSet.Decomp1539a

/-!
Burst burst-20261122 feed1122, session S89. Wiring of `U1539.leaf_shift_minor_dq5` of
`DQ5Decisions.lean`, P0082 Brüdern and Perelli 1998 page 370 last paragraph, Theorem 2 of
page 354 on the shifted window.

No new sorry. The statement is derived verbatim from two existing pieces:
* `DQLemma9.shift_minor_of_theorem2`, the same statement with `PhiDQ5` unfolded, proved from
  `Theorem2` with no open step of its own;
* `U1539.theorem2_of_all_leaves`, Theorem 2 from `Lemma10`, the only open input being the
  sealed CITED leaf `U1539.lemma10`, Karacuba 1973 Theorem 1, pages 370 to 371.
So `leaf_shift_minor_dq5_split` is CONDITIONAL ON the cited Karacuba bound alone; see the
`#print axioms` output, whose `sorryAx` comes from `lemma10` and from nothing in this file.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.U1539

open Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- `leaf_shift_minor_dq5` given `Theorem2`, by unfolding `PhiDQ5`. Clean axioms. -/
theorem leaf_shift_minor_dq5_of_theorem2 (hT : Theorem2) :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ δ : ℝ, 0 < δ → δ < γ - 1 →
      ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ β : ℝ, F γ N ^ (δ - 1) < |β| → |β| ≤ 2 * F γ N ^ δ + 2 →
          ‖PhiDQ5 γ N β‖ ≤ N * calE γ κ N ^ (-(1 : ℝ)) :=
  DQLemma9.shift_minor_of_theorem2 hT

/-- `leaf_shift_minor_dq5`, statement verbatim, from Theorem 2 conditional on the cited
Lemma 10. No new sorry; rests on `U1539.lemma10`. -/
theorem leaf_shift_minor_dq5_split :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ δ : ℝ, 0 < δ → δ < γ - 1 →
      ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ β : ℝ, F γ N ^ (δ - 1) < |β| → |β| ≤ 2 * F γ N ^ δ + 2 →
          ‖PhiDQ5 γ N β‖ ≤ N * calE γ κ N ^ (-(1 : ℝ)) :=
  leaf_shift_minor_dq5_of_theorem2 (theorem2_of_all_leaves lemma10)

/-- The split matches the parent statement exactly. -/
example : type_of% @leaf_shift_minor_dq5_split = type_of% @leaf_shift_minor_dq5 := rfl

#print axioms leaf_shift_minor_dq5_of_theorem2
#print axioms leaf_shift_minor_dq5_split

end LeanLab.ExceptionalSet.U1539
