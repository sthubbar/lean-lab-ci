import Mathlib
import LeanLab.Pintz2021.DecompJ579
import LeanLab.Pintz2021.DecompJ281

/-!
# Feed 1122: `DecompJ579.leaf_main_term_bound` from the cited display 2.21

Session burst-20261122-S105. AI-written Lean code, Claude. Binary Goldbach is OPEN.

`DecompJ579.leaf_main_term_bound` is display 2.21 of P0054 page 188 Theorem 1, the same estimate
as Pin1 arXiv:1804.05561v1 display 10.25. The lab already cites that theorem as
`DecompJ281.leaf_221`, which gives display 2.21 for one convergent series `Sg'` at the chosen
level `P`, together with `1 ≤ P`, finiteness and display 2.22.

This file proves that `leaf_main_term_bound`, statement unchanged, follows from the statement
of `leaf_221`, passed as a hypothesis so the result has clean axioms:
* `ε0` is cut to `min ε0 (1/5)`, which only shrinks the range of `ε`;
* every other series convergent at positive frequencies has the same limits, so its main term
  at a positive frequency equals the one of `leaf_221`, `DecompJ579.mainTermPrime_eq_of_converges`.

So the open goal `leaf_main_term_bound` holds no new mathematics beyond the cited `leaf_221`:
CONDITIONAL ON `DecompJ281.leaf_221`. No new LEAF is introduced.
-/

open Filter Topology
open LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DifferenceTask53
open LeanLab.Pintz2021.DecompJ281

namespace LeanLab.Pintz2021.Feed1122DecompJ579Split

noncomputable section

/-- The statement of `DecompJ281.leaf_221`, P0054 page 188 Theorem 1 displays 2.21 and 2.22,
copied verbatim as a proposition so that it can be a hypothesis. -/
def Leaf221Statement : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c C A H0 : ℝ, 0 < c ∧ 0 ≤ A ∧ ∀ H : ℝ, H0 ≤ H → ∃ X0 : ℝ, ∀ X P0 : ℝ,
      Thm1Hyp ε A X0 X P0 →
      ∃ P : ℝ, 1 ≤ P ∧ P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          (∀ m : ℕ, (m : ℝ) ≤ X →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε))) ∧
          ∀ m : ℕ, ∀ U : ℝ, X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U → U ≤ Real.sqrt X →
            ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
              mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
              C * (Sing m * X * Real.log U / Real.sqrt U)

/-- The proposition above is the type of the cited leaf, checked by the elaborator; an `example`
adds no declaration, so the cited placeholder never enters this file. -/
example : Leaf221Statement := DecompJ281.leaf_221

/-- `DecompJ579.leaf_main_term_bound`, identical statement, CONDITIONAL ON the statement of the
cited `DecompJ281.leaf_221`, P0054 page 188 Theorem 1 display 2.21. -/
theorem leaf_main_term_bound_of_leaf221 (h221 : Leaf221Statement) :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ 1 / 5 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c C A H0 : ℝ, 0 < c ∧ 0 ≤ A ∧ ∀ H : ℝ, H0 ≤ H → ∃ X0 : ℝ,
      ∀ X P0 : ℝ, Thm1Hyp ε A X0 X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
      ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
        Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ X →
        ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
          C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε)) := by
  obtain ⟨ε0, hε0, h⟩ := h221
  refine ⟨min ε0 (1 / 5), lt_min hε0 (by norm_num), min_le_right _ _, ?_⟩
  intro ε hε hεlt
  obtain ⟨c, C, A, H0, hc, hA, hH⟩ := h ε hε (lt_of_lt_of_le hεlt (min_le_left _ _))
  refine ⟨c, C, A, H0, hc, hA, ?_⟩
  intro H hH0
  obtain ⟨X0, hX⟩ := hH H hH0
  refine ⟨X0, ?_⟩
  intro X P0 hHyp
  obtain ⟨P, -, hP1, hP2, -, Sg, hSg, hB, -⟩ := hX X P0 hHyp
  refine ⟨P, hP1, hP2, ?_⟩
  intro Sg'' hSg'' m hm hmX
  have heq : mainTermPrime (excSet H (Real.sqrt X) P X) Sg'' ε X m =
      mainTermPrime (excSet H (Real.sqrt X) P X) Sg ε X m :=
    LeanLab.Pintz2021.DecompJ579.mainTermPrime_eq_of_converges
      (fun z hz w hw => hSg'' z hz w hw m hm) (fun z hz w hw => hSg z hz w hw m hm)
  rw [heq]
  exact hB m hmX

end

end LeanLab.Pintz2021.Feed1122DecompJ579Split
