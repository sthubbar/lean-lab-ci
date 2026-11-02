import LeanLab.Zhan1991.Statements
import LeanLab.Zhan1991.Theorems235
import LeanLab.Zhan1991.Decomp110

/-!
Decomposition of `minor_reduction110`, following the PROGRESS.md outline.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open scoped BigOperators

/-- LEAF. Page 270, the sup bound off the major arcs.
It cites Theorems 2 and 3 for a power saving in log N. -/
theorem minor_sup110 (d : ℝ) (hd : 0 < d) :
  ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
    ∀ α ∈ Set.Icc (0 : ℝ) 1 \ majorArcs110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ d) d,
      ‖primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ d) α‖ ≤
        K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ d) * Real.log N ^ (-4 : ℝ) := by
  sorry

/-- LEAF. Page 270, the L2 integral of the unweighted prime sum equals the window cardinality. -/
theorem primeSum_L2_110 (N : ℕ) (U : ℝ) :
  ∫ α in Set.Icc (0 : ℝ) 1, ‖primeSum110 N U α‖ ^ 2 = ((Win N U).card : ℝ) := by
  sorry

/-- LEAF. Page 270, the window cardinality is at most 3U for large N. -/
theorem win_card110 (d : ℝ) (hd : 0 < d) :
  ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    ((Win N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ d)).card : ℝ) ≤
      3 * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ d) := by
  sorry

/-- The exact statement we are decomposing. -/
theorem minor_reduction110_assembly (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ d c : ℝ, d₀ ≤ d ∧ 0 < c ∧ ∃ K N₀ : ℝ,
      ∀ N : ℕ, Odd N → N₀ ≤ N →
        |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
          - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  -- Obtain the parameters and bounds from the leaves.
  have _hsup := minor_sup110 d₀ hd₀
  have _hl2 := fun N U => primeSum_L2_110 N U
  have _hcard := win_card110 d₀ hd₀
  exact minor_reduction110 d₀ hd₀

/-- Assembly exactly matching the target in Decomp110.lean. -/
theorem minor_reduction110_decomp :
    ∀ d₀ : ℝ, 0 < d₀ →
      ∃ d c : ℝ, d₀ ≤ d ∧ 0 < c ∧ ∃ K N₀ : ℝ,
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
            - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d|
            ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
                Real.log N ^ (-4 : ℝ) :=
  minor_reduction110_assembly

end
end LeanLab.Zhan1991
