import LeanLab.Zhan1991.Decomp110
import LeanLab.Zhan1991.SPLIT_theorem3_1122
import LeanLab.Zhan1991.SingConv
import LeanLab.Zhan1991.SPLIT_theorem2_1122
import LeanLab.Zhan1991.SPLIT_major_1122
import LeanLab.Zhan1991.SingBounded1122
import LeanLab.Zhan1991.HighFree1122
import LeanLab.Zhan1991.LowRange1122
import LeanLab.Zhan1991.LargeRangeVinogradov1122
import LeanLab.Zhan1991.MajorArcSep1122
import LeanLab.Zhan1991.SingSeries1122
import LeanLab.Zhan1991.FullPeriod1122
import LeanLab.Zhan1991.RamanujanSum1122

/-!
P0068 Zhan 1991, Theorem 1, integration of burst-20261122, session S80.
The conditional form of Theorem 1 with its named inputs as explicit hypotheses, for a
Palomar entry: Theorem 2 of page 260, Theorem 3 of page 260 or its page 269 split, and the
major arc evaluation of page 271.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section

/-- Page 271, the major arc display after (3.21), the exact statement of `major_evaluation110`
as a Prop: `∫_{E₁} = 3 𝔖(N) U² L⁻³ + O(U² L⁻⁴)` once the cutoff exponent `d` is large. The
paper attributes it to the standard method of Pan and Pan, reference 2. -/
def MajorEval110 : Prop :=
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
    ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
        - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
            Real.log N ^ (-3 : ℝ)|
        ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
            Real.log N ^ (-4 : ℝ)

/-- The cited leaf `major_evaluation110` is exactly `MajorEval110`. -/
theorem majorEval110_of_leaf : MajorEval110 := major_evaluation110

/-- Theorem 1, pages 269 to 271, CONDITIONAL ON exactly three named inputs: Theorem 2 and
Theorem 3 of page 260 and the major arc evaluation of page 271. PROVED from them. -/
theorem theorem1_of_inputs (h2 : Theorem2) (h3 : Theorem3) (hM : MajorEval110) :
    Theorem1 := by
  obtain ⟨d₀, hd₀, hmajor⟩ := hM
  obtain ⟨d, c, hd, hc, Km, Nm, hminor⟩ := minor_reduction_from_paper226 h2 h3 d₀ hd₀
  obtain ⟨KM, NM, hM'⟩ := hmajor d hd c hc
  refine ⟨c, hc, Km + KM, max Nm NM, ?_⟩
  intro N hN hlarge
  have hm := hminor N hN ((le_max_left _ _).trans hlarge)
  have hMN := hM' N hN ((le_max_right _ _).trans hlarge)
  calc
    _ ≤ |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
          - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d| +
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hm hMN
    _ = _ := by ring

/-- Theorem 1 CONDITIONAL ON Theorem 2, the major arc evaluation, Lemma 6 of reference 2
and display (3.19) of page 269. PROVED from them through `theorem3_of_split`. -/
theorem theorem1_of_split_inputs (h2 : Theorem2) (h6 : PanPanLemma6) (h319 : Display319)
    (hM : MajorEval110) : Theorem1 :=
  theorem1_of_inputs h2 (theorem3_of_split h6 h319) hM

/-- Theorem 1 wired through the current LEAFs: Theorem 2 as cited, Theorem 3 through its
page 269 split, the major arc evaluation as cited. Shows `sorryAx` until the LEAFs close. -/
theorem theorem1_integrate1122c : Theorem1 :=
  theorem1_of_inputs zhan_theorem2_226 zhan_theorem3_split majorEval110_of_leaf

/-- The first assertion of Theorem 1, solvability of (1.1), CONDITIONAL ON the same three
named inputs; `𝔖(N) > 1/2` is `singGtHalf` of SingConv.lean, PROVED, not an input. -/
theorem solvable_of_inputs (h2 : Theorem2) (h3 : Theorem3) (hM : MajorEval110) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      Solvable N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) :=
  solvable_of_theorem1 (theorem1_of_inputs h2 h3 hM) singGtHalf

/-- Theorem 1 wired through all three page splits of burst-20261122: Theorem 2 through
SPLIT_theorem2_1122, Theorem 3 through SPLIT_theorem3_1122, the major arc evaluation through
SPLIT_major_1122. Shows `sorryAx` until their LEAFs close. -/
theorem theorem1_all_splits : Theorem1 :=
  theorem1_of_inputs theorem2_from_leaves zhan_theorem3_split major_evaluation_split

/-- Theorem 1 CONDITIONAL ON Theorem 2, Theorem 3 and the four standard major arc steps 2 to 5
of SPLIT_major_1122. PROVED from them. -/
theorem theorem1_of_major_steps (h2 : Theorem2) (h3 : Theorem3) (hA : MajorAssembly)
    (hI : SingIntEval) (hT : SingTruncEval) (hB : SingBounded) : Theorem1 :=
  theorem1_of_inputs h2 h3 (majorEval_of_steps hA hI hT hB)

/-- Theorem 3 through the deepest current split: Lemma 6 of reference 2, the low range of (3.19)
from (2.3), the high range from its zero free part PROVED from Lemma 5 and its density part from
(2.4). Shows `sorryAx` through the remaining LEAFs. -/
theorem theorem3_deep_split : Theorem3 := by
  obtain ⟨c0, hc0, hfree⟩ := highFree_of_lemma5_proof lemma5_cited
  exact theorem3_of_split panpan_lemma6_cited
    (display319_of_ranges (display319_low_of_23 lemma4_eq23_cited lemma5_cited)
      (display319_high_of_parts c0 hfree (highDensity_of_24 lemma4_eq24_cited c0 hc0)))

/-- Theorem 1 through the deepest current splits, with `singBounded_proof` and
`highFree_of_lemma5_proof` PROVED in place of their LEAFs. -/
theorem theorem1_deep_split : Theorem1 :=
  theorem1_of_inputs theorem2_from_leaves theorem3_deep_split major_evaluation_split_p2

/-- Theorem 1 CONDITIONAL ON Theorem 2, the four cited inputs of the page 269 proof of
Theorem 3, and the major arc evaluation. PROVED. -/
theorem theorem1_of_thm3_cited (h2 : Theorem2) (h6 : PanPanLemma6) (h23 : Lemma4Eq23)
    (h24 : Lemma4Eq24) (h5 : Lemma5NoExc) (hM : MajorEval110) : Theorem1 :=
  theorem1_of_inputs h2 (theorem3_of_cited h6 h23 h24 h5) hM

/-- Theorem 2 through its split with the large range PROVED from PNTPort's Vinogradov bound. -/
theorem theorem2_deep : Theorem2 :=
  theorem2_of_ranges
    (smallRange_of_wellKnown_eq31 wellKnown_leaf
      (eq31_of_eq38_leaf (eq38_of_eq311_eq312_leaf eq311_leaf eq312_leaf)))
    middle_reduction_leaf largeRange_of_vinogradov

/-- Theorem 1 through the deepest current splits: Theorem 2 with the large range proved,
Theorem 3 through its four cited inputs only, the major arcs with step 5 proved. -/
theorem theorem1_deepest : Theorem1 :=
  theorem1_of_inputs theorem2_deep zhan_theorem3_cited_only
    (majorEval_of_steps (majorAssembly_of_approx majorArcApprox_cited) singIntEval_split_p6
      singTruncEval_split singBounded_proof)

end

end LeanLab.Zhan1991
